import Ripple.Core.PowerClosure
import Ripple.Core.MaximalPIVP
import Ripple.Core.ShiftedClockCompilation
import Ripple.Core.ProductClockCompilation
import Ripple.LPP.Derandomization
import Ripple.LPP.Stages
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# BAC journal remarks

Chen and Huang, Bounded Analog Complexity, journal version (in preparation):
Lemma 6.3 (power trajectory), Example 1.1 (BFK), Remark 3.8
(shifted clock), and Remark 3.9 (product clock).

All equality and uniqueness claims for arbitrary total representatives
are restricted to their forward domains.

Remark 3.7, the general subset compiler with evolving retained
coordinates, is not implemented in this file.
-/

noncomputable section

namespace Ripple.BACJournalRemarks

open MvPolynomial Filter MeasureTheory Topology
open scoped BigOperators ENNReal

-- Retain the original finite budget within this namespace for the
-- finite-index polynomial and analytic proofs. The conservation proof
-- below fixes inference explicitly instead of increasing this budget.
set_option maxHeartbeats 800000

/-! ## B9: the full power trajectory and forward uniqueness -/

section Power

variable {d₁ d₂ : ℕ}

/-- A continuous representative of a forward input for the filter. -/
def powerInputExtension (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  x (max t 0)

theorem powerInputExtension_continuous {x : ℝ → ℝ}
    (hx : ContinuousOn x (Set.Ici 0)) :
    Continuous (powerInputExtension x) := by
  exact hx.comp_continuous (continuous_id.max continuous_const)
    (fun t => le_max_right t 0)

theorem power_lowpass_extension_eq (x : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    lowpassSq (powerInputExtension x) t = lowpassSq x t := by
  have hi :
      (∫ s in (0 : ℝ)..t, Real.exp s * powerInputExtension x s ^ 2) =
        ∫ s in (0 : ℝ)..t, Real.exp s * x s ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc 0 t := by
      simpa only [Set.uIcc_of_le ht] using hs
    simp only [powerInputExtension, max_eq_left hs'.1]
  simp only [lowpassSq, hi]

/-- The integrating-factor expression is exactly the journal convolution. -/
theorem power_lowpass_convolution (x : ℝ → ℝ) (t : ℝ) :
    lowpassSq x t = Real.exp (-t) +
      ∫ s in (0 : ℝ)..t, Real.exp (-(t - s)) * x s ^ 2 := by
  have hi :
      (∫ s in (0 : ℝ)..t, Real.exp (-(t - s)) * x s ^ 2) =
        Real.exp (-t) * ∫ s in (0 : ℝ)..t, Real.exp s * x s ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    have he : Real.exp (-(t - s)) = Real.exp (-t) * Real.exp s := by
      rw [← Real.exp_add]
      congr 1
      ring
    change Real.exp (-(t - s)) * x s ^ 2 =
      Real.exp (-t) * (Real.exp s * x s ^ 2)
    rw [he]
    ring
  rw [hi, lowpassSq]
  ring

theorem power_lowpass_positive (x : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ lowpassSq x t ∧ 0 < lowpassSq x t :=
  ⟨exp_neg_le_lowpassSq x ht, lowpassSq_pos x ht⟩

/-- Initialization of every indexed coordinate, without a convergence premise. -/
theorem powCurve_initial (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (sx : PIVP.Solution Px.toPIVP) (sy : PIVP.Solution Py.toPIVP)
    {w : ℝ → ℝ} (hw : w 0 = 1) :
    ∀ k, powCurve sx.trajectory sy.trajectory Py.output w 0 k =
      (powInit Px Py k : ℝ) := by
  intro k
  rcases k with i | j | a
  · exact congrFun sx.init_cond i
  · exact congrFun sy.init_cond j
  · cases a <;> simp [powCurve, powInit, hw]

/-- Every coordinate satisfies the actual polynomial field of powerSqCompile. -/
theorem powCurve_derivative (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (sx : PIVP.Solution Px.toPIVP) (sy : PIVP.Solution Py.toPIVP)
    {w : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hw : HasDerivAt w (sx.trajectory t Px.output ^ 2 - w t) t)
    (hwpos : 0 < w t) :
    ∀ k, HasDerivAt
      (fun s => powCurve sx.trajectory sy.trajectory Py.output w s k)
      ((powField Px Py k).eval₂ (Rat.castHom ℝ)
        (powCurve sx.trajectory sy.trajectory Py.output w t)) t := by
  let Z := powCurve sx.trajectory sy.trajectory Py.output w
  have hwne : w t ≠ 0 := hwpos.ne'
  have hx :
      (powX1RHS (d₂ := d₂) Px).eval₂ (Rat.castHom ℝ) (Z t) =
        sx.trajectory t Px.output ^ 2 - w t := by
    simp only [powX1RHS, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one, Z, powCurve]
    ring
  have hyd : HasDerivAt (fun s => sy.trajectory s Py.output)
      (Py.evalField (sy.trajectory t) Py.output) t :=
    hasDerivAt_pi.mp (sy.is_solution t ht) Py.output
  have hHy :
      (rename (fun k => (Sum.inr (Sum.inl k) : PowIndex d₁ d₂))
        (Py.field Py.output)).eval₂ (Rat.castHom ℝ) (Z t) =
          Py.evalField (sy.trajectory t) Py.output := by
    rw [eval₂_rename]
    rfl
  intro k
  change HasDerivAt (fun s => Z s k)
    ((powField Px Py k).eval₂ (Rat.castHom ℝ) (Z t)) t
  rcases k with i | j | a
  · show HasDerivAt (fun s => sx.trajectory s i)
      ((rename Sum.inl (Px.field i)).eval₂ (Rat.castHom ℝ) (Z t)) t
    rw [eval₂_rename]
    exact hasDerivAt_pi.mp (sx.is_solution t ht) i
  · show HasDerivAt (fun s => sy.trajectory s j)
      ((rename (fun k => (Sum.inr (Sum.inl k) : PowIndex d₁ d₂))
        (Py.field j)).eval₂ (Rat.castHom ℝ) (Z t)) t
    rw [eval₂_rename]
    exact hasDerivAt_pi.mp (sy.is_solution t ht) j
  · cases a with
    | x1 =>
      show HasDerivAt (fun s => w s - 1)
        ((powX1RHS Px).eval₂ (Rat.castHom ℝ) (Z t)) t
      rw [hx]
      exact hw.sub_const 1
    | u =>
      show HasDerivAt (fun s => Real.log (w s))
        (((1 - X (Sum.inr (Sum.inr PowSlot.v))) * powX1RHS Px).eval₂
          (Rat.castHom ℝ) (Z t)) t
      rw [eval₂_mul, hx]
      refine (hw.log hwne).congr_deriv ?_
      simp only [eval₂_sub, eval₂_one, eval₂_X, Z, powCurve]
      ring
    | v =>
      show HasDerivAt (fun s => 1 - 1 / w s)
        (((1 - X (Sum.inr (Sum.inr PowSlot.v))) ^ 2 * powX1RHS Px).eval₂
          (Rat.castHom ℝ) (Z t)) t
      rw [eval₂_mul, hx]
      have h := (hw.inv hwne).const_sub 1
      simp only [one_div]
      refine h.congr_deriv ?_
      simp only [eval₂_sub, eval₂_one, eval₂_X, eval₂_pow, Z, powCurve]
      ring
    | z =>
      show HasDerivAt
        (fun s => Real.exp (1 / 2 * sy.trajectory s Py.output * Real.log (w s)))
        ((C (1 / 2 : ℚ) * X (Sum.inr (Sum.inr PowSlot.z)) *
          (rename (fun k => (Sum.inr (Sum.inl k) : PowIndex d₁ d₂))
              (Py.field Py.output) * X (Sum.inr (Sum.inr PowSlot.u)) +
            X (Sum.inr (Sum.inl Py.output)) *
              (1 - X (Sum.inr (Sum.inr PowSlot.v))) * powX1RHS Px)).eval₂
                (Rat.castHom ℝ) (Z t)) t
      rw [eval₂_mul, eval₂_mul, eval₂_add, eval₂_mul, eval₂_mul,
        eval₂_mul, hHy, hx]
      have hc : (Rat.castHom ℝ) (1 / 2 : ℚ) = (1 / 2 : ℝ) := by simp
      simp only [eval₂_C, eval₂_sub, eval₂_one, eval₂_X, Z, powCurve, hc]
      have h := ((hyd.const_mul (1 / 2 : ℝ)).fun_mul (hw.log hwne)).exp
      refine h.congr_deriv ?_
      ring

/-- Full public trajectory for arbitrary supplied global upstream solutions.
No upstream boundedness, output limit, or uniqueness hypothesis is required. -/
theorem powCurve_solution (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (sx : PIVP.Solution Px.toPIVP) (sy : PIVP.Solution Py.toPIVP) :
    ∃ sol : PIVP.Solution (Px.powerSqCompile Py).toPIVP,
      ∀ t, 0 ≤ t → ∀ k : PowIndex d₁ d₂,
        sol.trajectory t (Fintype.equivFin (PowIndex d₁ d₂) k) =
          powCurve sx.trajectory sy.trajectory Py.output
            (lowpassSq (fun s => sx.trajectory s Px.output)) t k := by
  let x : ℝ → ℝ := fun t => sx.trajectory t Px.output
  have hxc : ContinuousOn x (Set.Ici 0) := by
    intro t ht
    exact (hasDerivAt_pi.mp (sx.is_solution t ht) Px.output).continuousAt.continuousWithinAt
  let w := lowpassSq (powerInputExtension x)
  let Z := powCurve sx.trajectory sy.trajectory Py.output w
  have hwzero : w 0 = 1 := lowpassSq_zero _
  have hZzero : ∀ k, Z 0 k = (powInit Px Py k : ℝ) :=
    powCurve_initial Px Py sx sy hwzero
  have hZd : ∀ t, 0 ≤ t → ∀ k, HasDerivAt (fun s => Z s k)
      ((powField Px Py k).eval₂ (Rat.castHom ℝ) (Z t)) t := by
    intro t ht
    have hw : HasDerivAt w (x t ^ 2 - w t) t := by
      simpa only [powerInputExtension, max_eq_left ht] using
        lowpassSq_hasDerivAt (powerInputExtension_continuous hxc) t
    exact powCurve_derivative Px Py sx sy ht hw (lowpassSq_pos _ ht)
  obtain ⟨sol, hsol⟩ := PolyPIVP.ofIndexed_solution
    (powField Px Py) (powInit Px Py) (Sum.inr (Sum.inr PowSlot.z)) Z hZzero hZd
  refine ⟨sol, ?_⟩
  intro t ht k
  rw [hsol]
  simp only [Equiv.symm_apply_apply]
  have hw : w t = lowpassSq x t := power_lowpass_extension_eq x ht
  change powCurve sx.trajectory sy.trajectory Py.output w t k =
    powCurve sx.trajectory sy.trajectory Py.output (lowpassSq x) t k
  rcases k with i | j | a
  · rfl
  · rfl
  · cases a <;> simp only [powCurve, hw]

/-- Forward uniqueness against every finite or infinite forward solution.
In particular, equality of arbitrary negative-time representatives is not asserted. -/
theorem powCurve_forward_unique (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (sx : PIVP.Solution Px.toPIVP) (sy : PIVP.Solution Py.toPIVP)
    (v : MaximalPIVP.ForwardSolution (Px.powerSqCompile Py))
    {t : ℝ} (ht : t ∈ MaximalPIVP.forwardInterval v.lifetime)
    (k : PowIndex d₁ d₂) :
    v.trajectory t (Fintype.equivFin (PowIndex d₁ d₂) k) =
      powCurve sx.trajectory sy.trajectory Py.output
        (lowpassSq (fun s => sx.trajectory s Px.output)) t k := by
  obtain ⟨sol, hsol⟩ := powCurve_solution Px Py sx sy
  have htglobal :
      t ∈ MaximalPIVP.forwardInterval
        (MaximalPIVP.ForwardSolution.ofGlobal sol).lifetime := by
    change t ∈ MaximalPIVP.forwardInterval ⊤
    rw [MaximalPIVP.forwardInterval_top]
    exact ht.1
  have heq := v.agree (MaximalPIVP.ForwardSolution.ofGlobal sol) ht htglobal
  change v.trajectory t = sol.trajectory t at heq
  rw [heq]
  exact hsol t ht.1 k

theorem powCurve_global_unique (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (sx : PIVP.Solution Px.toPIVP) (sy : PIVP.Solution Py.toPIVP)
    (v : PIVP.Solution (Px.powerSqCompile Py).toPIVP)
    {t : ℝ} (ht : 0 ≤ t) (k : PowIndex d₁ d₂) :
    v.trajectory t (Fintype.equivFin (PowIndex d₁ d₂) k) =
      powCurve sx.trajectory sy.trajectory Py.output
        (lowpassSq (fun s => sx.trajectory s Px.output)) t k := by
  apply powCurve_forward_unique Px Py sx sy
    (MaximalPIVP.ForwardSolution.ofGlobal v)
  change t ∈ MaximalPIVP.forwardInterval ⊤
  rw [MaximalPIVP.forwardInterval_top]
  exact ht

end Power

/-! ## B11: the BFK cyclic protocol -/

namespace BFK

open Filter MeasureTheory Set Topology MvPolynomial

/-- The predecessor in the three-state cyclic protocol. -/
def predecessor (i : Fin 3) : Fin 3 :=
  ⟨(i.val + 3 - 1) % 3, Nat.mod_lt _ (by decide)⟩

/-- The cyclic mean-field equation restricted to the mass-one plane. -/
def linearField (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => 2 * (x (predecessor i) - x i)

def decay (t : ℝ) : ℝ :=
  Real.exp (-3 * t)

def cosMode (t : ℝ) : ℝ :=
  decay t * Real.cos (Real.sqrt 3 * t)

def sinMode (t : ℝ) : ℝ :=
  decay t * Real.sin (Real.sqrt 3 * t) * (Real.sqrt 3 / 3)

/-- The journal trajectory from (1,0,0), with phases expanded. -/
def curve (t : ℝ) : Fin 3 → ℝ :=
  ![1 / 3 + (2 / 3) * cosMode t,
    1 / 3 - cosMode t / 3 + sinMode t,
    1 / 3 - cosMode t / 3 - sinMode t]

def energy (x : Fin 3 → ℝ) : ℝ :=
  ∑ i, (x i - 1 / 3) ^ 2

theorem energy_nonneg (x : Fin 3 → ℝ) : 0 ≤ energy x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

theorem decay_pos (t : ℝ) : 0 < decay t :=
  Real.exp_pos _

theorem decay_hasDerivAt (t : ℝ) :
    HasDerivAt decay (-3 * decay t) t := by
  change HasDerivAt (fun s : ℝ => Real.exp (-3 * s))
    (-3 * Real.exp (-3 * t)) t
  convert (((hasDerivAt_id t).const_mul (-3 : ℝ)).exp) using 1 <;>
    (try simp only [id_eq, id]) <;> ring

theorem cosMode_hasDerivAt (t : ℝ) :
    HasDerivAt cosMode (-3 * cosMode t - 3 * sinMode t) t := by
  convert (decay_hasDerivAt t).mul
    (((hasDerivAt_id t).const_mul (Real.sqrt 3)).cos) using 1 <;>
    dsimp [cosMode, sinMode] <;> ring

theorem sinMode_hasDerivAt (t : ℝ) :
    HasDerivAt sinMode (cosMode t - 3 * sinMode t) t := by
  have h :=
    ((decay_hasDerivAt t).mul
      (((hasDerivAt_id t).const_mul (Real.sqrt 3)).sin)).mul_const
        (Real.sqrt 3 / 3)
  refine h.congr_deriv ?_
  dsimp [cosMode, sinMode]
  linear_combination
    (decay t * Real.cos (Real.sqrt 3 * t) / 3) *
      (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))

theorem modes_sq (t : ℝ) :
    cosMode t ^ 2 + 3 * sinMode t ^ 2 = decay t ^ 2 := by
  have hsqrt : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  dsimp [cosMode, sinMode]
  calc
    (decay t * Real.cos (Real.sqrt 3 * t)) ^ 2 +
        3 * (decay t * Real.sin (Real.sqrt 3 * t) *
          (Real.sqrt 3 / 3)) ^ 2 =
        decay t ^ 2 *
          (Real.sin (Real.sqrt 3 * t) ^ 2 +
            Real.cos (Real.sqrt 3 * t) ^ 2) := by
      simp only [mul_pow, div_pow, hsqrt]
      ring
    _ = decay t ^ 2 := by
      rw [Real.sin_sq_add_cos_sq, mul_one]

theorem decay_sq (t : ℝ) :
    decay t ^ 2 = Real.exp (-6 * t) := by
  calc
    decay t ^ 2 = Real.exp ((-3 * t) + (-3 * t)) := by
      simp [decay, Real.exp_add, pow_two]
    _ = Real.exp (-6 * t) := by
      congr 1
      ring

theorem curve_zero : curve 0 = ![(1 : ℝ), 0, 0] := by
  funext i
  fin_cases i <;> norm_num [curve, cosMode, sinMode, decay]

/-- The literal phase formula in zero-based indexing. -/
theorem curve_eq_cos_phase (t : ℝ) (i : Fin 3) :
    curve t i =
      1 / 3 + (2 / 3) * Real.exp (-3 * t) *
        Real.cos (Real.sqrt 3 * t -
          2 * (i.val : ℝ) * Real.pi / 3) := by
  have hcos_two : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  have hsin_two : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  have hcos_four : Real.cos (4 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 4 * Real.pi / 3 = Real.pi + Real.pi / 3 by ring,
      Real.cos_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    ring
  have hsin_four : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
    rw [show 4 * Real.pi / 3 = Real.pi + Real.pi / 3 by ring,
      Real.sin_add, Real.sin_pi, Real.cos_pi,
      Real.sin_pi_div_three, Real.cos_pi_div_three]
    ring
  fin_cases i <;>
    norm_num [curve, cosMode, sinMode, decay, Real.cos_sub,
      hcos_two, hsin_two, hcos_four, hsin_four] <;>
    ring

theorem curve_sum (t : ℝ) : ∑ i, curve t i = 1 := by
  norm_num [curve, Fin.sum_univ_succ]
  ring

theorem curve_hasDerivAt (t : ℝ) :
    HasDerivAt curve (linearField (curve t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hc := cosMode_hasDerivAt t
  have hs := sinMode_hasDerivAt t
  fin_cases i
  · convert (hc.const_mul (2 / 3 : ℝ)).const_add (1 / 3 : ℝ)
      using 1 <;>
      norm_num [curve, linearField, predecessor] <;> ring
  · convert ((hc.div_const 3).const_sub (1 / 3 : ℝ)).add hs
      using 1 <;>
      norm_num [curve, linearField, predecessor] <;> ring
  · convert ((hc.div_const 3).const_sub (1 / 3 : ℝ)).sub hs
      using 1 <;>
      norm_num [curve, linearField, predecessor] <;> ring

@[simp] theorem curve_deriv (t : ℝ) :
    deriv curve t = linearField (curve t) :=
  (curve_hasDerivAt t).deriv

theorem curve_continuous : Continuous curve :=
  continuous_iff_continuousAt.mpr fun t =>
    (curve_hasDerivAt t).continuousAt

theorem curve_cyclic_ode (t : ℝ) :
    HasDerivAt curve
      ((cyclicProtocol 3 (by decide)).meanFieldDrift (curve t)) t := by
  have hfield :
      (cyclicProtocol 3 (by decide)).meanFieldDrift (curve t) =
        linearField (curve t) := by
    funext i
    exact cyclicDrift_eq 3 (by decide) (curve t) (curve_sum t) i
  rw [hfield]
  exact curve_hasDerivAt t

/-- A rational polynomial PIVP presenting the same mass-one dynamics. -/
def problem : PolyPIVP 3 where
  field := fun i => C 2 * (X (predecessor i) - X i)
  init := ![1, 0, 0]
  output := 0

theorem problem_eval (x : Fin 3 → ℝ) :
    problem.evalField x = linearField x := by
  funext i
  simp [problem, PolyPIVP.evalField, linearField]

def solution : PIVP.Solution problem.toPIVP where
  trajectory := curve
  init_cond := by
    funext i
    fin_cases i <;>
      norm_num [curve, cosMode, sinMode, decay,
        problem, PolyPIVP.toPIVP]
  is_solution := by
    intro t _
    change HasDerivAt curve (problem.evalField (curve t)) t
    rw [problem_eval]
    exact curve_hasDerivAt t

theorem curve_nonneg (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) :
    0 ≤ curve t i := by
  have hcrn : IsCRNImplementable 3 problem.toPIVP.field :=
    { prod := fun j x => 2 * x (predecessor j)
      degr := fun _ _ => 2
      prod_pos := by
        intro j x hx
        exact mul_nonneg (by norm_num) (hx _)
      degr_pos := by
        intro _ _ _
        norm_num
      field_eq := by
        intro x j
        change problem.evalField x j =
          2 * x (predecessor j) - 2 * x j
        rw [problem_eval]
        dsimp [linearField]
        ring }
  have hinit : ∀ j, 0 ≤ problem.toPIVP.init j := by
    intro j
    fin_cases j <;> norm_num [problem, PolyPIVP.toPIVP]
  exact pivp_solution_nonneg hcrn
    (polyPIVP_field_locally_lipschitz problem) hinit solution t ht i

theorem curve_simplex (t : ℝ) (ht : 0 ≤ t) :
    (∀ i, 0 ≤ curve t i) ∧ ∑ i, curve t i = 1 :=
  ⟨curve_nonneg t ht, curve_sum t⟩

/-- Uniqueness follows from polynomial ODE uniqueness. -/
theorem solution_unique (s : PIVP.Solution problem.toPIVP) :
    Set.EqOn s.trajectory curve (Set.Ici 0) :=
  MaximalPIVP.global_solution_unique problem s solution

/-- Conservation uses the actual reaction field on the ambient space. -/
theorem protocol_conservative {n : ℕ} (pp : Kurtz.PopProtocol n) :
    IsConservative pp.meanFieldDrift := by
  classical
  intro x
  simp only [Kurtz.PopProtocol.meanFieldDrift]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro reaction _
  rw [← Finset.sum_mul]
  have hzero : (∑ i, (reaction.netChange i : ℝ)) = 0 := by
    exact_mod_cast reaction.netChange_sum_zero
  rw [hzero, zero_mul]

theorem mass_one (x : ℝ → Fin 3 → ℝ)
    (hinit : ∑ i, x 0 i = 1)
    (hode : ∀ t, 0 ≤ t → HasDerivAt x
      ((cyclicProtocol 3 (by decide)).meanFieldDrift (x t)) t)
    (t : ℝ) (ht : 0 ≤ t) :
    ∑ i, x t i = 1 := by
  let P : PIVP 3 :=
    { field := (cyclicProtocol 3 (by decide)).meanFieldDrift
      init := x 0
      output := 0 }
  let s : PIVP.Solution P :=
    { trajectory := x
      init_cond := rfl
      is_solution := hode }
  have hconservative : IsConservative P.field := by
    change IsConservative
      ((cyclicProtocol 3 (by decide)).meanFieldDrift)
    exact protocol_conservative (cyclicProtocol 3 (by decide))
  -- Fix P before elaborating the field premise; do not infer it by
  -- reducing the concrete cyclic protocol.
  have hconstant :=
    pivp_solution_sum_const (P := P) hconservative s t ht
  change (∑ i, x t i) = ∑ i, x 0 i at hconstant
  exact hconstant.trans hinit

/-- Uniqueness for the actual protocol ODE, with no invariant premise. -/
theorem cyclic_solution_unique (x : ℝ → Fin 3 → ℝ)
    (hinit : x 0 = ![(1 : ℝ), 0, 0])
    (hode : ∀ t, 0 ≤ t → HasDerivAt x
      ((cyclicProtocol 3 (by decide)).meanFieldDrift (x t)) t) :
    Set.EqOn x curve (Set.Ici 0) := by
  have hmass_initial : ∑ i, x 0 i = 1 := by
    rw [hinit]
    norm_num [Fin.sum_univ_succ]
  have hmass : ∀ t, 0 ≤ t → ∑ i, x t i = 1 :=
    mass_one x hmass_initial hode
  let s : PIVP.Solution problem.toPIVP :=
    { trajectory := x
      init_cond := (hinit.trans curve_zero.symm).trans solution.init_cond
      is_solution := by
        intro t ht
        change HasDerivAt x (problem.evalField (x t)) t
        rw [problem_eval]
        have h := hode t ht
        have hfield :
            (cyclicProtocol 3 (by decide)).meanFieldDrift (x t) =
              linearField (x t) := by
          funext i
          exact cyclicDrift_eq 3 (by decide) (x t) (hmass t ht) i
        rw [hfield] at h
        exact h }
  exact solution_unique s

/-- The energy calculation for every supplied cyclic solution. -/
theorem energy_hasDerivAt {x : ℝ → Fin 3 → ℝ} {t : ℝ}
    (hmass : ∑ i, x t i = 1)
    (hd : HasDerivAt x
      ((cyclicProtocol 3 (by decide)).meanFieldDrift (x t)) t) :
    HasDerivAt (fun s => energy (x s)) (-6 * energy (x t)) t := by
  have hmass' : x t 0 + x t 1 + x t 2 = 1 := by
    simpa only [Fin.sum_univ_three] using hmass
  have henergy :
      HasDerivAt (fun s => energy (x s))
        (∑ i : Fin 3, 2 * (x t i - 1 / 3) *
          (cyclicProtocol 3 (by decide)).meanFieldDrift (x t) i) t := by
    simpa [energy] using
      (HasDerivAt.sum fun i (_ : i ∈ Finset.univ) =>
        ((hasDerivAt_pi.mp hd i).sub_const (1 / 3 : ℝ)).pow 2)
  apply henergy.congr_deriv
  simp_rw [cyclicDrift_eq 3 (by decide) (x t) hmass]
  simp only [energy, Fin.sum_univ_three]
  change
    2 * (x t 0 - 1 / 3) * (2 * (x t 2 - x t 0)) +
      2 * (x t 1 - 1 / 3) * (2 * (x t 0 - x t 1)) +
      2 * (x t 2 - 1 / 3) * (2 * (x t 1 - x t 2)) =
    -6 * ((x t 0 - 1 / 3) ^ 2 +
      (x t 1 - 1 / 3) ^ 2 + (x t 2 - 1 / 3) ^ 2)
  rw [show x t 2 = 1 - x t 0 - x t 1 by linarith]
  ring

/-- Exact energy decay for every mass-one forward cyclic solution. -/
theorem energy_eq (x : ℝ → Fin 3 → ℝ)
    (hmass : ∀ t, 0 ≤ t → ∑ i, x t i = 1)
    (hode : ∀ t, 0 ≤ t → HasDerivAt x
      ((cyclicProtocol 3 (by decide)).meanFieldDrift (x t)) t)
    (t : ℝ) (ht : 0 ≤ t) :
    energy (x t) = energy (x 0) * Real.exp (-6 * t) := by
  have hweighted : ∀ s, 0 ≤ s →
      HasDerivAt (fun u => Real.exp (6 * u) * energy (x u)) 0 s := by
    intro s hs
    have h := (((hasDerivAt_id s).const_mul (6 : ℝ)).exp).mul
      (energy_hasDerivAt (hmass s hs) (hode s hs))
    convert h using 1 <;> ring
  have hconstant :
      Real.exp (6 * t) * energy (x t) = energy (x 0) := by
    have hftc :
        (∫ s in (0 : ℝ)..t, (0 : ℝ)) =
          Real.exp (6 * t) * energy (x t) -
            Real.exp (6 * 0) * energy (x 0) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hweighted s
          ((show s ∈ Set.Icc 0 t by
            simpa [Set.uIcc_of_le ht] using hs).1))
        intervalIntegrable_const
    norm_num at hftc
    linarith
  have hinverse : Real.exp (-6 * t) * Real.exp (6 * t) = 1 := by
    rw [← Real.exp_add, show -6 * t + 6 * t = 0 by ring, Real.exp_zero]
  calc
    energy (x t) =
        Real.exp (-6 * t) * (Real.exp (6 * t) * energy (x t)) := by
      rw [← mul_assoc, hinverse, one_mul]
    _ = energy (x 0) * Real.exp (-6 * t) := by
      rw [hconstant]
      ring

/-- General exponential convergence on the mass-one plane. -/
theorem error_le (x : ℝ → Fin 3 → ℝ)
    (hmass : ∀ t, 0 ≤ t → ∑ i, x t i = 1)
    (hode : ∀ t, 0 ≤ t → HasDerivAt x
      ((cyclicProtocol 3 (by decide)).meanFieldDrift (x t)) t)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) :
    |x t i - 1 / 3| ≤ Real.sqrt (energy (x 0)) * decay t := by
  have hsingle : (x t i - 1 / 3) ^ 2 ≤ energy (x t) := by
    change (x t i - 1 / 3) ^ 2 ≤
      ∑ j : Fin 3, (x t j - 1 / 3) ^ 2
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (x t j - 1 / 3)) (Finset.mem_univ i)
  have hmajor :
      (Real.sqrt (energy (x 0)) * decay t) ^ 2 =
        energy (x 0) * Real.exp (-6 * t) := by
    rw [mul_pow, Real.sq_sqrt (energy_nonneg _), decay_sq]
  apply (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (decay_pos t).le)).mp
  rw [sq_abs, hmajor]
  exact hsingle.trans_eq (energy_eq x hmass hode t ht)

theorem tendsto_uniform (x : ℝ → Fin 3 → ℝ)
    (hmass : ∀ t, 0 ≤ t → ∑ i, x t i = 1)
    (hode : ∀ t, 0 ≤ t → HasDerivAt x
      ((cyclicProtocol 3 (by decide)).meanFieldDrift (x t)) t) :
    Tendsto x atTop (𝓝 (fun _ : Fin 3 => (1 / 3 : ℝ))) := by
  have hinner :
      Tendsto (fun t : ℝ => (-3 : ℝ) * t) atTop atBot :=
    tendsto_const_nhds.neg_mul_atTop
      (by norm_num : (-3 : ℝ) < 0) tendsto_id
  have hdecay : Tendsto decay atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp hinner
  have hmajor :
      Tendsto (fun t => Real.sqrt (energy (x 0)) * decay t)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hdecay.const_mul (Real.sqrt (energy (x 0)))
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_iff_dist_tendsto_zero.mpr
  have habs : Tendsto (fun t => |x t i - 1 / 3|)
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      (by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        exact error_le x hmass hode t ht i)
      hmajor
  simpa [Real.dist_eq] using habs

theorem energy_eq_of_initial_mass (x : ℝ → Fin 3 → ℝ)
    (hinit : ∑ i, x 0 i = 1)
    (hode : ∀ t, 0 ≤ t → HasDerivAt x
      ((cyclicProtocol 3 (by decide)).meanFieldDrift (x t)) t)
    (t : ℝ) (ht : 0 ≤ t) :
    energy (x t) = energy (x 0) * Real.exp (-6 * t) :=
  energy_eq x (mass_one x hinit hode) hode t ht

/-- Stability, expressed by a nonincreasing positive-definite energy. -/
theorem energy_le_initial (x : ℝ → Fin 3 → ℝ)
    (hinit : ∑ i, x 0 i = 1)
    (hode : ∀ t, 0 ≤ t → HasDerivAt x
      ((cyclicProtocol 3 (by decide)).meanFieldDrift (x t)) t)
    (t : ℝ) (ht : 0 ≤ t) :
    energy (x t) ≤ energy (x 0) := by
  rw [energy_eq_of_initial_mass x hinit hode t ht]
  have hexp : Real.exp (-6 * t) ≤ 1 := by
    calc
      Real.exp (-6 * t) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  simpa using mul_le_mul_of_nonneg_left hexp (energy_nonneg (x 0))

theorem error_le_of_initial_mass (x : ℝ → Fin 3 → ℝ)
    (hinit : ∑ i, x 0 i = 1)
    (hode : ∀ t, 0 ≤ t → HasDerivAt x
      ((cyclicProtocol 3 (by decide)).meanFieldDrift (x t)) t)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) :
    |x t i - 1 / 3| ≤ Real.sqrt (energy (x 0)) * decay t :=
  error_le x (mass_one x hinit hode) hode t ht i

/-- Attraction on the entire mass-one affine plane, hence on the simplex. -/
theorem tendsto_uniform_of_initial_mass (x : ℝ → Fin 3 → ℝ)
    (hinit : ∑ i, x 0 i = 1)
    (hode : ∀ t, 0 ≤ t → HasDerivAt x
      ((cyclicProtocol 3 (by decide)).meanFieldDrift (x t)) t) :
    Tendsto x atTop (𝓝 (fun _ : Fin 3 => (1 / 3 : ℝ))) :=
  tendsto_uniform x (mass_one x hinit hode) hode

theorem curve_energy (t : ℝ) :
    energy (curve t) = (2 / 3) * Real.exp (-6 * t) := by
  calc
    energy (curve t) =
        (2 / 3) * (cosMode t ^ 2 + 3 * sinMode t ^ 2) := by
      norm_num [energy, Fin.sum_univ_three, curve, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    _ = (2 / 3) * decay t ^ 2 := by
      rw [modes_sq]
    _ = (2 / 3) * Real.exp (-6 * t) := by
      rw [decay_sq]

theorem curve_ne_uniform (t : ℝ) :
    curve t ≠ (fun _ : Fin 3 => (1 / 3 : ℝ)) := by
  intro h
  have hp : 0 < energy (curve t) := by
    rw [curve_energy]
    positivity
  rw [h] at hp
  norm_num [energy, Fin.sum_univ_succ] at hp

theorem curve_error_le (t : ℝ) (i : Fin 3) :
    |curve t i - 1 / 3| ≤ (2 / 3) * decay t := by
  have hm := modes_sq t
  have hsquare :
      (curve t i - 1 / 3) ^ 2 ≤ ((2 / 3) * decay t) ^ 2 := by
    fin_cases i <;> norm_num [curve] <;>
      nlinarith [sq_nonneg (sinMode t),
        sq_nonneg (cosMode t + sinMode t),
        sq_nonneg (cosMode t - sinMode t)]
  apply (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (by norm_num) (decay_pos t).le)).mp
  simpa only [sq_abs] using hsquare

/-- The norm is the sup norm on Fin 3 → ℝ. -/
theorem speed_le (t : ℝ) :
    ‖deriv curve t‖ ≤ (8 / 3) * decay t := by
  rw [curve_deriv]
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (by norm_num) (decay_pos t).le)).mpr
  intro i
  have ha := curve_error_le t (predecessor i)
  have hb := curve_error_le t i
  have htriangle :=
    abs_sub_le (curve t (predecessor i)) (1 / 3 : ℝ) (curve t i)
  rw [abs_sub_comm (1 / 3 : ℝ) (curve t i)] at htriangle
  rw [Real.norm_eq_abs]
  dsimp [linearField]
  rw [abs_mul]
  norm_num
  linarith

theorem speed_continuous : Continuous (fun t => ‖deriv curve t‖) := by
  have hfield : Continuous (fun t => linearField (curve t)) := by
    apply continuous_pi
    intro i
    exact continuous_const.mul
      (((continuous_apply (predecessor i)).comp curve_continuous).sub
        ((continuous_apply i).comp curve_continuous))
  simpa only [curve_deriv] using hfield.norm

theorem speed_integrable :
    IntegrableOn (fun t => ‖deriv curve t‖) (Set.Ioi (0 : ℝ)) := by
  have hmajor :
      IntegrableOn (fun t => (8 / 3 : ℝ) * decay t)
        (Set.Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0)
      (0 : ℝ)).const_mul (8 / 3 : ℝ)
  apply hmajor.mono' speed_continuous.aestronglyMeasurable
  exact Eventually.of_forall fun t => by simpa using speed_le t

/-- Total raw arc length as an improper Lebesgue integral. -/
def totalRawArcLength : ℝ :=
  ∫ t : ℝ in Set.Ioi 0, ‖deriv curve t‖

theorem total_raw_arc_length_le : totalRawArcLength ≤ 8 / 9 := by
  have hmajor :
      IntegrableOn (fun t => (8 / 3 : ℝ) * decay t)
        (Set.Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0)
      (0 : ℝ)).const_mul (8 / 3 : ℝ)
  calc
    totalRawArcLength ≤
        ∫ t : ℝ in Set.Ioi 0, (8 / 3 : ℝ) * decay t :=
      integral_mono speed_integrable hmajor speed_le
    _ = 8 / 9 := by
      rw [integral_const_mul]
      change (8 / 3 : ℝ) *
        (∫ t : ℝ in Set.Ioi 0, Real.exp ((-3 : ℝ) * t)) = 8 / 9
      rw [integral_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0) (0 : ℝ)]
      norm_num

def rawArcLength (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, ‖deriv curve s‖

theorem raw_arc_length_le (t : ℝ) (ht : 0 ≤ t) :
    rawArcLength t ≤ (8 / 9) * (1 - decay t) := by
  have hc : Continuous decay :=
    continuous_iff_continuousAt.mpr fun s =>
      (decay_hasDerivAt s).continuousAt
  have hmajor :
      IntervalIntegrable (fun s => (8 / 3 : ℝ) * decay s)
        volume 0 t :=
    (continuous_const.mul hc).intervalIntegrable 0 t
  have hprimitive : ∀ s,
      HasDerivAt (fun u => -(8 / 9 : ℝ) * decay u)
        ((8 / 3 : ℝ) * decay s) s := by
    intro s
    convert (decay_hasDerivAt s).const_mul (-(8 / 9 : ℝ)) using 1 <;>
      ring
  calc
    rawArcLength t ≤
        ∫ s in (0 : ℝ)..t, (8 / 3 : ℝ) * decay s :=
      intervalIntegral.integral_mono_on ht
        (speed_continuous.intervalIntegrable 0 t) hmajor
        (fun s _ => speed_le s)
    _ = -(8 / 9 : ℝ) * decay t -
        (-(8 / 9 : ℝ) * decay 0) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hprimitive s) hmajor
    _ = (8 / 9) * (1 - decay t) := by
      simp only [decay, mul_zero, Real.exp_zero, mul_one]
      ring

theorem raw_arc_length_uniform_le (t : ℝ) (ht : 0 ≤ t) :
    rawArcLength t ≤ 8 / 9 := by
  have h := raw_arc_length_le t ht
  have hp := decay_pos t
  linarith

/-- PAPER-GAP: the normalization already fails at time one. -/
theorem not_normalized :
    ¬ (∀ t : ℝ, 0 ≤ t → t ≤ rawArcLength t) := by
  intro h
  have hupper := raw_arc_length_uniform_le 1 (by norm_num)
  have hlower := h 1 (by norm_num)
  linarith

end BFK

/-! ## B13: shifted maximal sources and elimination of unused constants -/

theorem linear_substitution_degree_le {ι κ : Type*}
    (g : ι → MvPolynomial κ ℚ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (q : MvPolynomial ι ℚ) :
    (aeval g q).totalDegree ≤ q.totalDegree := by
  classical
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun e he => ?_)
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  calc
    (e.prod fun i k => g i ^ k).totalDegree
        ≤ ∑ i ∈ e.support, (g i ^ e i).totalDegree :=
      totalDegree_finset_prod _ _
    _ ≤ ∑ i ∈ e.support, e i := Finset.sum_le_sum fun i _ =>
      (totalDegree_pow _ _).trans (by
        simpa using Nat.mul_le_mul_left (e i) (hg i))
    _ = e.sum fun _ k => k := rfl
    _ ≤ q.totalDegree := le_totalDegree he

def translatePolynomial {d : ℕ}
    (c : Fin d → ℚ) (q : MvPolynomial (Fin d) ℚ) :
    MvPolynomial (Fin d) ℚ :=
  aeval (fun i => X i + C (c i)) q

theorem translatePolynomial_eval {d : ℕ}
    (c : Fin d → ℚ) (q : MvPolynomial (Fin d) ℚ) (z : Fin d → ℝ) :
    (translatePolynomial c q).eval₂ (Rat.castHom ℝ) z =
      q.eval₂ (Rat.castHom ℝ) (z + fun i => (c i : ℝ)) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      simp [translatePolynomial, aeval_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
      simp only [translatePolynomial, map_add, eval₂_add] at hp hq ⊢
      rw [hp, hq]
  | mul_X p j hp =>
      simp only [translatePolynomial, map_mul, aeval_X, eval₂_mul, eval₂_add,
        eval₂_X, eval₂_C, Pi.add_apply, eq_ratCast] at hp ⊢
      rw [hp]

theorem translatePolynomial_degree_le {d : ℕ}
    (c : Fin d → ℚ) (q : MvPolynomial (Fin d) ℚ) :
    (translatePolynomial c q).totalDegree ≤ q.totalDegree := by
  apply linear_substitution_degree_le
  intro i
  exact (totalDegree_add _ _).trans
    (max_le (totalDegree_X _).le (by simp))

def initialTranslation {d : ℕ} (P : PolyPIVP d) : PolyPIVP d where
  field i := translatePolynomial P.init (P.field i)
  init _ := 0
  output := P.output

theorem initialTranslation_evalField {d : ℕ} (P : PolyPIVP d) (z : Fin d → ℝ) :
    (initialTranslation P).evalField z =
      P.evalField (z + fun i => (P.init i : ℝ)) := by
  funext i
  exact translatePolynomial_eval P.init (P.field i) z

def translatedForward {d : ℕ} {P : PolyPIVP d}
    (v : MaximalPIVP.ForwardSolution (initialTranslation P)) :
    MaximalPIVP.ForwardSolution P where
  lifetime := v.lifetime
  positive := v.positive
  trajectory t := v.trajectory t + fun i => (P.init i : ℝ)
  initial := by
    rw [v.initial]
    funext i
    simp [initialTranslation]
  ode := by
    intro t ht
    simpa only [initialTranslation_evalField] using
      (v.ode t ht).add_const (fun i => (P.init i : ℝ))

/-- Translation preserves the genuine maximal lifespan. -/
def translatedMaximal {d : ℕ} {P : PolyPIVP d}
    (u : MaximalPIVP.MaximalSolution P) :
    MaximalPIVP.MaximalSolution (initialTranslation P) where
  lifetime := u.lifetime
  positive := u.positive
  trajectory t := u.trajectory t - fun i => (P.init i : ℝ)
  initial := by
    rw [u.initial]
    funext i
    simp [initialTranslation]
  ode := by
    intro t ht
    simpa only [initialTranslation_evalField, sub_add_cancel] using
      (u.ode t ht).sub_const (fun i => (P.init i : ℝ))
  maximal := by
    intro v _
    exact u.lifetime_le (translatedForward v)

def shiftedState {d m N : ℕ}
    (o : Fin m → Fin d) (c z : Fin d → ℝ) : ShiftIndex d m N → ℝ
  | Sum.inl i => c i
  | Sum.inr (Sum.inl j) => z (o j) + c (o j)
  | Sum.inr (Sum.inr a) => jointSurrogate N a z

theorem shifted_solution_of_displacement {n d m : ℕ}
    (S : PolyPIVPFamily n d m) {N : ℕ} (hN : Even N) (hNpos : 2 ≤ N)
    (hdeg : ∀ i, (S.field i).totalDegree ≤ N)
    (x : Fin n → ℝ) (z : ℝ → Fin d → ℝ) (hzinit : z 0 = 0)
    (hz : ∀ τ, 0 ≤ τ → ∀ i,
      HasDerivAt (fun σ => z σ i)
        (S.evalField (z τ + S.evalInit x) i / jointClock N (z τ)) τ) :
    ∃ Y : ℝ → Fin (Fintype.card (ShiftIndex d m N)) → ℝ,
      (S.shiftedCompile N).IsSolution x Y ∧
      ∀ τ k, Y τ (Fintype.equivFin (ShiftIndex d m N) k) =
        shiftedState S.output (S.evalInit x) (z τ) k := by
  classical
  let c := S.evalInit x
  let Z : ℝ → ShiftIndex d m N → ℝ :=
    fun τ => shiftedState S.output c (z τ)
  have harg : ∀ τ, (fun i => c i + z τ i) = z τ + c := by
    intro τ
    funext i
    exact add_comm _ _
  have hlift : ∀ τ i, (S.shiftLift N i).eval₂ (Rat.castHom ℝ) (Z τ) =
      S.evalField (z τ + c) i / jointClock N (z τ) := by
    intro τ i
    rw [PolyPIVPFamily.shiftLift,
      liftShift_eval ((totalDegree_shiftPoly_le _).trans (hdeg i))
        c (z τ) (Z τ) (fun _ => rfl) (fun _ => rfl),
      shiftPoly_eval, harg]
    rfl
  have hinit : ∀ k, Z 0 k = (S.shiftInit N k).eval₂ (Rat.castHom ℝ) x := by
    intro k
    rcases k with i | j | a
    · rfl
    · show z 0 (S.output j) + c (S.output j) =
        (S.init (S.output j)).eval₂ (Rat.castHom ℝ) x
      rw [hzinit]
      simp only [Pi.zero_apply, zero_add]
      rfl
    · show jointSurrogate N a (z 0) =
        (if a = SurrogateIndex.zero d N then 1 else 0 :
          MvPolynomial (Fin n) ℚ).eval₂ (Rat.castHom ℝ) x
      have hclock : jointClock N (0 : Fin d → ℝ) = 1 := by
        simp [jointClock, zero_pow (by omega : N ≠ 0)]
      rw [hzinit, jointSurrogate, hclock, div_one,
        PolyPIVPFamily.surrogateIndex_eval_zero]
      split_ifs <;> simp
  have hderiv : ∀ τ, 0 ≤ τ → ∀ k, HasDerivAt (fun σ => Z σ k)
      ((S.shiftField N k).eval₂ (Rat.castHom ℝ) (Z τ)) τ := by
    intro τ hτ k
    rcases k with i | j | a
    · simpa [PolyPIVPFamily.shiftField, Z, shiftedState] using
        hasDerivAt_const τ (c i)
    · show HasDerivAt (fun σ => z σ (S.output j) + c (S.output j))
        ((S.shiftLift N (S.output j)).eval₂ (Rat.castHom ℝ) (Z τ)) τ
      rw [hlift]
      exact (hz τ hτ (S.output j)).add_const (c (S.output j))
    · have h := hasDerivAt_jointSurrogate_of hN a z τ
        (S.evalField (z τ + c)) (hz τ hτ)
      convert h using 1
      simp only [PolyPIVPFamily.shiftField, eval₂_sub, eval₂_mul, eval₂_sum,
        eval₂_C, eval₂_X, hlift, eq_ratCast, Rat.cast_natCast]
      rfl
  refine ⟨fun τ j => Z τ ((Fintype.equivFin (ShiftIndex d m N)).symm j),
    PolyPIVPFamily.ofIndexed_isSolution _ _ _ x Z hinit hderiv, ?_⟩
  intro τ k
  simp only [Equiv.symm_apply_apply]
  rfl

/-- The existing shifted compiler on a supplied maximal source of either
lifespan. Compatibility identifies its family input with that rational source. -/
theorem shifted_solution_of_maximal {n d m : ℕ} {P : PolyPIVP d}
    (u : MaximalPIVP.MaximalSolution P) (S : PolyPIVPFamily n d m)
    (x : Fin n → ℝ) (hfield : ∀ i, S.field i = P.field i)
    (hinit : S.evalInit x = fun i => (P.init i : ℝ))
    {N : ℕ} (hN : Even N) (hNpos : 2 ≤ N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    ∃ (Y : ℝ → Fin (Fintype.card (ShiftIndex d m N)) → ℝ) (s : ℝ → ℝ),
      (S.shiftedCompile N).IsSolution x Y ∧
      s 0 = 0 ∧ StrictMono s ∧
      (∀ τ, 0 ≤ τ → s τ ∈ MaximalPIVP.forwardInterval u.lifetime) ∧
      Tendsto s atTop (MaximalPIVP.endpointFilter u.lifetime) ∧
      (∀ t ∈ MaximalPIVP.forwardInterval u.lifetime,
        s (∫ v in (0 : ℝ)..t,
          jointClock N (fun i => u.trajectory v i - S.evalInit x i)) = t) ∧
      (∀ τ, 0 ≤ τ → ∀ k,
        Y τ (Fintype.equivFin (ShiftIndex d m N) k) =
          PolyPIVPFamily.shiftCurve N S.output (S.evalInit x)
            u.trajectory s τ k) := by
  classical
  have htranslated : ∀ i, ((initialTranslation P).field i).totalDegree ≤ N :=
    fun i => (translatePolynomial_degree_le P.init (P.field i)).trans (hdeg i)
  obtain ⟨tc⟩ := MaximalPIVP.exists_timeChange (translatedMaximal u) hN htranslated
  have hfamily : ∀ v, S.evalField v = P.evalField v := by
    intro v
    funext i
    simp only [PolyPIVPFamily.evalField, PolyPIVP.evalField, hfield]
  have hzinit : tc.curve 0 = 0 := by
    simpa only [initialTranslation, Rat.cast_zero] using tc.curve_initial
  have hz : ∀ τ, 0 ≤ τ → ∀ i,
      HasDerivAt (fun σ => tc.curve σ i)
        (S.evalField (tc.curve τ + S.evalInit x) i /
          jointClock N (tc.curve τ)) τ := by
    intro τ hτ i
    simpa only [hfamily, hinit, initialTranslation_evalField] using
      tc.curve_deriv τ hτ i
  obtain ⟨Y, hY, hcurve⟩ := shifted_solution_of_displacement S hN hNpos
    (fun i => by rw [hfield]; exact hdeg i) x tc.curve hzinit hz
  refine ⟨Y, tc.inverse, hY, tc.inverse_zero, tc.inverse_strictMono,
    tc.inverse_mem, tc.inverse_limit, ?_, ?_⟩
  · intro t ht
    have hclock : MaximalPIVP.jointTime (translatedMaximal u) N t =
        ∫ v in (0 : ℝ)..t,
          jointClock N (fun i => u.trajectory v i - S.evalInit x i) := by
      rw [hinit]
      rfl
    rw [← hclock]
    exact tc.left_inverse t ht
  · intro τ hτ k
    rw [hcurve]
    have heq : tc.curve τ =
        u.trajectory (tc.inverse τ) - fun i => (P.init i : ℝ) :=
      tc.curve_eq τ hτ
    rcases k with i | j | a
    · rfl
    · change tc.curve τ (S.output j) + S.evalInit x (S.output j) =
        u.trajectory (tc.inverse τ) (S.output j)
      rw [heq, hinit]
      simp
    · change jointSurrogate N a (tc.curve τ) =
        jointSurrogate N a
          (fun i => u.trajectory (tc.inverse τ) i - S.evalInit x i)
      rw [heq, hinit]
      rfl

/-- Two-sided inversion and the exact shifted-clock domain bijection. -/
theorem shifted_clock_inverse_and_bijOn {d N : ℕ} {P : PolyPIVP d}
    (u : MaximalPIVP.MaximalSolution P) (c : Fin d → ℝ)
    (s : ℝ → ℝ) (hN : Even N) (hmono : StrictMono s)
    (hmem : ∀ τ, 0 ≤ τ → s τ ∈ MaximalPIVP.forwardInterval u.lifetime)
    (hleft : ∀ t ∈ MaximalPIVP.forwardInterval u.lifetime,
      s (∫ v in (0 : ℝ)..t,
        jointClock N (fun i => u.trajectory v i - c i)) = t) :
    (∀ t ∈ MaximalPIVP.forwardInterval u.lifetime,
      s (∫ v in (0 : ℝ)..t,
        jointClock N (fun i => u.trajectory v i - c i)) = t) ∧
    (∀ τ, 0 ≤ τ →
      (∫ v in (0 : ℝ)..s τ,
        jointClock N (fun i => u.trajectory v i - c i)) = τ) ∧
    Set.BijOn
      (fun t => ∫ v in (0 : ℝ)..t,
        jointClock N (fun i => u.trajectory v i - c i))
      (MaximalPIVP.forwardInterval u.lifetime) (Set.Ici 0) := by
  have hright : ∀ τ, 0 ≤ τ →
      (∫ v in (0 : ℝ)..s τ,
        jointClock N (fun i => u.trajectory v i - c i)) = τ := by
    intro τ hτ
    apply hmono.injective
    exact hleft (s τ) (hmem τ hτ)
  refine ⟨hleft, hright, ?_, ?_, ?_⟩
  · intro t ht
    exact intervalIntegral.integral_nonneg ht.1
      (fun v _ => zero_le_one.trans (jointClock_ge_one hN _))
  · intro a ha b hb hab
    have h := congrArg s hab
    simpa only [hleft a ha, hleft b hb] using h
  · intro τ hτ
    exact ⟨s τ, hmem τ hτ, hright τ hτ⟩

/-- Finite limits of all copied outputs bound every shifted state and
preserve the complete output-vector limit. -/
theorem shifted_trajectory_bounded_and_limit {n d m N : ℕ} {P : PolyPIVP d}
    (u : MaximalPIVP.MaximalSolution P) (S : PolyPIVPFamily n d m)
    (x : Fin n → ℝ) (hN : Even N)
    (Y : ℝ → Fin (Fintype.card (ShiftIndex d m N)) → ℝ) (s : ℝ → ℝ)
    (hmem : ∀ τ, 0 ≤ τ → s τ ∈ MaximalPIVP.forwardInterval u.lifetime)
    (hslim : Tendsto s atTop (MaximalPIVP.endpointFilter u.lifetime))
    (hcurve : ∀ τ, 0 ≤ τ → ∀ k,
      Y τ (Fintype.equivFin (ShiftIndex d m N) k) =
        PolyPIVPFamily.shiftCurve N S.output (S.evalInit x) u.trajectory s τ k)
    (L : Fin m → ℝ)
    (hlim : ∀ j, Tendsto (fun t => u.trajectory t (S.output j))
      (MaximalPIVP.endpointFilter u.lifetime) (𝓝 (L j))) :
    (∃ M : ℝ, 0 < M ∧ ∀ τ, 0 ≤ τ → ‖Y τ‖ ≤ M) ∧
      Tendsto (fun τ => (S.shiftedCompile N).outputAt Y τ) atTop (𝓝 L) := by
  classical
  let c := S.evalInit x
  let b : Fin m → ℝ := fun j => MaximalPIVP.coordinateSup u (S.output j)
  let M := ‖c‖ + ‖b‖ + 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hb : ∀ j, BddAbove (MaximalPIVP.coordinateValues u (S.output j)) :=
    fun j => MaximalPIVP.coordinateValues_bddAbove u (S.output j) (hlim j)
  refine ⟨⟨M, hM, ?_⟩, ?_⟩
  · intro τ hτ
    refine (pi_norm_le_iff_of_nonneg hM.le).mpr fun a => ?_
    rw [Real.norm_eq_abs]
    obtain ⟨k, rfl⟩ := (Fintype.equivFin (ShiftIndex d m N)).surjective a
    rw [hcurve τ hτ k]
    rcases k with i | j | a
    · change |c i| ≤ M
      have hc := norm_le_pi_norm c i
      rw [Real.norm_eq_abs] at hc
      dsimp [M]
      linarith [norm_nonneg b]
    · change |u.trajectory (s τ) (S.output j)| ≤ M
      have hout := MaximalPIVP.coordinate_le_sup u (S.output j) (hb j) (hmem τ hτ)
      have hcoord := norm_le_pi_norm b j
      rw [Real.norm_eq_abs] at hcoord
      have habs := le_abs_self (b j)
      change |u.trajectory (s τ) (S.output j)| ≤ b j at hout
      dsimp [M]
      linarith [norm_nonneg c]
    · change |jointSurrogate N a (fun i => u.trajectory (s τ) i - c i)| ≤ M
      have hw := jointSurrogate_abs_le_one hN a
        (fun i => u.trajectory (s τ) i - c i)
      dsimp [M]
      linarith [norm_nonneg c, norm_nonneg b]
  · refine tendsto_pi_nhds.mpr fun j => ?_
    refine ((hlim j).comp hslim).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    change u.trajectory (s τ) (S.output j) =
      Y τ (Fintype.equivFin (ShiftIndex d m N) (Sum.inr (Sum.inl j)))
    rw [hcurve τ hτ]
    rfl

/-- Exactly the constants occurring in the shifted source field p(z+c). -/
def occurringConstants {n d m : ℕ} (S : PolyPIVPFamily n d m) :
    Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun j =>
    ∃ i, Sum.inl j ∈ (shiftPoly (S.field i)).vars

abbrev ReducedShiftIndex {n d m : ℕ} (S : PolyPIVPFamily n d m) (N : ℕ) :=
  {i : Fin d // i ∈ occurringConstants S} ⊕ (Fin m ⊕ SurrogateIndex d N)

def reducedShiftEmbedding {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) :
    ReducedShiftIndex S N → ShiftIndex d m N
  | Sum.inl i => Sum.inl i.1
  | Sum.inr k => Sum.inr k

def reducedShiftVar {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) :
    ShiftIndex d m N → MvPolynomial (ReducedShiftIndex S N) ℚ
  | Sum.inl i => if h : i ∈ occurringConstants S then X (Sum.inl ⟨i, h⟩) else 0
  | Sum.inr k => X (Sum.inr k)

def reducedShiftHom {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) :
    MvPolynomial (ShiftIndex d m N) ℚ →ₐ[ℚ]
      MvPolynomial (ReducedShiftIndex S N) ℚ :=
  aeval (reducedShiftVar S N)

theorem reducedShiftHom_C {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) (q : ℚ) :
    reducedShiftHom S N (C q) = C q := by
  simp [reducedShiftHom, aeval_C, MvPolynomial.algebraMap_eq]

theorem reducedShiftHom_X {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) (k : ShiftIndex d m N) :
    reducedShiftHom S N (X k) = reducedShiftVar S N k := by
  simp [reducedShiftHom]

theorem reduced_zMon_rebuild {n d m N : ℕ}
    (S : PolyPIVPFamily n d m) (e : (Fin d ⊕ Fin d) →₀ ℕ) :
    rename (reducedShiftEmbedding S N)
      (reducedShiftHom S N (zMon (m := m) N e)) = zMon (m := m) N e := by
  classical
  unfold zMon
  split_ifs
  · simp [reducedShiftHom, reducedShiftVar, reducedShiftEmbedding]
  · simp

theorem reduced_shiftLift_rebuild {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) (i : Fin d) :
    rename (reducedShiftEmbedding S N)
      (reducedShiftHom S N (S.shiftLift N i)) = S.shiftLift N i := by
  classical
  unfold PolyPIVPFamily.shiftLift liftShift
  simp only [map_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hp :
      rename (reducedShiftEmbedding S N)
        (reducedShiftHom S N
          (∏ j : Fin d, X (Sum.inl j) ^ e (Sum.inl j))) =
        ∏ j : Fin d, X (Sum.inl j) ^ e (Sum.inl j) := by
    simp only [map_prod, map_pow, reducedShiftHom_X]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j ∈ occurringConstants S
    · simp [reducedShiftVar, hj, reducedShiftEmbedding]
    · have hnot : Sum.inl j ∉ (shiftPoly (S.field i)).vars := by
        intro hvar
        apply hj
        simp only [occurringConstants, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i, hvar⟩
      have hz := MvPolynomial.mem_support_notMem_vars_zero he hnot
      simp only [hz, pow_zero]
  simp only [map_mul, reducedShiftHom_C, rename_C, hp, reduced_zMon_rebuild]

/-- Exact reconstruction of every full field polynomial after renaming. -/
theorem reducedShiftField_rebuild {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) (k : ShiftIndex d m N) :
    rename (reducedShiftEmbedding S N)
      (reducedShiftHom S N (S.shiftField N k)) = S.shiftField N k := by
  rcases k with i | j | a
  · simp [PolyPIVPFamily.shiftField]
  · exact reduced_shiftLift_rebuild S N (S.output j)
  · simp only [PolyPIVPFamily.shiftField, map_sub, map_sum, map_mul,
      reducedShiftHom_C, rename_C, reducedShiftHom_X,
      reducedShiftVar, reducedShiftEmbedding, rename_X,
      reduced_shiftLift_rebuild]

def reducedShiftField {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) (k : ReducedShiftIndex S N) :
    MvPolynomial (ReducedShiftIndex S N) ℚ :=
  reducedShiftHom S N (S.shiftField N (reducedShiftEmbedding S N k))

/-- Output initializers stay unchanged even if their constants are deleted. -/
def reducedShiftInit {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) (k : ReducedShiftIndex S N) :
    MvPolynomial (Fin n) ℚ :=
  S.shiftInit N (reducedShiftEmbedding S N k)

def reducedShiftCompile {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) :
    PolyPIVPFamily n (Fintype.card (ReducedShiftIndex S N)) m :=
  PolyPIVPFamily.ofIndexed (reducedShiftField S N) (reducedShiftInit S N)
    (fun j => Sum.inr (Sum.inl j))

theorem card_reducedShiftIndex {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) :
    Fintype.card (ReducedShiftIndex S N) =
      (occurringConstants S).card + (m + (d + N).choose N) := by
  simp [ReducedShiftIndex, Fintype.card_sum, card_surrogateIndex]

theorem reducedShiftInit_output {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) (j : Fin m) :
    reducedShiftInit S N (Sum.inr (Sum.inl j)) = S.init (S.output j) := rfl

theorem reducedShiftHom_degree_le {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ)
    (q : MvPolynomial (ShiftIndex d m N) ℚ) :
    (reducedShiftHom S N q).totalDegree ≤ q.totalDegree := by
  apply linear_substitution_degree_le
  intro k
  rcases k with i | k
  · by_cases hi : i ∈ occurringConstants S <;> simp [reducedShiftVar, hi]
  · simp [reducedShiftVar]

theorem shifted_field_degree_le {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) {D : ℕ}
    (hdeg : ∀ i, (S.field i).totalDegree ≤ D) (k : ShiftIndex d m N) :
    (S.shiftField N k).totalDegree ≤ 3 + D := by
  let e := Fintype.equivFin (ShiftIndex d m N)
  have hforward : (rename e (S.shiftField N k)).totalDegree ≤ 3 + D := by
    simpa only [PolyPIVPFamily.shiftedCompile, PolyPIVPFamily.ofIndexed,
      e, Equiv.symm_apply_apply] using S.shiftedCompile_totalDegree_le N hdeg (e k)
  have hback := totalDegree_rename_le e.symm (rename e (S.shiftField N k))
  have hback' : (S.shiftField N k).totalDegree ≤
      (rename e (S.shiftField N k)).totalDegree := by
    simpa only [MvPolynomial.rename_rename, e.symm_comp_self,
      MvPolynomial.rename_id_apply] using hback
  exact hback'.trans hforward

theorem reducedShiftCompile_degree_le {n d m : ℕ}
    (S : PolyPIVPFamily n d m) (N : ℕ) {D : ℕ}
    (hdeg : ∀ i, (S.field i).totalDegree ≤ D)
    (j : Fin (Fintype.card (ReducedShiftIndex S N))) :
    ((reducedShiftCompile S N).field j).totalDegree ≤ 3 + D := by
  refine (totalDegree_rename_le _ _).trans
    ((reducedShiftHom_degree_le S N _).trans ?_)
  exact shifted_field_degree_le S N hdeg _

/-- Projection of any full shifted solution, with no increase in norm. -/
theorem reducedShiftCompile_solution {n d m N : ℕ}
    (S : PolyPIVPFamily n d m) (x : Fin n → ℝ)
    (Y : ℝ → Fin (Fintype.card (ShiftIndex d m N)) → ℝ)
    (hY : (S.shiftedCompile N).IsSolution x Y) :
    ∃ R : ℝ → Fin (Fintype.card (ReducedShiftIndex S N)) → ℝ,
      (reducedShiftCompile S N).IsSolution x R ∧
      (∀ τ k, R τ (Fintype.equivFin (ReducedShiftIndex S N) k) =
        Y τ (Fintype.equivFin (ShiftIndex d m N)
          (reducedShiftEmbedding S N k))) ∧
      (∀ τ, ‖R τ‖ ≤ ‖Y τ‖) := by
  classical
  let e := Fintype.equivFin (ShiftIndex d m N)
  let eR := Fintype.equivFin (ReducedShiftIndex S N)
  let Z : ℝ → ReducedShiftIndex S N → ℝ :=
    fun τ k => Y τ (e (reducedShiftEmbedding S N k))
  have hinit : ∀ k, Z 0 k = (reducedShiftInit S N k).eval₂ (Rat.castHom ℝ) x := by
    intro k
    change Y 0 (e (reducedShiftEmbedding S N k)) =
      (S.shiftInit N (reducedShiftEmbedding S N k)).eval₂ (Rat.castHom ℝ) x
    simpa only [PolyPIVPFamily.evalInit, PolyPIVPFamily.shiftedCompile,
      PolyPIVPFamily.ofIndexed, e, Equiv.symm_apply_apply] using
      congrFun hY.1 (e (reducedShiftEmbedding S N k))
  have hderiv : ∀ τ, 0 ≤ τ → ∀ k, HasDerivAt (fun σ => Z σ k)
      ((reducedShiftField S N k).eval₂ (Rat.castHom ℝ) (Z τ)) τ := by
    intro τ hτ k
    have h := hasDerivAt_pi.mp (hY.2 τ hτ) (e (reducedShiftEmbedding S N k))
    refine h.congr_deriv ?_
    change (rename e
      (S.shiftField N (e.symm (e (reducedShiftEmbedding S N k))))).eval₂
        (Rat.castHom ℝ) (Y τ) =
      (reducedShiftField S N k).eval₂ (Rat.castHom ℝ) (Z τ)
    rw [Equiv.symm_apply_apply, eval₂_rename,
      ← reducedShiftField_rebuild S N (reducedShiftEmbedding S N k), eval₂_rename]
    rfl
  refine ⟨fun τ j => Z τ (eR.symm j),
    PolyPIVPFamily.ofIndexed_isSolution _ _ _ x Z hinit hderiv, ?_, ?_⟩
  · intro τ k
    change Z τ (eR.symm (eR k)) = Z τ k
    rw [Equiv.symm_apply_apply]
  · intro τ
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg (Y τ))).mpr fun j => ?_
    exact norm_le_pi_norm (Y τ) (e (reducedShiftEmbedding S N (eR.symm j)))

/-- Reduced-dimensional maximal-source theorem with exact trajectories,
boundedness, and output-vector limit preservation. -/
theorem reduced_shifted_solution_of_maximal {n d m : ℕ} {P : PolyPIVP d}
    (u : MaximalPIVP.MaximalSolution P) (S : PolyPIVPFamily n d m)
    (x : Fin n → ℝ) (hfield : ∀ i, S.field i = P.field i)
    (hinit : S.evalInit x = fun i => (P.init i : ℝ))
    {N : ℕ} (hN : Even N) (hNpos : 2 ≤ N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    ∃ (R : ℝ → Fin (Fintype.card (ReducedShiftIndex S N)) → ℝ) (s : ℝ → ℝ),
      (reducedShiftCompile S N).IsSolution x R ∧
      s 0 = 0 ∧ StrictMono s ∧
      (∀ τ, 0 ≤ τ → s τ ∈ MaximalPIVP.forwardInterval u.lifetime) ∧
      Tendsto s atTop (MaximalPIVP.endpointFilter u.lifetime) ∧
      (∀ t ∈ MaximalPIVP.forwardInterval u.lifetime,
        s (∫ v in (0 : ℝ)..t,
          jointClock N (fun i => u.trajectory v i - S.evalInit x i)) = t) ∧
      (∀ τ, 0 ≤ τ → ∀ k,
        R τ (Fintype.equivFin (ReducedShiftIndex S N) k) =
          PolyPIVPFamily.shiftCurve N S.output (S.evalInit x)
            u.trajectory s τ (reducedShiftEmbedding S N k)) ∧
      (∀ L : Fin m → ℝ,
        (∀ j, Tendsto (fun t => u.trajectory t (S.output j))
          (MaximalPIVP.endpointFilter u.lifetime) (𝓝 (L j))) →
        (∃ M : ℝ, 0 < M ∧ ∀ τ, 0 ≤ τ → ‖R τ‖ ≤ M) ∧
          Tendsto (fun τ => (reducedShiftCompile S N).outputAt R τ) atTop (𝓝 L)) := by
  obtain ⟨Y, s, hY, hs, hmono, hmem, hslim, hleft, hcurve⟩ :=
    shifted_solution_of_maximal u S x hfield hinit hN hNpos hdeg
  obtain ⟨R, hR, hproj, hnorm⟩ := reducedShiftCompile_solution S x Y hY
  refine ⟨R, s, hR, hs, hmono, hmem, hslim, hleft, ?_, ?_⟩
  · intro τ hτ k
    rw [hproj τ k, hcurve τ hτ]
  · intro L hlim
    obtain ⟨⟨M, hM, hbound⟩, hL⟩ :=
      shifted_trajectory_bounded_and_limit u S x hN Y s hmem hslim hcurve L hlim
    refine ⟨⟨M, hM, fun τ hτ => (hnorm τ).trans (hbound τ hτ)⟩, ?_⟩
    refine hL.congr' (Filter.Eventually.of_forall fun τ => ?_)
    funext j
    change Y τ (Fintype.equivFin (ShiftIndex d m N) (Sum.inr (Sum.inl j))) =
      R τ (Fintype.equivFin (ReducedShiftIndex S N) (Sum.inr (Sum.inl j)))
    exact (hproj τ (Sum.inr (Sum.inl j))).symm

/-! ## B14: the product clock and its reduced compiler -/

section Product

variable {d : ℕ}

/-- Product-clock lifted fields have degree at most the source dimension. -/
theorem productLift_degree (N : ℕ) (q : MvPolynomial (Fin d) ℚ) :
    (productLift N q).totalDegree ≤ d := by
  classical
  unfold productLift
  apply totalDegree_finsetSum_le
  intro b hb
  have hp : (∏ j : Fin d, (X (some (j, b j)) :
      MvPolynomial (ProductIndex d N) ℚ)).totalDegree ≤ d := by
    simpa using totalDegree_finsetProd Finset.univ
      (fun j : Fin d => (X (some (j, b j)) :
        MvPolynomial (ProductIndex d N) ℚ))
  exact (totalDegree_mul _ _).trans
    (by simpa only [totalDegree_C, zero_add] using hp)

theorem productField_degree (P : PolyPIVP d) (N : ℕ) (i : Fin d)
    (m : Fin (N + 1)) :
    (productField P N i m).totalDegree ≤ d + 2 := by
  have ha : (C (((m : ℕ) : ℚ)) * X (some (i, predExp m)) :
      MvPolynomial (ProductIndex d N) ℚ).totalDegree ≤ 1 :=
    totalDegree_C_mul_X_le _ _
  have hb : (C ((N : ℚ)) * X (some (i, topExp N)) * X (some (i, m)) :
      MvPolynomial (ProductIndex d N) ℚ).totalDegree ≤ 2 := by
    have hc : (C ((N : ℚ)) * X (some (i, topExp N)) :
        MvPolynomial (ProductIndex d N) ℚ).totalDegree ≤ 1 :=
      totalDegree_C_mul_X_le _ _
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)
  have hp : (C (((m : ℕ) : ℚ)) * X (some (i, predExp m)) -
      C ((N : ℚ)) * X (some (i, topExp N)) * X (some (i, m)) :
      MvPolynomial (ProductIndex d N) ℚ).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (max_le (ha.trans (by omega)) hb)
  unfold productField
  have hl := productLift_degree N (P.field i)
  exact (totalDegree_mul _ _).trans (by omega)

theorem productFieldAll_degree (P : PolyPIVP d) (N : ℕ)
    (k : ProductIndex d N) :
    (productFieldAll P N k).totalDegree ≤ d + 2 := by
  rcases k with _ | ⟨i, m⟩
  · exact (productLift_degree N _).trans (by omega)
  · exact productField_degree P N i m

/-- Degree bound for the actual reindexed product compiler. -/
theorem productClockCompile_degree (P : PolyPIVP d) (N : ℕ)
    (j : Fin (productDim d N)) :
    ((P.productClockCompile N).field j).totalDegree ≤ d + 2 :=
  (totalDegree_rename_le _ _).trans (productFieldAll_degree P N _)

/-- The product clock dominates the joint sum clock. -/
theorem jointClock_le_productClock {N : ℕ} (hN : Even N)
    (y : Fin d → ℝ) :
    jointClock N y ≤ productClock N y := by
  classical
  have h : ∀ s : Finset (Fin d),
      1 + ∑ i ∈ s, y i ^ N ≤ ∏ i ∈ s, (1 + y i ^ N) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hsum : 0 ≤ ∑ i ∈ s, y i ^ N :=
        Finset.sum_nonneg fun i _ => hN.pow_nonneg (y i)
      have haN := hN.pow_nonneg (y a)
      have hmul := mul_le_mul_of_nonneg_left ih
        (by linarith : 0 ≤ 1 + y a ^ N)
      nlinarith
  exact h Finset.univ

/-- Exact finite-source product-clock data. -/
structure ProductFiniteChange (P : PolyPIVP d)
    (u : MaximalPIVP.MaximalSolution P) (N : ℕ) where
  inverse : ℝ → ℝ
  inverse_zero : inverse 0 = 0
  inverse_continuous : Continuous inverse
  inverse_strictMono : StrictMono inverse
  inverse_mem : ∀ τ, 0 ≤ τ →
    inverse τ ∈ Set.Ico 0 u.lifetime.toReal
  left_inverse : ∀ t ∈ Set.Ico 0 u.lifetime.toReal,
    inverse (clockIntegral (fun v => productClock N (u.trajectory v)) t) = t
  right_inverse : ∀ τ, 0 ≤ τ →
    clockIntegral (fun v => productClock N (u.trajectory v)) (inverse τ) = τ
  inverse_deriv : ∀ τ, 0 ≤ τ →
    HasDerivAt inverse (productClock N (u.trajectory (inverse τ)))⁻¹ τ
  inverse_limit : Tendsto inverse atTop
    (nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal))
  curve : ℝ → Fin d → ℝ
  curve_continuous : Continuous curve
  curve_eq : ∀ τ, 0 ≤ τ → curve τ = u.trajectory (inverse τ)
  curve_initial : curve 0 = fun i => (P.init i : ℝ)
  curve_deriv : ∀ τ, 0 ≤ τ → ∀ i,
    HasDerivAt (fun σ => curve σ i)
      (P.evalField (curve τ) i / productClock N (curve τ)) τ

/-- Maximality supplies the finite product-clock time change. -/
theorem exists_productFiniteChange (P : PolyPIVP d)
    (u : MaximalPIVP.MaximalSolution P) (hfin : u.lifetime ≠ ⊤)
    {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    Nonempty (ProductFiniteChange P u N) := by
  classical
  have hT := u.finite_time_pos hfin
  obtain ⟨y, hc, heq, hd⟩ :=
    exists_extension_Iio hT u.trajectory (u.ode_finite hfin)
  obtain ⟨tc⟩ := MaximalPIVP.exists_timeChange u hN hdeg
  have hQc : ContinuousOn (fun t => productClock N (y t))
      (Set.Iio u.lifetime.toReal) :=
    (continuous_productClock N).comp_continuousOn hc
  have hQone : ∀ t, 1 ≤ productClock N (y t) :=
    fun t => productClock_ge_one hN _
  have hQunb : ¬ BddAbove
      (clockIntegral (fun t => productClock N (y t)) ''
        Set.Ico 0 u.lifetime.toReal) := by
    rintro ⟨K, hK⟩
    let τ : ℝ := max K 0 + 1
    have hτ : 0 ≤ τ := by
      dsimp [τ]
      linarith [le_max_right K 0]
    have ht : tc.inverse τ ∈ Set.Ico 0 u.lifetime.toReal := by
      have hm := tc.inverse_mem τ hτ
      rwa [MaximalPIVP.forwardInterval_finite u.positive hfin] at hm
    have hyc : ContinuousOn y (Set.Icc 0 (tc.inverse τ)) :=
      hc.mono fun v hv => hv.2.trans_lt ht.2
    have hle := intervalIntegral.integral_mono_on (μ := volume) ht.1
      (((continuous_jointClock N).comp_continuousOn hyc).intervalIntegrable_of_Icc ht.1)
      (((continuous_productClock N).comp_continuousOn hyc).intervalIntegrable_of_Icc ht.1)
      (fun v _ => jointClock_le_productClock hN (y v))
    have hj :
        clockIntegral (fun v => jointClock N (y v)) (tc.inverse τ) = τ := by
      calc
        _ = MaximalPIVP.jointTime u N (tc.inverse τ) := by
          unfold clockIntegral MaximalPIVP.jointTime
          apply intervalIntegral.integral_congr
          intro v hv
          rw [Set.uIcc_of_le ht.1] at hv
          change jointClock N (y v) = jointClock N (u.trajectory v)
          rw [heq v hv.1]
        _ = τ := tc.right_inverse τ hτ
    have hbound :
        clockIntegral (fun v => productClock N (y v)) (tc.inverse τ) ≤ K :=
      hK ⟨tc.inverse τ, ht, rfl⟩
    change clockIntegral (fun v => jointClock N (y v)) (tc.inverse τ) ≤
      clockIntegral (fun v => productClock N (y v)) (tc.inverse τ) at hle
    have hlt : K < τ := by
      dsimp [τ]
      linarith [le_max_left K 0]
    linarith
  obtain ⟨s, hs, hsT, hsd, hsc, hsm, hst, hsθ⟩ :=
    exists_inverse_timeChange_Iio hT hQc hQone hQunb
  have hnonneg : ∀ τ, 0 ≤ τ → 0 ≤ s τ :=
    fun τ hτ => hs ▸ hsm.monotone hτ
  have hclock : ∀ t, 0 ≤ t →
      clockIntegral (fun v => productClock N (u.trajectory v)) t =
      clockIntegral (fun v => productClock N (y v)) t := by
    intro t ht
    unfold clockIntegral
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le ht] at hv
    change productClock N (u.trajectory v) = productClock N (y v)
    rw [heq v hv.1]
  have hθs : ∀ τ,
      clockIntegral (fun v => productClock N (y v)) (s τ) = τ :=
    fun τ => hsm.injective (hsθ (s τ) (hsT τ))
  refine ⟨{
    inverse := s
    inverse_zero := hs
    inverse_continuous := hsc
    inverse_strictMono := hsm
    inverse_mem := fun τ hτ => ⟨hnonneg τ hτ, hsT τ⟩
    left_inverse := ?_
    right_inverse := ?_
    inverse_deriv := ?_
    inverse_limit := hst
    curve := fun τ => y (s τ)
    curve_continuous := hc.comp_continuous hsc (fun τ => hsT τ)
    curve_eq := fun τ hτ => heq (s τ) (hnonneg τ hτ)
    curve_initial := by rw [hs, heq 0 le_rfl, u.initial]
    curve_deriv := ?_ }⟩
  · intro t ht
    rw [hclock t ht.1]
    exact hsθ t ht.2
  · intro τ hτ
    rw [hclock (s τ) (hnonneg τ hτ)]
    exact hθs τ
  · intro τ hτ
    simpa only [heq (s τ) (hnonneg τ hτ)] using hsd τ
  · intro τ hτ i
    have hh := (hd (s τ) ⟨hnonneg τ hτ, hsT τ⟩).scomp τ (hsd τ)
    refine (hasDerivAt_pi.mp hh i).congr_deriv ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_eq_inv_mul]

/-- Complete finite-source trajectory and proved forward uniqueness. -/
theorem productClockCompile_solution_finite (P : PolyPIVP d)
    (u : MaximalPIVP.MaximalSolution P) (hfin : u.lifetime ≠ ⊤)
    {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    ∃ (tc : ProductFiniteChange P u N)
      (sol : PIVP.Solution (P.productClockCompile N).toPIVP),
      Continuous sol.trajectory ∧
      (∀ τ, 0 ≤ τ →
        sol.trajectory τ (P.productClockCompile N).output =
          u.trajectory (tc.inverse τ) P.output) ∧
      (∀ τ, 0 ≤ τ → ∀ i (m : Fin (N + 1)),
        sol.trajectory τ (productCoord i m) =
          coordSurrogate N i m (u.trajectory (tc.inverse τ))) ∧
      (∀ other : PIVP.Solution (P.productClockCompile N).toPIVP,
        Set.EqOn other.trajectory sol.trajectory (Set.Ici 0)) := by
  obtain ⟨tc⟩ := exists_productFiniteChange P u hfin hN hdeg
  obtain ⟨sol, hout, hsur, hcont⟩ :=
    P.productClockCompile_solution_of_curve hN hdeg
      tc.curve tc.curve_initial tc.curve_deriv
  refine ⟨tc, sol, hcont tc.curve_continuous, ?_, ?_, ?_⟩
  · intro τ hτ
    rw [hout τ, tc.curve_eq τ hτ]
  · intro τ hτ i m
    rw [hsur τ i m, tc.curve_eq τ hτ]
  · intro other
    exact MaximalPIVP.global_solution_unique _ other sol

theorem productClockCompile_finite_certified (P : PolyPIVP d)
    (u : MaximalPIVP.MaximalSolution P) (hfin : u.lifetime ≠ ⊤)
    {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N)
    {α : ℝ} (hlim : Tendsto (fun t => u.trajectory t P.output)
      (nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal)) (nhds α)) :
    ∃ btc : CertifiedBoundedTimeComputable (productDim d N) α,
      btc.pivp = P.productClockCompile N := by
  obtain ⟨tc, sol, hc, hout, hsur, _⟩ :=
    productClockCompile_solution_finite P u hfin hN hdeg
  obtain ⟨M, _, hM⟩ :=
    exists_abs_le_of_tendsto_Iio (u.finite_time_pos hfin)
      (fun t ht => (continuous_apply P.output).continuousAt.comp
        ((u.ode_finite hfin t ht).continuousAt)) hlim
  have hbd := productClockCompile_isBounded P hN sol
    (fun τ => u.trajectory (tc.inverse τ)) hout hsur
    (fun τ hτ => hM _ (tc.inverse_mem τ hτ))
  have hlim' :
      Tendsto (fun τ => sol.trajectory τ (P.productClockCompile N).output)
        atTop (nhds α) := by
    refine (hlim.comp tc.inverse_limit).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact (hout τ hτ).symm
  obtain ⟨btc, hb, _⟩ :=
    CertifiedBoundedTimeComputable.exists_of_tendsto _ sol hbd hc hlim'
  exact ⟨btc, hb⟩

/-- Keep the output and exponents 0 through N-1 for each source coordinate. -/
abbrev ReducedProductIndex (d N : ℕ) := Option (Fin d × Fin N)

abbrev reducedProductDim (d N : ℕ) :=
  Fintype.card (ReducedProductIndex d N)

theorem reducedProductDim_eq (d N : ℕ) :
    reducedProductDim d N = 1 + d * N := by
  simp only [reducedProductDim, ReducedProductIndex,
    Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The omitted top surrogate is 1 minus the zeroth surrogate. -/
def reducedProductVar {N : ℕ} (hpos : 0 < N)
    (i : Fin d) (m : Fin (N + 1)) :
    MvPolynomial (ReducedProductIndex d N) ℚ :=
  if hm : (m : ℕ) < N then X (some (i, ⟨m, hm⟩))
  else 1 - X (some (i, ⟨0, hpos⟩))

def reducedProductLift {N : ℕ} (hpos : 0 < N)
    (q : MvPolynomial (Fin d) ℚ) :
    MvPolynomial (ReducedProductIndex d N) ℚ :=
  ∑ b : MIndex d N,
    C (q.coeff b.toFinsupp) * ∏ j, reducedProductVar hpos j (b j)

def reducedProductField (P : PolyPIVP d)
    {N : ℕ} (hpos : 0 < N) :
    ReducedProductIndex d N → MvPolynomial (ReducedProductIndex d N) ℚ
  | none => reducedProductLift hpos (P.field P.output)
  | some (i, m) =>
      (C (((m : ℕ) : ℚ)) * reducedProductVar hpos i (predExp m.castSucc) -
        C ((N : ℚ)) * reducedProductVar hpos i (topExp N) *
          reducedProductVar hpos i m.castSucc) *
        reducedProductLift hpos (P.field i)

def reducedProductInit (P : PolyPIVP d) (N : ℕ) :
    ReducedProductIndex d N → ℚ
  | none => P.init P.output
  | some (i, m) => P.init i ^ (m : ℕ) / (1 + P.init i ^ N)

def reducedProductCompile (P : PolyPIVP d)
    {N : ℕ} (hpos : 0 < N) : PolyPIVP (reducedProductDim d N) :=
  PolyPIVP.ofIndexed (reducedProductField P hpos) (reducedProductInit P N) none

def reducedProductEmbedding {N : ℕ} :
    ReducedProductIndex d N → ProductIndex d N
  | none => none
  | some (i, m) => some (i, m.castSucc)

def reducedProductSubstitution {N : ℕ} (hpos : 0 < N) :
    ProductIndex d N → MvPolynomial (ReducedProductIndex d N) ℚ
  | none => X none
  | some (i, m) => reducedProductVar hpos i m

/-- Exact affine substitution of the original field on retained coordinates. -/
theorem reducedProductField_substitution (P : PolyPIVP d)
    {N : ℕ} (hpos : 0 < N) (k : ReducedProductIndex d N) :
    reducedProductField P hpos k =
      (productFieldAll P N (reducedProductEmbedding k)).eval₂
        C (reducedProductSubstitution hpos) := by
  classical
  rcases k with _ | ⟨i, m⟩
  · simp only [reducedProductField, reducedProductLift,
      reducedProductEmbedding, productFieldAll, productLift,
      eval₂_sum, eval₂_mul, eval₂_C, eval₂_prod, eval₂_X,
      reducedProductSubstitution]
  · simp only [reducedProductField, reducedProductLift,
      reducedProductEmbedding, productFieldAll, productField, productLift,
      eval₂_sum, eval₂_mul, eval₂_sub, eval₂_C, eval₂_prod, eval₂_X,
      reducedProductSubstitution]
    rfl

theorem reducedProductVar_degree {N : ℕ} (hpos : 0 < N)
    (i : Fin d) (m : Fin (N + 1)) :
    (reducedProductVar hpos i m).totalDegree ≤ 1 := by
  classical
  unfold reducedProductVar
  split_ifs
  · exact (totalDegree_X _).le
  · refine (totalDegree_sub _ _).trans ?_
    simp only [totalDegree_one, totalDegree_X]
    omega

theorem reducedProductLift_degree {N : ℕ} (hpos : 0 < N)
    (q : MvPolynomial (Fin d) ℚ) :
    (reducedProductLift hpos q).totalDegree ≤ d := by
  classical
  unfold reducedProductLift
  apply totalDegree_finsetSum_le
  intro b hb
  have hp : (∏ j : Fin d, reducedProductVar hpos j (b j)).totalDegree ≤ d := by
    have hh := (totalDegree_finsetProd Finset.univ
      (fun j : Fin d => reducedProductVar hpos j (b j))).trans
      (Finset.sum_le_sum fun j _ => reducedProductVar_degree hpos j (b j))
    simpa using hh
  exact (totalDegree_mul _ _).trans
    (by simpa only [totalDegree_C, zero_add] using hp)

theorem reducedProductField_degree (P : PolyPIVP d)
    {N : ℕ} (hpos : 0 < N) (k : ReducedProductIndex d N) :
    (reducedProductField P hpos k).totalDegree ≤ d + 2 := by
  rcases k with _ | ⟨i, m⟩
  · exact (reducedProductLift_degree hpos _).trans (by omega)
  · have hc : ∀ (c : ℚ) (j : Fin d) (l : Fin (N + 1)),
        (C c * reducedProductVar hpos j l).totalDegree ≤ 1 := by
      intro c j l
      have hh := reducedProductVar_degree hpos j l
      exact (totalDegree_mul _ _).trans
        (by simpa only [totalDegree_C, zero_add] using hh)
    have ha := hc (((m : ℕ) : ℚ)) i (predExp m.castSucc)
    have hb :
        (C ((N : ℚ)) * reducedProductVar hpos i (topExp N) *
          reducedProductVar hpos i m.castSucc).totalDegree ≤ 2 := by
      have hh := hc ((N : ℚ)) i (topExp N)
      have hv := reducedProductVar_degree hpos i m.castSucc
      exact (totalDegree_mul _ _).trans (by omega)
    have hp :
        (C (((m : ℕ) : ℚ)) * reducedProductVar hpos i (predExp m.castSucc) -
          C ((N : ℚ)) * reducedProductVar hpos i (topExp N) *
            reducedProductVar hpos i m.castSucc).totalDegree ≤ 2 :=
      (totalDegree_sub _ _).trans (max_le (ha.trans (by omega)) hb)
    change ((_ - _) * reducedProductLift hpos (P.field i)).totalDegree ≤ d + 2
    have hl := reducedProductLift_degree hpos (P.field i)
    exact (totalDegree_mul _ _).trans (by omega)

theorem reducedProductCompile_degree (P : PolyPIVP d)
    {N : ℕ} (hpos : 0 < N) (j : Fin (reducedProductDim d N)) :
    ((reducedProductCompile P hpos).field j).totalDegree ≤ d + 2 :=
  (totalDegree_rename_le _ _).trans (reducedProductField_degree P hpos _)

theorem reducedProductVar_eval {N : ℕ} (hpos : 0 < N) (hN : Even N)
    (y : Fin d → ℝ) (v : ReducedProductIndex d N → ℝ)
    (hv : ∀ i (m : Fin N),
      v (some (i, m)) = coordSurrogate N i m y)
    (i : Fin d) (m : Fin (N + 1)) :
    (reducedProductVar hpos i m).eval₂ (Rat.castHom ℝ) v =
      coordSurrogate N i m y := by
  classical
  unfold reducedProductVar
  split_ifs with hm
  · simpa only [eval₂_X] using hv i ⟨m, hm⟩
  · have hmN : (m : ℕ) = N := by omega
    simp only [eval₂_sub, eval₂_one, eval₂_X, hv,
      coordSurrogate, pow_zero, hmN]
    have hnz : 1 + y i ^ N ≠ 0 :=
      (lt_of_lt_of_le one_pos (one_le_one_add_pow hN (y i))).ne'
    field_simp [hnz] <;> ring

theorem reducedProductLift_eval {N : ℕ} (hpos : 0 < N) (hN : Even N)
    {q : MvPolynomial (Fin d) ℚ} (hq : q.totalDegree ≤ N)
    (y : Fin d → ℝ) (v : ReducedProductIndex d N → ℝ)
    (hv : ∀ i (m : Fin N),
      v (some (i, m)) = coordSurrogate N i m y) :
    (reducedProductLift hpos q).eval₂ (Rat.castHom ℝ) v =
      q.eval₂ (Rat.castHom ℝ) y / productClock N y := by
  have hvar := reducedProductVar_eval hpos hN y v hv
  rw [eval₂_as_mindex_sum q hq y, Finset.sum_div]
  simp only [reducedProductLift, eval₂_sum, eval₂_mul, eval₂_C,
    eval₂_prod, hvar]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_div_assoc, eval_div_productClock]
  simp

def reducedProductCurve (N : ℕ) (o : Fin d)
    (z : ℝ → Fin d → ℝ) (τ : ℝ) : ReducedProductIndex d N → ℝ
  | none => z τ o
  | some (i, m) => coordSurrogate N i m (z τ)

def reducedProductReconstruct {N : ℕ} (hpos : 0 < N)
    (v : ReducedProductIndex d N → ℝ) : ProductIndex d N → ℝ
  | none => v none
  | some (i, m) => (reducedProductVar hpos i m).eval₂ (Rat.castHom ℝ) v

theorem reducedProductReconstruct_curve {N : ℕ}
    (hpos : 0 < N) (hN : Even N) (o : Fin d)
    (z : ℝ → Fin d → ℝ) (τ : ℝ) :
    reducedProductReconstruct hpos (reducedProductCurve N o z τ) =
      productCurve N o z τ := by
  funext k
  rcases k with _ | ⟨i, m⟩
  · rfl
  · exact reducedProductVar_eval hpos hN (z τ)
      (reducedProductCurve N o z τ) (fun _ _ => rfl) i m

theorem reducedProductCompile_solution_of_curve (P : PolyPIVP d)
    {N : ℕ} (hpos : 0 < N) (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N)
    (z : ℝ → Fin d → ℝ)
    (hzInitial : z 0 = fun i => (P.init i : ℝ))
    (hz : ∀ τ, 0 ≤ τ → ∀ i,
      HasDerivAt (fun σ => z σ i)
        (P.evalField (z τ) i / productClock N (z τ)) τ) :
    ∃ sol : PIVP.Solution (reducedProductCompile P hpos).toPIVP,
      (∀ τ k,
        sol.trajectory τ (Fintype.equivFin (ReducedProductIndex d N) k) =
          reducedProductCurve N P.output z τ k) ∧
      (Continuous z → Continuous sol.trajectory) ∧
      (∀ other : PIVP.Solution (reducedProductCompile P hpos).toPIVP,
        Set.EqOn other.trajectory sol.trajectory (Set.Ici 0)) := by
  have hInitial : ∀ k,
      reducedProductCurve N P.output z 0 k =
        (reducedProductInit P N k : ℝ) := by
    intro k
    rcases k with _ | ⟨i, m⟩
    · simp [reducedProductCurve, reducedProductInit, hzInitial]
    · simp [reducedProductCurve, reducedProductInit, hzInitial, coordSurrogate]
  have hDerivative : ∀ τ, 0 ≤ τ → ∀ k,
      HasDerivAt (fun σ => reducedProductCurve N P.output z σ k)
        ((reducedProductField P hpos k).eval₂ (Rat.castHom ℝ)
          (reducedProductCurve N P.output z τ)) τ := by
    intro τ hτ k
    rcases k with _ | ⟨i, m⟩
    · change HasDerivAt (fun σ => z σ P.output)
        ((reducedProductLift hpos (P.field P.output)).eval₂
          (Rat.castHom ℝ) (reducedProductCurve N P.output z τ)) τ
      rw [reducedProductLift_eval hpos hN (hdeg _) (z τ) _
        (fun _ _ => rfl)]
      exact hz τ hτ P.output
    · have hd := hasDerivAt_coordSurrogate P hN hdeg i m.castSucc
        z τ (hz τ hτ i) (productCurve N P.output z τ) (fun _ _ => rfl)
      have hl :
          (productLift N (P.field i)).eval₂ (Rat.castHom ℝ)
            (productCurve N P.output z τ) =
          P.evalField (z τ) i / productClock N (z τ) :=
        productLift_eval₂ (hdeg i) (z τ) _ (fun _ _ => rfl)
      have hr :
          (reducedProductLift hpos (P.field i)).eval₂ (Rat.castHom ℝ)
            (reducedProductCurve N P.output z τ) =
          P.evalField (z τ) i / productClock N (z τ) :=
        reducedProductLift_eval hpos hN (hdeg i) (z τ) _ (fun _ _ => rfl)
      have hvar := reducedProductVar_eval hpos hN (z τ)
        (reducedProductCurve N P.output z τ) (fun _ _ => rfl)
      refine hd.congr_deriv ?_
      simp only [productField, reducedProductField,
        eval₂_mul, eval₂_sub, eval₂_C, eval₂_X,
        productCurve, hl, hr, hvar]
      rfl
  obtain ⟨sol, hsol⟩ :=
    PolyPIVP.ofIndexed_solution (reducedProductField P hpos)
      (reducedProductInit P N) none
      (reducedProductCurve N P.output z) hInitial hDerivative
  refine ⟨sol, ?_, ?_, ?_⟩
  · intro τ k
    rw [hsol]
    simp
  · intro hzc
    rw [hsol]
    refine continuous_pi fun j => ?_
    rcases h : (Fintype.equivFin (ReducedProductIndex d N)).symm j with _ | ⟨i, m⟩
    · simpa [reducedProductCurve, h] using
        (continuous_apply P.output).comp hzc
    · simpa [reducedProductCurve, h] using
        (continuous_coordSurrogate hN i m).comp hzc
  · intro other
    exact MaximalPIVP.global_solution_unique _ other sol

/-- The reduced compiler for an arbitrary supplied global source, with
both clock identities and the complete forward trajectory. -/
theorem reducedProductCompile_solution (P : PolyPIVP d)
    {N : ℕ} (hpos : 0 < N) (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N)
    (sol : PIVP.Solution P.toPIVP) :
    ∃ (sol' : PIVP.Solution (reducedProductCompile P hpos).toPIVP)
      (s : ℝ → ℝ),
      Continuous sol'.trajectory ∧
      s 0 = 0 ∧ Continuous s ∧ StrictMono s ∧ Tendsto s atTop atTop ∧
      (∀ t, 0 ≤ t →
        s (∫ u in (0 : ℝ)..t, productClock N (sol.trajectory u)) = t) ∧
      (∀ τ, 0 ≤ τ →
        (∫ u in (0 : ℝ)..(s τ), productClock N (sol.trajectory u)) = τ) ∧
      (∀ τ, 0 ≤ τ →
        HasDerivAt s (productClock N (sol.trajectory (s τ)))⁻¹ τ) ∧
      (∀ τ, 0 ≤ τ → ∀ k,
        sol'.trajectory τ (Fintype.equivFin (ReducedProductIndex d N) k) =
          reducedProductCurve N P.output
            (fun σ => sol.trajectory (s σ)) τ k) ∧
      (∀ other : PIVP.Solution (reducedProductCompile P hpos).toPIVP,
        Set.EqOn other.trajectory sol'.trajectory (Set.Ici 0)) := by
  obtain ⟨solc, hcont, heq⟩ := sol.exists_continuous
  have hρc : Continuous (fun t => productClock N (solc.trajectory t)) :=
    (continuous_productClock N).comp hcont
  have hρone : ∀ t, 1 ≤ productClock N (solc.trajectory t) :=
    fun t => productClock_ge_one hN _
  obtain ⟨s, hsInitial, hsd, hsc, hsm, hst, hsθ, hθs⟩ :=
    exists_inverse_timeChange hρc hρone
  have hsNonneg : ∀ τ, 0 ≤ τ → 0 ≤ s τ :=
    fun τ hτ => hsInitial ▸ hsm.monotone hτ
  have hz : ∀ τ, 0 ≤ τ → ∀ i,
      HasDerivAt (fun σ => solc.trajectory (s σ) i)
        (P.evalField (solc.trajectory (s τ)) i /
          productClock N (solc.trajectory (s τ))) τ := by
    intro τ hτ i
    have hh := (solc.is_solution (s τ) (hsNonneg τ hτ)).scomp τ (hsd τ)
    refine (hasDerivAt_pi.mp hh i).congr_deriv ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_eq_inv_mul]
    rfl
  have hzInitial : solc.trajectory (s 0) = fun i => (P.init i : ℝ) := by
    rw [hsInitial, solc.init_cond]
    rfl
  obtain ⟨sol', hcoord, hc, hu⟩ :=
    reducedProductCompile_solution_of_curve P hpos hN hdeg
      (fun σ => solc.trajectory (s σ)) hzInitial hz
  have hclock : ∀ t, 0 ≤ t →
      (∫ u in (0 : ℝ)..t, productClock N (sol.trajectory u)) =
        clockIntegral (fun u => productClock N (solc.trajectory u)) t := by
    intro t ht
    unfold clockIntegral
    apply intervalIntegral.integral_congr
    intro u hmem
    rw [Set.uIcc_of_le ht] at hmem
    change productClock N (sol.trajectory u) =
      productClock N (solc.trajectory u)
    rw [heq u hmem.1]
  refine ⟨sol', s, hc (hcont.comp hsc), hsInitial, hsc, hsm, hst,
    ?_, ?_, ?_, ?_, hu⟩
  · intro t ht
    rw [hclock t ht]
    exact hsθ t
  · intro τ hτ
    rw [hclock (s τ) (hsNonneg τ hτ)]
    exact hθs τ
  · intro τ hτ
    simpa only [heq (s τ) (hsNonneg τ hτ)] using hsd τ
  · intro τ hτ k
    rw [hcoord τ k]
    rcases k with _ | ⟨i, m⟩
    · exact congrFun (heq (s τ) (hsNonneg τ hτ)) P.output
    · exact congrArg (coordSurrogate N i m)
        (heq (s τ) (hsNonneg τ hτ))

theorem reducedProductCompile_certified (P : PolyPIVP d)
    {N : ℕ} (hpos : 0 < N) (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N)
    (sol : PIVP.Solution P.toPIVP)
    {α : ℝ}
    (hlim : Tendsto (fun t => sol.trajectory t P.output) atTop (nhds α)) :
    ∃ btc : CertifiedBoundedTimeComputable (reducedProductDim d N) α,
      btc.pivp = reducedProductCompile P hpos := by
  obtain ⟨sol', s, hc, hsInitial, _, hsm, hst, _, _, _, hcoord, _⟩ :=
    reducedProductCompile_solution P hpos hN hdeg sol
  have hsNonneg : ∀ τ, 0 ≤ τ → 0 ≤ s τ :=
    fun τ hτ => hsInitial ▸ hsm.monotone hτ
  obtain ⟨M, _, hM⟩ := exists_abs_le_of_tendsto
    (fun t ht => (continuous_apply P.output).continuousAt.comp
      ((sol.is_solution t ht).continuousAt)) hlim
  have hout : ∀ τ, 0 ≤ τ →
      sol'.trajectory τ (reducedProductCompile P hpos).output =
        sol.trajectory (s τ) P.output := by
    intro τ hτ
    exact hcoord τ hτ none
  have hbd :
      (reducedProductCompile P hpos).toPIVP.IsBounded sol'.trajectory := by
    refine ⟨max M 1, lt_max_of_lt_right one_pos, fun τ hτ => ?_⟩
    refine (pi_norm_le_iff_of_nonneg
      (le_trans zero_le_one (le_max_right _ _))).2 fun j => ?_
    rw [Real.norm_eq_abs]
    obtain ⟨k, rfl⟩ :=
      (Fintype.equivFin (ReducedProductIndex d N)).surjective j
    rw [hcoord τ hτ k]
    rcases k with _ | ⟨i, m⟩
    · exact (hM _ (hsNonneg τ hτ)).trans (le_max_left _ _)
    · exact (coordSurrogate_abs_le_one hN i m.castSucc _).trans
        (le_max_right _ _)
  have hlim' :
      Tendsto (fun τ => sol'.trajectory τ (reducedProductCompile P hpos).output)
        atTop (nhds α) := by
    refine (hlim.comp hst).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact (hout τ hτ).symm
  obtain ⟨btc, hb, _⟩ :=
    CertifiedBoundedTimeComputable.exists_of_tendsto _ sol' hbd hc hlim'
  exact ⟨btc, hb⟩

/-- Every reduced solution reconstructs the full forward product solution. -/
theorem reducedProductCompile_reconstruct_solution (P : PolyPIVP d)
    {N : ℕ} (hpos : 0 < N) (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N)
    (z : ℝ → Fin d → ℝ)
    (hzInitial : z 0 = fun i => (P.init i : ℝ))
    (hz : ∀ τ, 0 ≤ τ → ∀ i,
      HasDerivAt (fun σ => z σ i)
        (P.evalField (z τ) i / productClock N (z τ)) τ)
    (small : PIVP.Solution (reducedProductCompile P hpos).toPIVP)
    (large : PIVP.Solution (P.productClockCompile N).toPIVP)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    reducedProductReconstruct hpos
      (fun k => small.trajectory τ (Fintype.equivFin (ReducedProductIndex d N) k)) =
      (fun k => large.trajectory τ (Fintype.equivFin (ProductIndex d N) k)) := by
  obtain ⟨sm, hsm, _, _⟩ :=
    reducedProductCompile_solution_of_curve P hpos hN hdeg z hzInitial hz
  obtain ⟨lg, hout, hsur, _⟩ :=
    P.productClockCompile_solution_of_curve hN hdeg z hzInitial hz
  have hsmall : small.trajectory τ = sm.trajectory τ :=
    (MaximalPIVP.global_solution_unique _ small sm) hτ
  have hlarge : large.trajectory τ = lg.trajectory τ :=
    (MaximalPIVP.global_solution_unique _ large lg) hτ
  have hf :
      (fun k => small.trajectory τ (Fintype.equivFin (ReducedProductIndex d N) k)) =
        reducedProductCurve N P.output z τ := by
    funext k
    rw [congrFun hsmall (Fintype.equivFin (ReducedProductIndex d N) k), hsm τ k]
  rw [hf, reducedProductReconstruct_curve hpos hN P.output z τ]
  funext k
  rw [congrFun hlarge (Fintype.equivFin (ProductIndex d N) k)]
  rcases k with _ | ⟨i, m⟩
  · change z τ P.output = lg.trajectory τ (P.productClockCompile N).output
    exact (hout τ).symm
  · change coordSurrogate N i m (z τ) = lg.trajectory τ (productCoord i m)
    exact (hsur τ i m).symm

theorem reducedProductCompile_solution_finite (P : PolyPIVP d)
    (u : MaximalPIVP.MaximalSolution P) (hfin : u.lifetime ≠ ⊤)
    {N : ℕ} (hpos : 0 < N) (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    ∃ (tc : ProductFiniteChange P u N)
      (sol : PIVP.Solution (reducedProductCompile P hpos).toPIVP),
      Continuous sol.trajectory ∧
      (∀ τ, 0 ≤ τ → ∀ k,
        sol.trajectory τ (Fintype.equivFin (ReducedProductIndex d N) k) =
          reducedProductCurve N P.output
            (fun σ => u.trajectory (tc.inverse σ)) τ k) ∧
      (∀ other : PIVP.Solution (reducedProductCompile P hpos).toPIVP,
        Set.EqOn other.trajectory sol.trajectory (Set.Ici 0)) := by
  obtain ⟨tc⟩ := exists_productFiniteChange P u hfin hN hdeg
  obtain ⟨sol, hcoord, hc, hu⟩ :=
    reducedProductCompile_solution_of_curve P hpos hN hdeg
      tc.curve tc.curve_initial tc.curve_deriv
  refine ⟨tc, sol, hc tc.curve_continuous, ?_, hu⟩
  intro τ hτ k
  rw [hcoord τ k]
  rcases k with _ | ⟨i, m⟩
  · exact congrFun (tc.curve_eq τ hτ) P.output
  · exact congrArg (coordSurrogate N i m) (tc.curve_eq τ hτ)

theorem reducedProductCompile_finite_certified (P : PolyPIVP d)
    (u : MaximalPIVP.MaximalSolution P) (hfin : u.lifetime ≠ ⊤)
    {N : ℕ} (hpos : 0 < N) (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N)
    {α : ℝ} (hlim : Tendsto (fun t => u.trajectory t P.output)
      (nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal)) (nhds α)) :
    ∃ btc : CertifiedBoundedTimeComputable (reducedProductDim d N) α,
      btc.pivp = reducedProductCompile P hpos := by
  obtain ⟨tc, sol, hc, hcoord, _⟩ :=
    reducedProductCompile_solution_finite P u hfin hpos hN hdeg
  obtain ⟨M, _, hM⟩ :=
    exists_abs_le_of_tendsto_Iio (u.finite_time_pos hfin)
      (fun t ht => (continuous_apply P.output).continuousAt.comp
        ((u.ode_finite hfin t ht).continuousAt)) hlim
  have hout : ∀ τ, 0 ≤ τ →
      sol.trajectory τ (reducedProductCompile P hpos).output =
        u.trajectory (tc.inverse τ) P.output := by
    intro τ hτ
    exact hcoord τ hτ none
  have hbd : (reducedProductCompile P hpos).toPIVP.IsBounded sol.trajectory := by
    refine ⟨max M 1, lt_max_of_lt_right one_pos, fun τ hτ => ?_⟩
    refine (pi_norm_le_iff_of_nonneg
      (le_trans zero_le_one (le_max_right _ _))).2 fun j => ?_
    rw [Real.norm_eq_abs]
    obtain ⟨k, rfl⟩ :=
      (Fintype.equivFin (ReducedProductIndex d N)).surjective j
    rw [hcoord τ hτ k]
    rcases k with _ | ⟨i, m⟩
    · exact (hM _ (tc.inverse_mem τ hτ)).trans (le_max_left _ _)
    · exact (coordSurrogate_abs_le_one hN i m.castSucc _).trans (le_max_right _ _)
  have hlim' :
      Tendsto (fun τ => sol.trajectory τ (reducedProductCompile P hpos).output)
        atTop (nhds α) := by
    refine (hlim.comp tc.inverse_limit).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact (hout τ hτ).symm
  obtain ⟨btc, hb, _⟩ :=
    CertifiedBoundedTimeComputable.exists_of_tendsto _ sol hbd hc hlim'
  exact ⟨btc, hb⟩

end Product

end Ripple.BACJournalRemarks

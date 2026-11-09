/-
  Ripple.Core.CRNReadout — [BAC] journal draft §7 (`sec:crn-pipeline`): the readout modules and
  the GPAC ⇒ CRN composition, with the modulus relation in the types.

  The draft's analysis (§7.2) is for the linearized equation only, and its Thm 7.3 claims
  `μ_Z(r) = μ(r) + O(1)`, which does not follow (errata E7.1-E7.5 in
  `docs/refactor/BAC2-PAPER.md` §7). The repair (BAC2-PAPER.md §7.1-7.7) works
  with the exact solution of the reciprocal module `q' = 1 − x q`,
  `q(t) = e^{−X(t)} (q₀ + ∫₀ᵗ e^{X(s)} ds)`, `X = ∫₀ᵗ x` (`invFilter`), and a Lyapunov estimate
  for `(q − 1/α)²`. The Anderson–Joshi readout is `Z = 1/q` with `q₀ = 1`; double inversion is
  `q` applied twice with `q₀ = 0`.

  Main results:
  * `invFilter_converges` (BAC2-PAPER §7.2): `|q(t) − 1/α| < e^{−r}` for
    `t > max(μ(r + k), T₀) + (4/α) r + C`.
  * `ajReadout_spec`, `doubleInversion_spec` (`thm:crn-preserves`, Thm 7.3, corrected):
    `μ_Z(r) ≤ max(μ(r + k), 0) + c r + C` with `c = 4/α`, resp. `c = 4/α + 4α`.
  * `crn_of_certified` (BAC2-PAPER §7.5): a bounded ℚ-PIVP computing `α > 0` gives a mass-action
    CRN (`PolyCRNDecomposition`) with all initial values `0`, nonnegative species and
    single-species output, computing `α` with modulus `≤ max(μ(r + k), 0) + (4/α + 4α) r + C`.
  * `isPolyTimeCRNComputable_iff` (`cor:crn-realizable`, Cor 7.4; [RTCRN2] main theorem for
    `n = 1`): for `α > 0` and `n ≥ 1`, polynomial-time GPAC = polynomial-time CRN.
  * `IsCRNComputable.isLPPComputable` ([LPP] Main Theorem, GPAC ⇒ LPP, for `α ∈ [0, 1]`).
  * `isPolyTimeCRNComputable_rpow` (`cor:crn-power`, Cor 6.5).
  * `input_limited`, `module_limited` (`lem:input-limited`, Lemma 7.1 with the repaired
    hypothesis `ε'/ε → 0`; `lem:module-limited`, Lemma 7.2), for the linear equation.
-/

import Ripple.Core.InitShift
import Ripple.Core.PowerClosure
import Ripple.DualRail.PolynomialScaleDualRailBounded
import Ripple.LPP.Compiler
import Ripple.LPP.AlgebraicLPP

namespace Ripple

open MvPolynomial Filter Topology MeasureTheory

namespace CRNReadout

/-! ## The comparison lemma (BAC2-PAPER §7.1) -/

/-- If `V' ≤ −a (V − c)` on `(T, t)` and `V` is continuous on `[T, t]`, then
`V(t) ≤ c + (V(T) − c) e^{−a(t − T)}`. -/
theorem comparison {V V' : ℝ → ℝ} {a c T t : ℝ} (hTt : T ≤ t)
    (hc : ContinuousOn V (Set.Icc T t))
    (hd : ∀ s ∈ Set.Ioo T t, HasDerivAt V (V' s) s)
    (hle : ∀ s ∈ Set.Ioo T t, V' s ≤ -a * (V s - c)) :
    V t ≤ c + (V T - c) * Real.exp (-(a * (t - T))) := by
  have hWc : ContinuousOn (fun s => Real.exp (a * s) * (V s - c)) (Set.Icc T t) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (hc.sub continuousOn_const)
  have hWd : ∀ s ∈ Set.Ioo T t, HasDerivAt (fun s => Real.exp (a * s) * (V s - c))
      (Real.exp (a * s) * (V' s + a * (V s - c))) s := by
    intro s hs
    have he : HasDerivAt (fun s => Real.exp (a * s)) (Real.exp (a * s) * a) s := by
      simpa using ((hasDerivAt_id s).const_mul a).exp
    exact (he.mul ((hd s hs).sub_const c)).congr_deriv (by ring)
  have hanti : AntitoneOn (fun s => Real.exp (a * s) * (V s - c)) (Set.Icc T t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc T t) hWc
      (f' := fun s => Real.exp (a * s) * (V' s + a * (V s - c))) (fun s hs => ?_)
      (fun s hs => ?_)
    · rw [interior_Icc] at hs
      exact (hWd s hs).hasDerivWithinAt
    · rw [interior_Icc] at hs
      have := hle s hs
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have hWt : Real.exp (a * t) * (V t - c) ≤ Real.exp (a * T) * (V T - c) :=
    hanti ⟨le_rfl, hTt⟩ ⟨hTt, le_rfl⟩ hTt
  have hpos := Real.exp_pos (a * t)
  have hE : Real.exp (-(a * (t - T))) * Real.exp (a * t) = Real.exp (a * T) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : (V t - c) * Real.exp (a * t) ≤
      ((V T - c) * Real.exp (-(a * (t - T)))) * Real.exp (a * t) := by
    rw [mul_assoc, hE]; linarith
  have h2 := le_of_mul_le_mul_right h1 hpos
  linarith

/-! ## The reciprocal module `q' = 1 − x q` (BAC2-PAPER §7.2) -/

/-- `X(t) = ∫₀ᵗ x`. -/
noncomputable def prim (x : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, x s

theorem prim_hasDerivAt {x : ℝ → ℝ} (hx : Continuous x) (t : ℝ) :
    HasDerivAt (prim x) (x t) t :=
  (hx.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem prim_continuous {x : ℝ → ℝ} (hx : Continuous x) : Continuous (prim x) :=
  continuous_iff_continuousAt.2 fun t => (prim_hasDerivAt hx t).continuousAt

/-- The explicit solution `q(t) = e^{−X(t)} (q₀ + ∫₀ᵗ e^{X(s)} ds)` of `q' = 1 − x q`,
`q(0) = q₀`. -/
noncomputable def invFilter (x : ℝ → ℝ) (q₀ t : ℝ) : ℝ :=
  Real.exp (-prim x t) * (q₀ + ∫ s in (0 : ℝ)..t, Real.exp (prim x s))

theorem invFilter_zero (x : ℝ → ℝ) (q₀ : ℝ) : invFilter x q₀ 0 = q₀ := by
  simp [invFilter, prim]

theorem invFilter_hasDerivAt {x : ℝ → ℝ} (hx : Continuous x) (q₀ t : ℝ) :
    HasDerivAt (invFilter x q₀) (1 - x t * invFilter x q₀ t) t := by
  have hc : Continuous fun s => Real.exp (prim x s) :=
    Real.continuous_exp.comp (prim_continuous hx)
  have hI := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hE : HasDerivAt (fun s => Real.exp (-prim x s)) (Real.exp (-prim x t) * (-x t)) t :=
    ((prim_hasDerivAt hx t).neg).exp
  have h := hE.mul (hI.const_add q₀)
  refine h.congr_deriv ?_
  have h1 : Real.exp (-prim x t) * Real.exp (prim x t) = 1 := by
    rw [← Real.exp_add]; simp
  unfold invFilter
  linear_combination h1

theorem invFilter_continuous {x : ℝ → ℝ} (hx : Continuous x) (q₀ : ℝ) :
    Continuous (invFilter x q₀) :=
  continuous_iff_continuousAt.2 fun t => (invFilter_hasDerivAt hx q₀ t).continuousAt

theorem invFilter_nonneg (x : ℝ → ℝ) {q₀ t : ℝ} (hq : 0 ≤ q₀) (ht : 0 ≤ t) :
    0 ≤ invFilter x q₀ t :=
  mul_nonneg (Real.exp_pos _).le
    (add_nonneg hq (intervalIntegral.integral_nonneg ht fun s _ => (Real.exp_pos _).le))

theorem invFilter_pos (x : ℝ → ℝ) {q₀ t : ℝ} (hq : 0 < q₀) (ht : 0 ≤ t) :
    0 < invFilter x q₀ t :=
  mul_pos (Real.exp_pos _)
    (add_pos_of_pos_of_nonneg hq
      (intervalIntegral.integral_nonneg ht fun s _ => (Real.exp_pos _).le))

/-- The Lyapunov step of BAC2-PAPER §7.2: with `w = 1/α`, `E = q − w`, `D = x − α`, if
`x ≥ α/2` and `D² ≤ η²` then `2E(1 − x q) ≤ −(α/2)(E² − 4η²w⁴)`. -/
theorem lyapunov_step {α w x q η : ℝ} (hα : 0 < α) (hw : α * w = 1) (hx : α / 2 ≤ x)
    (hD : (x - α) ^ 2 ≤ η ^ 2) :
    2 * (q - w) * (1 - x * q) ≤ -(α / 2) * ((q - w) ^ 2 - 4 * η ^ 2 * w ^ 4) := by
  have hw0 : 0 < w := by
    have : 0 < α * w := by rw [hw]; exact one_pos
    exact pos_of_mul_pos_right this hα.le
  set E := q - w with hE
  set D := x - α with hDdef
  have hid : 1 - x * q = -x * E - D * w := by
    simp only [hE, hDdef]; linear_combination (-1 : ℝ) * hw
  rw [hid]
  have h1 : 0 ≤ (x - α / 2) * E ^ 2 := mul_nonneg (by linarith) (sq_nonneg E)
  have h2 : 0 ≤ (α / 2) * (E + 2 * D * w ^ 2) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2' : (α / 2) * (E + 2 * D * w ^ 2) ^ 2 =
      (α / 2) * E ^ 2 + 2 * E * D * w + 2 * D ^ 2 * w ^ 3 := by
    linear_combination (2 * E * D * w + 2 * D ^ 2 * w ^ 3) * hw
  have h4 : D ^ 2 * w ^ 3 ≤ η ^ 2 * w ^ 3 := mul_le_mul_of_nonneg_right hD (by positivity)
  have h5 : (α / 2) * (4 * η ^ 2 * w ^ 4) = 2 * η ^ 2 * w ^ 3 := by
    linear_combination (2 * η ^ 2 * w ^ 3) * hw
  nlinarith

/-- BAC2-PAPER §7.2 (b), (c): the reciprocal module converges to `1/α` with modulus
`max(μ(r + k), T₀) + (4/α) r + C`; no bound on `x` is needed. -/
theorem invFilter_converges {α : ℝ} (hα : 0 < α) {x : ℝ → ℝ} (hx : Continuous x)
    {μ : ℕ → ℝ} (hμ : ∀ r : ℕ, ∀ t, μ r < t → |x t - α| < Real.exp (-(r : ℝ))) (q₀ : ℝ) :
    ∃ (k : ℕ) (T₀ K C : ℝ), 0 ≤ T₀ ∧ 0 ≤ C ∧
      (∀ t, T₀ ≤ t → (invFilter x q₀ t - 1 / α) ^ 2 ≤ K) ∧
      ∀ r : ℕ, ∀ t, max (μ (r + k)) T₀ + 4 / α * r + C < t →
        |invFilter x q₀ t - 1 / α| < Real.exp (-(r : ℝ)) := by
  set w : ℝ := 1 / α with hw_def
  have hw : α * w = 1 := by rw [hw_def]; exact mul_one_div_cancel hα.ne'
  have hw0 : 0 < w := by rw [hw_def]; positivity
  clear_value w
  set q := invFilter x q₀ with hq_def
  -- `r₀` with `e^{−r₀} ≤ α/2`.
  obtain ⟨r₀, hr₀⟩ := exists_nat_gt (Real.log (2 / α))
  have hr₀' : Real.exp (-(r₀ : ℝ)) ≤ α / 2 := by
    have h := Real.exp_lt_exp.mpr (neg_lt_neg hr₀)
    rw [Real.exp_neg (Real.log _), Real.exp_log (by positivity), inv_div] at h
    exact h.le
  set T₀ : ℝ := max (μ r₀) 0 with hT₀
  have hT₀0 : 0 ≤ T₀ := le_max_right _ _
  have hxlo : ∀ s, T₀ < s → α / 2 ≤ x s ∧ |x s - α| ≤ α / 2 := by
    intro s hs
    have h := hμ r₀ s ((le_max_left _ _).trans_lt hs)
    have h' : |x s - α| ≤ α / 2 := (h.trans_le hr₀').le
    exact ⟨by linarith [(abs_le.mp h').1], h'⟩
  clear_value T₀
  -- the derivative of `V = (q − w)²`
  have hVc : Continuous fun s => (q s - w) ^ 2 :=
    ((invFilter_continuous hx q₀).sub continuous_const).pow 2
  have hVd : ∀ s, HasDerivAt (fun s => (q s - w) ^ 2) (2 * (q s - w) * (1 - x s * q s)) s := by
    intro s
    have := ((invFilter_hasDerivAt hx q₀ s).sub_const w).pow 2
    refine this.congr_deriv ?_
    norm_num <;> ring
  -- the generic comparison step
  have hstep : ∀ (T t η : ℝ), T₀ ≤ T → T ≤ t → (∀ s, T < s → |x s - α| ≤ η) →
      (q t - w) ^ 2 ≤ 4 * η ^ 2 * w ^ 4 +
        ((q T - w) ^ 2 - 4 * η ^ 2 * w ^ 4) * Real.exp (-(α / 2 * (t - T))) := by
    intro T t η hT hTt hη
    refine comparison (V := fun s => (q s - w) ^ 2) hTt hVc.continuousOn
      (fun s _ => hVd s) (fun s hs => ?_)
    have hs0 : T₀ < s := hT.trans_lt hs.1
    have hD : (x s - α) ^ 2 ≤ η ^ 2 := by
      have h := hη s hs.1
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    exact lyapunov_step hα hw (hxlo s hs0).1 hD
  set K : ℝ := 4 * (α / 2) ^ 2 * w ^ 4 + (q T₀ - w) ^ 2 with hK
  have hK0 : 0 < K := by positivity
  clear_value K
  have hbound : ∀ t, T₀ ≤ t → (q t - w) ^ 2 ≤ K := by
    intro t ht
    have h := hstep T₀ t (α / 2) le_rfl ht fun s hs => (hxlo s hs).2
    have hE0 := Real.exp_pos (-(α / 2 * (t - T₀)))
    have hE1 : Real.exp (-(α / 2 * (t - T₀))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have hc0 : 0 ≤ 4 * (α / 2) ^ 2 * w ^ 4 := by positivity
    have hV0 : 0 ≤ (q T₀ - w) ^ 2 := sq_nonneg _
    have : ((q T₀ - w) ^ 2 - 4 * (α / 2) ^ 2 * w ^ 4) * Real.exp (-(α / 2 * (t - T₀))) ≤
        (q T₀ - w) ^ 2 := by nlinarith
    linarith
  -- `k` with `e^k > 3 w²`
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.log (3 * w ^ 2))
  have hk' : 3 * w ^ 2 < Real.exp (k : ℝ) := by
    have := Real.exp_lt_exp.mpr hk
    rwa [Real.exp_log (by positivity)] at this
  set M : ℝ := max (Real.log (2 * K)) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hML : Real.log (2 * K) ≤ M := le_max_left _ _
  clear_value M
  refine ⟨k, T₀, K, 2 * w * M, hT₀0, by positivity, hbound, fun r t ht => ?_⟩
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  set T₁ : ℝ := max (μ (r + k)) T₀ with hT₁
  have hT₁a : μ (r + k) ≤ T₁ := le_max_left _ _
  have hT₁b : T₀ ≤ T₁ := le_max_right _ _
  clear_value T₁
  have h4w : 4 / α = 4 * w := by rw [hw_def]; ring
  have hT₁t : T₁ ≤ t := by
    have : 0 ≤ 4 / α * r + 2 * w * M := by positivity
    linarith
  set η : ℝ := Real.exp (-((r + k : ℕ) : ℝ)) with hη
  have hη' : ∀ s, T₁ < s → |x s - α| ≤ η :=
    fun s hs => (hμ (r + k) s (hT₁a.trans_lt hs)).le
  clear_value η
  have h := hstep T₁ t η hT₁b hT₁t hη'
  have hVT₁ := hbound T₁ hT₁b
  set ρ : ℝ := Real.exp (-(r : ℝ)) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  -- `4 η² w⁴ ≤ ρ²/2`
  have hηρ : η = ρ * Real.exp (-(k : ℝ)) := by
    rw [hη, hρ, ← Real.exp_add]; congr 1; push_cast; ring
  have hu : Real.exp (-(k : ℝ)) * (3 * w ^ 2) < 1 := by
    have h1 : Real.exp (-(k : ℝ)) * Real.exp (k : ℝ) = 1 := by
      rw [← Real.exp_add]; simp
    have := mul_lt_mul_of_pos_left hk' (Real.exp_pos (-(k : ℝ)))
    linarith
  have hc1 : 4 * η ^ 2 * w ^ 4 ≤ ρ ^ 2 / 2 := by
    rw [hηρ]
    set u := Real.exp (-(k : ℝ)) * w ^ 2 with hu_def
    have hu0 : 0 ≤ u := by positivity
    have hu1 : u ^ 2 ≤ 1 / 9 := by nlinarith
    have : 4 * (ρ * Real.exp (-(k : ℝ))) ^ 2 * w ^ 4 = 4 * ρ ^ 2 * u ^ 2 := by
      rw [hu_def]; ring
    rw [this]
    have h4 := mul_le_mul_of_nonneg_left hu1 (by positivity : (0 : ℝ) ≤ 4 * ρ ^ 2)
    have h5 := sq_nonneg ρ
    linarith
  -- `K e^{−(α/2)(t − T₁)} < ρ²/2`
  have hlt : 2 * (r : ℝ) + Real.log (2 * K) < α / 2 * (t - T₁) := by
    have h1 : 4 / α * r + 2 * w * M < t - T₁ := by linarith
    have h2 := mul_lt_mul_of_pos_left h1 (by positivity : (0 : ℝ) < α / 2)
    have h3 : α / 2 * (4 / α * r + 2 * w * M) = 2 * r + M := by
      rw [h4w]; linear_combination (2 * (r : ℝ) + M) * hw
    linarith
  have hE : Real.exp (-(α / 2 * (t - T₁))) < Real.exp (-(2 * (r : ℝ) + Real.log (2 * K))) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hEK : Real.exp (-(2 * (r : ℝ) + Real.log (2 * K))) * (2 * K) = ρ ^ 2 := by
    have : Real.exp (-(2 * (r : ℝ) + Real.log (2 * K))) * Real.exp (Real.log (2 * K)) =
        ρ ^ 2 := by
      rw [← Real.exp_add, hρ, sq, ← Real.exp_add]; congr 1; ring
    rwa [Real.exp_log (by positivity)] at this
  have hE0 := Real.exp_pos (-(α / 2 * (t - T₁)))
  have hc0 : 0 ≤ 4 * η ^ 2 * w ^ 4 := by positivity
  have hfin : (q t - w) ^ 2 < ρ ^ 2 := by
    have h5 : ((q T₁ - w) ^ 2 - 4 * η ^ 2 * w ^ 4) * Real.exp (-(α / 2 * (t - T₁))) ≤
        K * Real.exp (-(α / 2 * (t - T₁))) :=
      mul_le_mul_of_nonneg_right (by linarith) hE0.le
    have h6 : K * Real.exp (-(α / 2 * (t - T₁))) <
        K * Real.exp (-(2 * (r : ℝ) + Real.log (2 * K))) :=
      mul_lt_mul_of_pos_left hE hK0
    linarith [h, h5, h6, hEK, hc1]
  exact abs_lt_of_sq_lt_sq hfin hρ0.le

/-! ## The two readout modules (`thm:crn-preserves`, Thm 7.3, corrected) -/

/-- BAC2-PAPER §7.3: for `q₀ = 1` and `|x| ≤ B`, `q(t) ≥ min(1, 1/B)` on `[0, ∞)`. -/
theorem invFilter_one_ge {x : ℝ → ℝ} (hx : Continuous x) {B : ℝ} (hB : 0 < B)
    (hxB : ∀ t, 0 ≤ t → |x t| ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    min 1 (1 / B) ≤ invFilter x 1 t := by
  have hcmp := comparison (V := fun s => -invFilter x 1 s)
    (V' := fun s => -(1 - x s * invFilter x 1 s)) (a := B) (c := -(1 / B)) ht
    (invFilter_continuous hx 1).neg.continuousOn
    (fun s _ => (invFilter_hasDerivAt hx 1 s).neg)
    (fun s hs => by
      have hq := (invFilter_pos x one_pos hs.1.le).le
      have h1 : x s * invFilter x 1 s ≤ B * invFilter x 1 s :=
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hxB s hs.1.le)) hq
      have hB1 : B * (1 / B) = 1 := mul_one_div_cancel hB.ne'
      nlinarith)
  simp only [invFilter_zero, sub_zero] at hcmp
  have hE0 := Real.exp_pos (-(B * t))
  have hE1 : Real.exp (-(B * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h3 : Real.exp (-(B * t)) * min 1 (1 / B) ≤ Real.exp (-(B * t)) * 1 :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hE0.le
  have h4 : (1 - Real.exp (-(B * t))) * min 1 (1 / B) ≤ (1 - Real.exp (-(B * t))) * (1 / B) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
  nlinarith

/-- The Anderson–Joshi readout `Z = 1/q`, `q₀ = 1` ([BAC] journal draft `eq:aj-readout`). -/
noncomputable def ajReadout (x : ℝ → ℝ) (t : ℝ) : ℝ := (invFilter x 1 t)⁻¹

/-- [BAC] journal draft Thm 7.3 (`thm:crn-preserves`), Anderson–Joshi module, corrected
(BAC2-PAPER.md §7.4): `Z = 1/q` solves `Ż = xZ − Z²`, `Z(0) = 1`, stays in `(0, max(1, B)]`, and
converges to `α` with modulus `max(μ(r + k), 0) + (4/α) r + C`. The draft's `μ_Z = μ + O(1)` is
replaced by this bound (errata E7.2, E7.5). -/
theorem ajReadout_spec {α B : ℝ} (hα : 0 < α) (hB : 0 < B) {x : ℝ → ℝ} (hx : Continuous x)
    (hxB : ∀ t, 0 ≤ t → |x t| ≤ B) {μ : ℕ → ℝ}
    (hμ : ∀ r : ℕ, ∀ t, μ r < t → |x t - α| < Real.exp (-(r : ℝ))) :
    ajReadout x 0 = 1 ∧
    (∀ t, 0 ≤ t → HasDerivAt (ajReadout x) (x t * ajReadout x t - ajReadout x t ^ 2) t) ∧
    (∀ t, 0 ≤ t → 0 < ajReadout x t ∧ ajReadout x t ≤ max 1 B) ∧
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : ℕ, ∀ t, max (μ (r + k)) 0 + 4 / α * r + C < t →
      |ajReadout x t - α| < Real.exp (-(r : ℝ)) := by
  have hpos : ∀ t, 0 ≤ t → 0 < invFilter x 1 t := fun t ht => invFilter_pos x one_pos ht
  have hM : 0 < max 1 B := lt_max_of_lt_left one_pos
  have hle : ∀ t, 0 ≤ t → ajReadout x t ≤ max 1 B := by
    intro t ht
    unfold ajReadout
    rw [inv_le_comm₀ (hpos t ht) hM]
    refine le_trans (le_min ?_ ?_) (invFilter_one_ge hx hB hxB ht)
    · exact inv_le_one_of_one_le₀ (le_max_left _ _)
    · rw [one_div]; exact inv_anti₀ hB (le_max_right _ _)
  refine ⟨by simp [ajReadout, invFilter_zero], fun t ht => ?_,
    fun t ht => ⟨inv_pos.mpr (hpos t ht), hle t ht⟩, ?_⟩
  · have hq := (hpos t ht).ne'
    refine ((invFilter_hasDerivAt hx 1 t).inv hq).congr_deriv ?_
    unfold ajReadout
    field_simp
    ring
  · obtain ⟨k, T₀, K, C, hT₀, hC, -, hconv⟩ := invFilter_converges hα hx hμ 1
    obtain ⟨j, hj⟩ := exists_nat_gt (Real.log (α * max 1 B))
    have hj' : α * max 1 B < Real.exp (j : ℝ) := by
      have := Real.exp_lt_exp.mpr hj
      rwa [Real.exp_log (by positivity)] at this
    refine ⟨j + k, T₀ + 4 / α * j + C, by positivity, fun r t ht => ?_⟩
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have ht0 : 0 ≤ t := by
      have : 0 ≤ max (μ (r + (j + k))) 0 + 4 / α * r + (T₀ + 4 / α * j + C) := by positivity
      linarith
    have hm1 := le_max_left (μ (r + (j + k))) 0
    have hm2 := le_max_right (μ (r + (j + k))) 0
    have hconv' := hconv (r + j) t (by
      rw [show r + j + k = r + (j + k) by omega]
      have : max (μ (r + (j + k))) T₀ ≤ max (μ (r + (j + k))) 0 + T₀ :=
        max_le (by linarith) (by linarith)
      push_cast
      linarith)
    have hq := hpos t ht0
    have hZ : ajReadout x t - α = -(α * ajReadout x t) * (invFilter x 1 t - 1 / α) := by
      unfold ajReadout; field_simp; ring
    rw [hZ, abs_mul, abs_neg,
      abs_of_pos (show 0 < α * ajReadout x t from mul_pos hα (inv_pos.mpr hq))]
    have hZle : α * ajReadout x t ≤ α * max 1 B := mul_le_mul_of_nonneg_left (hle t ht0) hα.le
    have hρ : Real.exp (-((r + j : ℕ) : ℝ)) = Real.exp (-(r : ℝ)) * Real.exp (-(j : ℝ)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hρ] at hconv'
    have h1 : Real.exp (-(j : ℝ)) * Real.exp (j : ℝ) = 1 := by rw [← Real.exp_add]; simp
    have hρ0 := Real.exp_pos (-(r : ℝ))
    have hj0 := Real.exp_pos (-(j : ℝ))
    have h2 : α * max 1 B * Real.exp (-(j : ℝ)) < 1 := by
      have := mul_lt_mul_of_pos_right hj' hj0
      linarith
    calc α * ajReadout x t * |invFilter x 1 t - 1 / α|
        ≤ α * max 1 B * |invFilter x 1 t - 1 / α| :=
          mul_le_mul_of_nonneg_right hZle (abs_nonneg _)
      _ ≤ α * max 1 B * (Real.exp (-(r : ℝ)) * Real.exp (-(j : ℝ))) :=
          mul_le_mul_of_nonneg_left hconv'.le (by positivity)
      _ = Real.exp (-(r : ℝ)) * (α * max 1 B * Real.exp (-(j : ℝ))) := by ring
      _ < Real.exp (-(r : ℝ)) * 1 := mul_lt_mul_of_pos_left h2 hρ0
      _ = Real.exp (-(r : ℝ)) := mul_one _

/-- A continuous function on `[0, ∞)` with `(f − a)² ≤ K` on `[T, ∞)` is bounded above on
`[0, ∞)`. -/
theorem bddAbove_of_sq_le {f : ℝ → ℝ} (hf : Continuous f) {a K T : ℝ}
    (h : ∀ t, T ≤ t → (f t - a) ^ 2 ≤ K) : ∃ M, ∀ t, 0 ≤ t → f t ≤ M := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := 0) (b := T)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max M₀ (a + K + 1), fun t ht => ?_⟩
  rcases le_total t T with htT | htT
  · have := hM₀ t ⟨ht, htT⟩
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  · have h1 := h t htT
    have : f t ≤ a + K + 1 := by nlinarith [sq_nonneg (f t - a - 1 / 2)]
    exact this.trans (le_max_right _ _)

/-- [BAC] journal draft Thm 7.3 (`thm:crn-preserves`), double-inversion module
(`eq:two-recip-system`), corrected (BAC2-PAPER.md §7.4): `Y = q[x]`, `Z = q[Y]` with zero initial
values solve `Ẏ = 1 − xY`, `Ż = 1 − YZ`, are nonnegative and bounded, and `Z` converges to `α`
with modulus `max(μ(r + k), 0) + (4/α + 4α) r + C` (erratum E7.3: the draft does not argue the
cascade). -/
theorem doubleInversion_spec {α : ℝ} (hα : 0 < α) {x : ℝ → ℝ} (hx : Continuous x)
    {μ : ℕ → ℝ} (hμ : ∀ r : ℕ, ∀ t, μ r < t → |x t - α| < Real.exp (-(r : ℝ))) :
    invFilter x 0 0 = 0 ∧ invFilter (invFilter x 0) 0 0 = 0 ∧
    (∀ t, HasDerivAt (invFilter x 0) (1 - x t * invFilter x 0 t) t) ∧
    (∀ t, HasDerivAt (invFilter (invFilter x 0) 0)
      (1 - invFilter x 0 t * invFilter (invFilter x 0) 0 t) t) ∧
    (∀ t, 0 ≤ t → 0 ≤ invFilter x 0 t ∧ 0 ≤ invFilter (invFilter x 0) 0 t) ∧
    (∃ M, ∀ t, 0 ≤ t → invFilter x 0 t ≤ M ∧ invFilter (invFilter x 0) 0 t ≤ M) ∧
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : ℕ, ∀ t,
      max (μ (r + k)) 0 + (4 / α + 4 * α) * r + C < t →
        |invFilter (invFilter x 0) 0 t - α| < Real.exp (-(r : ℝ)) := by
  have hYc := invFilter_continuous hx 0
  obtain ⟨k₁, T₀, K, C₁, hT₀, hC₁, hKb, hconv₁⟩ := invFilter_converges hα hx hμ 0
  set μY : ℕ → ℝ := fun r => max (μ (r + k₁)) T₀ + 4 / α * r + C₁ with hμY
  have hα' : 0 < 1 / α := by positivity
  have hμY' : ∀ r : ℕ, ∀ t, μY r < t → |invFilter x 0 t - 1 / α| < Real.exp (-(r : ℝ)) :=
    fun r t ht => hconv₁ r t ht
  obtain ⟨k₂, T₀', K', C₂, hT₀', hC₂, hKb', hconv₂⟩ := invFilter_converges hα' hYc hμY' 0
  obtain ⟨MY, hMY⟩ := bddAbove_of_sq_le hYc hKb
  obtain ⟨MZ, hMZ⟩ := bddAbove_of_sq_le (invFilter_continuous hYc 0) hKb'
  refine ⟨invFilter_zero _ _, invFilter_zero _ _, invFilter_hasDerivAt hx 0,
    invFilter_hasDerivAt hYc 0, fun t ht => ⟨invFilter_nonneg _ le_rfl ht,
      invFilter_nonneg _ le_rfl ht⟩, ⟨max MY MZ, fun t ht =>
      ⟨(hMY t ht).trans (le_max_left _ _), (hMZ t ht).trans (le_max_right _ _)⟩⟩,
    k₂ + k₁, T₀ + 4 / α * k₂ + C₁ + T₀' + C₂, by positivity, fun r t ht => ?_⟩
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 : (1 : ℝ) / (1 / α) = α := by field_simp
  have h2 : (4 : ℝ) / (1 / α) = 4 * α := by field_simp
  have h := hconv₂ r t (by
    rw [h2]
    have hm1 := le_max_left (μ (r + (k₂ + k₁))) 0
    have hm2 := le_max_right (μ (r + (k₂ + k₁))) 0
    have hY : μY (r + k₂) ≤ max (μ (r + (k₂ + k₁))) 0 + T₀ + 4 / α * r + 4 / α * k₂ + C₁ := by
      simp only [hμY]
      rw [show r + k₂ + k₁ = r + (k₂ + k₁) by omega]
      have : max (μ (r + (k₂ + k₁))) T₀ ≤ max (μ (r + (k₂ + k₁))) 0 + T₀ :=
        max_le (by linarith) (by linarith)
      push_cast
      linarith
    have hY0 : 0 ≤ max (μ (r + (k₂ + k₁))) 0 + T₀ + 4 / α * r + 4 / α * k₂ + C₁ := by
      positivity
    have : max (μY (r + k₂)) T₀' ≤
        max (μ (r + (k₂ + k₁))) 0 + T₀ + 4 / α * r + 4 / α * k₂ + C₁ + T₀' :=
      max_le (by linarith) (by linarith)
    have h4 : (4 / α + 4 * α) * (r : ℝ) = 4 / α * r + 4 * α * r := by ring
    linarith)
  rwa [h1] at h

/-! ## Mass-action composition (BAC2-PAPER §7.5) -/

/-- Coefficient nonnegativity is preserved by `rename` along an injection. -/
theorem coeff_rename_nonneg {σ τ : Type*} (f : σ → τ) (hf : Function.Injective f)
    {p : MvPolynomial σ ℚ} (hp : ∀ m, 0 ≤ p.coeff m) (m : τ →₀ ℕ) :
    0 ≤ (rename f p).coeff m := by
  classical
  by_cases h : ∃ u : σ →₀ ℕ, u.mapDomain f = m
  · obtain ⟨u, rfl⟩ := h
    rw [coeff_rename_mapDomain f hf]
    exact hp u
  · rw [coeff_rename_eq_zero f p m (fun u hu => (h ⟨u, hu⟩).elim)]

theorem coeff_nonneg_mul {σ : Type*} {p q : MvPolynomial σ ℚ} (hp : ∀ m, 0 ≤ p.coeff m)
    (hq : ∀ m, 0 ≤ q.coeff m) (m : σ →₀ ℕ) : 0 ≤ (p * q).coeff m := by
  classical
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

theorem coeff_nonneg_add {σ : Type*} {p q : MvPolynomial σ ℚ} (hp : ∀ m, 0 ≤ p.coeff m)
    (hq : ∀ m, 0 ≤ q.coeff m) (m : σ →₀ ℕ) : 0 ≤ (p + q).coeff m := by
  rw [coeff_add]; exact add_nonneg (hp m) (hq m)

theorem coeff_nonneg_X {σ : Type*} (i : σ) (m : σ →₀ ℕ) :
    0 ≤ (X i : MvPolynomial σ ℚ).coeff m := by
  classical
  rw [coeff_X']; split_ifs <;> norm_num

theorem coeff_nonneg_C {σ : Type*} {c : ℚ} (hc : 0 ≤ c) (m : σ →₀ ℕ) :
    0 ≤ (C c : MvPolynomial σ ℚ).coeff m := by
  classical
  rw [coeff_C]; split_ifs <;> simp [hc]

theorem coeff_nonneg_one {σ : Type*} (m : σ →₀ ℕ) : 0 ≤ (1 : MvPolynomial σ ℚ).coeff m := by
  classical
  rw [coeff_one]; split_ifs <;> norm_num

/-- A reindexed system whose fields are `prod − degr · X` with nonnegative-coefficient `prod`,
`degr` and nonnegative initial values is a mass-action CRN. -/
noncomputable def ofIndexedPCD {ι : Type*} [Fintype ι] (prod degr : ι → MvPolynomial ι ℚ)
    (x₀ : ι → ℚ) (o : ι) (hp : ∀ i m, 0 ≤ (prod i).coeff m) (hd : ∀ i m, 0 ≤ (degr i).coeff m)
    (h0 : ∀ i, 0 ≤ x₀ i) :
    PolyCRNDecomposition (Fintype.card ι)
      (PolyPIVP.ofIndexed (fun i => prod i - degr i * X i) x₀ o) where
  prod j := rename (Fintype.equivFin ι) (prod ((Fintype.equivFin ι).symm j))
  degr j := rename (Fintype.equivFin ι) (degr ((Fintype.equivFin ι).symm j))
  prod_nonneg j m := coeff_rename_nonneg _ (Fintype.equivFin ι).injective (hp _) m
  degr_nonneg j m := coeff_rename_nonneg _ (Fintype.equivFin ι).injective (hd _) m
  init_nonneg j := h0 _
  field_eq j := by
    simp only [PolyPIVP.ofIndexed]
    rw [map_sub, map_mul, rename_X, Equiv.apply_symm_apply]

/-- The two readout species of the double-inversion module. -/
inductive ReadSlot
  | y
  | z
  deriving DecidableEq, Fintype

/-- Species of the composed CRN: the dual-rail species and the readout species `Y`, `Z`. -/
abbrev ReadIndex (d : ℕ) := Fin (2 * d) ⊕ ReadSlot

variable {d : ℕ}

/-- The positive rail `X⁺_o` of coordinate `o`. -/
def posIdx (o : Fin d) : Fin (2 * d) := ⟨2 * o.val, by have := o.isLt; omega⟩

/-- The negative rail `X⁻_o` of coordinate `o`. -/
def negIdx (o : Fin d) : Fin (2 * d) := ⟨2 * o.val + 1, by have := o.isLt; omega⟩

variable [NeZero d]

/-- Production polynomials: the dual-rail ones, `1 + X⁻_o Y + c⁻ Y` for `Y`, `1` for `Z`. -/
noncomputable def readProd (p : Fin d → MvPolynomial (Fin d) ℚ) (o : Fin d) (cneg : ℚ) :
    ReadIndex d → MvPolynomial (ReadIndex d) ℚ
  | .inl k => rename Sum.inl ((DualRail.polynomialScaleDualRail_pcd d p).prod k)
  | .inr .y => 1 + X (.inl (negIdx o)) * X (.inr .y) + C cneg * X (.inr .y)
  | .inr .z => 1

/-- Degradation polynomials: the dual-rail ones, `X⁺_o + c⁺` for `Y`, `Y` for `Z`. -/
noncomputable def readDegr (p : Fin d → MvPolynomial (Fin d) ℚ) (o : Fin d) (cpos : ℚ) :
    ReadIndex d → MvPolynomial (ReadIndex d) ℚ
  | .inl k => rename Sum.inl ((DualRail.polynomialScaleDualRail_pcd d p).degr k)
  | .inr .y => X (.inl (posIdx o)) + C cpos
  | .inr .z => X (.inr .y)

/-- The composed CRN of BAC2-PAPER §7.5: dual rail of `p` and the double-inversion readout driven
by `X⁺_o − X⁻_o + c⁺ − c⁻`; all initial values `0`; output `Z`. -/
noncomputable def readoutCRN (p : Fin d → MvPolynomial (Fin d) ℚ) (o : Fin d) (cpos cneg : ℚ) :
    PolyPIVP (Fintype.card (ReadIndex d)) :=
  PolyPIVP.ofIndexed (fun i => readProd p o cneg i - readDegr p o cpos i * X i) (fun _ => 0)
    (.inr .z)

theorem readProd_nonneg (p : Fin d → MvPolynomial (Fin d) ℚ) (o : Fin d) {cneg : ℚ}
    (hc : 0 ≤ cneg) (i : ReadIndex d) (m : ReadIndex d →₀ ℕ) :
    0 ≤ (readProd p o cneg i).coeff m := by
  rcases i with k | _ | _
  · exact coeff_rename_nonneg _ Sum.inl_injective
      ((DualRail.polynomialScaleDualRail_pcd d p).prod_nonneg k) m
  · exact coeff_nonneg_add (coeff_nonneg_add coeff_nonneg_one
      (coeff_nonneg_mul (coeff_nonneg_X _) (coeff_nonneg_X _)))
      (coeff_nonneg_mul (coeff_nonneg_C hc) (coeff_nonneg_X _)) m
  · exact coeff_nonneg_one m

theorem readDegr_nonneg (p : Fin d → MvPolynomial (Fin d) ℚ) (o : Fin d) {cpos : ℚ}
    (hc : 0 ≤ cpos) (i : ReadIndex d) (m : ReadIndex d →₀ ℕ) :
    0 ≤ (readDegr p o cpos i).coeff m := by
  rcases i with k | _ | _
  · exact coeff_rename_nonneg _ Sum.inl_injective
      ((DualRail.polynomialScaleDualRail_pcd d p).degr_nonneg k) m
  · exact coeff_nonneg_add (coeff_nonneg_X _) (coeff_nonneg_C hc) m
  · exact coeff_nonneg_X _ m

/-- The composed system is a mass-action CRN. -/
noncomputable def readoutCRN_pcd (p : Fin d → MvPolynomial (Fin d) ℚ) (o : Fin d) {cpos cneg : ℚ}
    (hpos : 0 ≤ cpos) (hneg : 0 ≤ cneg) :
    PolyCRNDecomposition _ (readoutCRN p o cpos cneg) :=
  ofIndexedPCD _ _ _ _ (readProd_nonneg p o hneg) (readDegr_nonneg p o hpos) fun _ => le_rfl

/-- The curve of the composed system. -/
def readTraj (s : ℝ → Fin (2 * d) → ℝ) (Y Z : ℝ → ℝ) (τ : ℝ) : ReadIndex d → ℝ
  | .inl k => s τ k
  | .inr .y => Y τ
  | .inr .z => Z τ

end CRNReadout

open CRNReadout

/-- **GPAC ⇒ CRN with the modulus relation** (BAC2-PAPER.md §7.5; [BAC] journal draft §7,
dual rail + readout). A bounded ℚ-PIVP computing `α > 0` with modulus `μ` gives a
mass-action CRN (a `PolyCRNDecomposition`) with all initial values `0`, nonnegative species and a
single-species output, computing `α` with modulus `≤ max(μ(r + k), 0) + (4/α + 4α) r + C`. The
construction: shift to zero initial values ([RTCRN2] Thm 3), dual rail with state-dependent
annihilation, double-inversion readout. -/
theorem crn_of_certified {d : ℕ} {α : ℝ} (btc : CertifiedBoundedTimeComputable d α)
    (hα : 0 < α) :
    ∃ (d' : ℕ) (btc' : CertifiedBoundedTimeComputable d' α),
      Nonempty (PolyCRNDecomposition d' btc'.pivp) ∧ (∀ i, btc'.pivp.init i = 0) ∧
      (∀ t, 0 ≤ t → ∀ i, 0 ≤ btc'.sol.trajectory t i) ∧
      ∃ (k : ℕ) (C : ℝ), ∀ r : ℕ,
        btc'.modulus r ≤ max (btc.modulus (r + k)) 0 + (4 / α + 4 * α) * r + C := by
  haveI : NeZero d := ⟨by have := btc.pivp.output.isLt; omega⟩
  set c : ℚ := btc.pivp.init btc.pivp.output with hc
  obtain ⟨btc0, hbtc0⟩ : ∃ b : CertifiedBoundedTimeComputable d (α - c),
      b = btc.shiftToZero := ⟨_, rfl⟩
  have hmod0 : btc0.modulus = btc.modulus := by rw [hbtc0]; rfl
  have h_zero : ∀ j, btc0.toSemantic.pivp.init j = 0 := by
    intro j
    change ((btc0.pivp.init j : ℚ) : ℝ) = 0
    rw [hbtc0, CertifiedBoundedTimeComputable.shiftToZero_init, Rat.cast_zero]
  obtain ⟨o, ho⟩ : ∃ o, o = btc0.pivp.output := ⟨_, rfl⟩
  obtain ⟨solDR, BDR, hBDR, hnn, hle, hdiff, hcont⟩ :=
    DualRail.polynomialScaleDualRail_bounded btc0.toSemantic btc0.pivp.field (fun _ _ => rfl)
      h_zero
  set cpos : ℚ := max c 0 with hcpos
  set cneg : ℚ := max (-c) 0 with hcneg
  have hcpos0 : 0 ≤ cpos := le_max_right _ _
  have hcneg0 : 0 ≤ cneg := le_max_right _ _
  have hcpnQ : cpos - cneg = c := by
    rcases le_total 0 c with h | h
    · rw [hcpos, hcneg, max_eq_left h, max_eq_right (by linarith : -c ≤ 0)]; ring
    · rw [hcpos, hcneg, max_eq_right h, max_eq_left (by linarith : 0 ≤ -c)]; ring
  have hcpn : (cpos : ℝ) - cneg = c := by exact_mod_cast hcpnQ
  set x : ℝ → ℝ := fun τ =>
    solDR.trajectory τ (posIdx o) - solDR.trajectory τ (negIdx o) + (c : ℝ) with hx_def
  have hxc : Continuous x :=
    (((continuous_apply _).comp hcont).sub ((continuous_apply _).comp hcont)).add
      continuous_const
  have hμx : ∀ r : ℕ, ∀ t, max (btc.modulus r) 0 < t → |x t - α| < Real.exp (-(r : ℝ)) := by
    intro r t ht
    have ht0 : 0 ≤ t := (le_max_right _ _).trans ht.le
    have hm : btc0.modulus r < t := by rw [hmod0]; exact (le_max_left _ _).trans_lt ht
    have h1 := btc0.convergence r t hm
    rw [← ho] at h1
    have h2 : solDR.trajectory t (posIdx o) - solDR.trajectory t (negIdx o) =
        btc0.sol.trajectory t o := hdiff t ht0 o
    have h3 : x t - α = btc0.sol.trajectory t o - (α - c) := by
      simp only [hx_def]; linear_combination h2
    rw [h3]; exact h1
  obtain ⟨-, -, hYd, hZd, hYZnn, ⟨M, hM⟩, k, C, hC, hconv⟩ := doubleInversion_spec hα hxc hμx
  set Y := invFilter x 0 with hY
  set Z := invFilter Y 0 with hZ
  set P := readoutCRN btc0.pivp.field o cpos cneg with hP
  set Zt : ℝ → ReadIndex d → ℝ := readTraj solDR.trajectory Y Z with hZt
  have hcomp : ∀ τ, (Zt τ ∘ Sum.inl) = solDR.trajectory τ := fun τ => rfl
  have hcastp : (Rat.castHom ℝ) cpos = (cpos : ℝ) := rfl
  have hcastn : (Rat.castHom ℝ) cneg = (cneg : ℝ) := rfl
  obtain ⟨sol, hsol⟩ := PolyPIVP.ofIndexed_solution
    (fun i => readProd btc0.pivp.field o cneg i - readDegr btc0.pivp.field o cpos i * X i)
    (fun _ => 0) (.inr .z) Zt
    (by
      intro i
      rcases i with k | _ | _
      · have h0 := congrFun solDR.init_cond k
        simp only [hZt, readTraj, Rat.cast_zero]
        rw [h0]
        simp [PolyPIVP.toPIVP, DualRail.polynomialScaleDualRail]
      · simp [hZt, readTraj, hY, invFilter_zero]
      · simp [hZt, readTraj, hZ, invFilter_zero])
    (by
      intro τ hτ i
      rcases i with k | _ | _
      · refine ((hasDerivAt_pi.1 (solDR.is_solution τ hτ)) k).congr_deriv ?_
        simp only [readProd, readDegr, eval₂_sub, eval₂_mul, eval₂_rename, eval₂_X, hcomp]
        change ((DualRail.polynomialScaleDualRail d btc0.pivp.field).field k).eval₂
          (Rat.castHom ℝ) (solDR.trajectory τ) = _
        rw [(DualRail.polynomialScaleDualRail_pcd d btc0.pivp.field).field_eq k, eval₂_sub,
          eval₂_mul, eval₂_X]
        rfl
      · refine (hYd τ).congr_deriv ?_
        simp only [readProd, readDegr, eval₂_sub, eval₂_add, eval₂_mul, eval₂_one, eval₂_X,
          eval₂_C, hcastp, hcastn, hZt, readTraj, hx_def]
        linear_combination (Y τ) * hcpn
      · refine (hZd τ).congr_deriv ?_
        simp only [readProd, readDegr, eval₂_sub, eval₂_mul, eval₂_one, eval₂_X, hZt, readTraj])
  have hval : ∀ τ j, sol.trajectory τ j = Zt τ ((Fintype.equivFin (ReadIndex d)).symm j) := by
    intro τ j; rw [hsol]
  have hZtnn : ∀ τ, 0 ≤ τ → ∀ i, 0 ≤ Zt τ i := by
    intro τ hτ i
    rcases i with k | _ | _
    · exact hnn τ hτ k
    · exact (hYZnn τ hτ).1
    · exact (hYZnn τ hτ).2
  set Mall : ℝ := max (max BDR M) 1 with hMall
  have hMall0 : 0 < Mall := lt_max_of_lt_right one_pos
  have hbd : P.toPIVP.IsBounded sol.trajectory := by
    refine ⟨Mall, hMall0, fun τ hτ => ?_⟩
    refine (pi_norm_le_iff_of_nonneg hMall0.le).2 fun j => ?_
    rw [hval, Real.norm_eq_abs, abs_of_nonneg (hZtnn τ hτ _)]
    generalize (Fintype.equivFin (ReadIndex d)).symm j = i
    have h1 : BDR ≤ Mall := (le_max_left _ _).trans (le_max_left _ _)
    have h2 : M ≤ Mall := (le_max_right _ _).trans (le_max_left _ _)
    rcases i with k | _ | _
    · exact (hle τ hτ k).trans h1
    · exact (hM τ hτ).1.trans h2
    · exact (hM τ hτ).2.trans h2
  have hout : ∀ τ, sol.trajectory τ P.output = Z τ := by
    intro τ
    rw [hval]
    simp [hP, readoutCRN, PolyPIVP.ofIndexed, hZt, readTraj]
  obtain ⟨btc', hpivp, hmod, heq⟩ := CertifiedBoundedTimeComputable.exists_of_solution P sol hbd
    (fun r => max (max (btc.modulus (r + k)) 0) 0 + (4 / α + 4 * α) * r + C)
    (fun r t ht => by rw [hout]; exact hconv r t ht)
  refine ⟨_, btc', ?_, ?_, ?_, k, C, fun r => ?_⟩
  · rw [hpivp]; exact ⟨readoutCRN_pcd _ o hcpos0 hcneg0⟩
  · intro i; rw [hpivp]; rfl
  · intro t ht i
    rw [heq t ht, hval]
    exact hZtnn t ht _
  · have h := hmod r
    beta_reduce at h
    rw [h, max_eq_left (le_max_right (btc.modulus (r + k)) 0)]
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have h1 := le_max_right (btc.modulus (r + k)) 0
    have h2 : 0 ≤ (4 / α + 4 * α) * r := by positivity
    exact max_le (by linarith) le_rfl

/-- Computation of `α` by a mass-action CRN with all initial values `0` ([RTCRN2] convention)
and time modulus `O((r + 1)ⁿ)`; `n = 1` is the real-time CRN class of [RTCRN2]. -/
def IsPolyTimeCRNComputable (α : ℝ) (n : ℕ) : Prop :=
  ∃ d : ℕ, ∃ btc : CertifiedBoundedTimeComputable d α,
    Nonempty (PolyCRNDecomposition d btc.pivp) ∧ (∀ i, btc.pivp.init i = 0) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1) ^ n

/-- [BAC] journal draft Cor 7.4 (`cor:crn-realizable`), corrected (BAC2-PAPER.md §7.7): for
`α > 0` and `n ≥ 1`, a polynomial-time (degree `n`) bounded GPAC gives a polynomial-time
(degree `n`) mass-action CRN with zero initial values. The draft's `Θ` becomes `O` (no lower
bound is claimed). -/
theorem IsPolyTimeComputable.isPolyTimeCRNComputable {α : ℝ} {n : ℕ} (h : IsPolyTimeComputable α n)
    (hn : 1 ≤ n) (hα : 0 < α) : IsPolyTimeCRNComputable α n := by
  obtain ⟨d, btc, K, hK, hμ⟩ := h
  obtain ⟨d', btc', hpcd, hinit, -, k, C, hle⟩ := crn_of_certified btc hα
  set A : ℝ := 4 / α + 4 * α with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨d', btc', hpcd, hinit, K * ((k : ℝ) + 1) ^ n + A + |C| + 1, by positivity,
    fun r => ?_⟩
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  have hpow1 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ n := le_self_pow₀ hr1 (by omega)
  have hpow0 : (0 : ℝ) ≤ ((r : ℝ) + 1) ^ n := by positivity
  have hshift : (((r + k : ℕ) : ℝ) + 1) ^ n ≤ ((k : ℝ) + 1) ^ n * ((r : ℝ) + 1) ^ n := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hm : max (btc.modulus (r + k)) 0 ≤ K * (((k : ℝ) + 1) ^ n * ((r : ℝ) + 1) ^ n) :=
    max_le ((hμ (r + k)).trans (mul_le_mul_of_nonneg_left hshift hK.le)) (by positivity)
  have hCabs : C ≤ |C| * ((r : ℝ) + 1) ^ n := by
    have := le_abs_self C
    have h1 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ n := one_le_pow₀ hr1
    nlinarith [abs_nonneg C]
  have hAr : A * r ≤ A * ((r : ℝ) + 1) ^ n := mul_le_mul_of_nonneg_left (by linarith) hA0
  calc btc'.modulus r ≤ max (btc.modulus (r + k)) 0 + A * r + C := hle r
    _ ≤ (K * ((k : ℝ) + 1) ^ n + A + |C| + 1) * ((r : ℝ) + 1) ^ n := by nlinarith

/-- A CRN computation is a GPAC computation (forget the decomposition). -/
theorem IsPolyTimeCRNComputable.isPolyTimeComputable {α : ℝ} {n : ℕ}
    (h : IsPolyTimeCRNComputable α n) : IsPolyTimeComputable α n := by
  obtain ⟨d, btc, -, -, C, hC, hμ⟩ := h
  exact ⟨d, btc, C, hC, hμ⟩

/-- For `α > 0` and `n ≥ 1`: polynomial-time GPAC = polynomial-time mass-action CRN with zero
initial values. For `n = 1` this is the [RTCRN2] main theorem (real-time GPAC = real-time CRN)
in the modulus form, for positive reals. -/
theorem isPolyTimeCRNComputable_iff {α : ℝ} {n : ℕ} (hn : 1 ≤ n) (hα : 0 < α) :
    IsPolyTimeCRNComputable α n ↔ IsPolyTimeComputable α n :=
  ⟨IsPolyTimeCRNComputable.isPolyTimeComputable,
    fun h => h.isPolyTimeCRNComputable hn hα⟩

/-- [RTCRN2] main theorem, GPAC ⇒ CRN direction (modulus form, `α > 0`): a real-time
computable `α` is computed in real time by a mass-action CRN with zero initial values. -/
theorem IsRealTimeComputable.isPolyTimeCRNComputable_one {α : ℝ} (h : IsRealTimeComputable α)
    (hα : 0 < α) : IsPolyTimeCRNComputable α 1 := by
  obtain ⟨d, btc, C, hC, hμ⟩ := h
  exact IsPolyTimeComputable.isPolyTimeCRNComputable ⟨d, btc, C, hC, fun r => by simpa using hμ r⟩
    le_rfl hα

/-- [LPP] Main Theorem, GPAC ⇒ LPP direction (computability only): every
`α ∈ [0, 1]` computed by a bounded ℚ-PIVP is computed by a deterministic large-population
protocol. For `α > 0` the CRN of `crn_of_certified` feeds the [LPP] compiler
(`isLPPComputable_of_certified`); `α = 0` is `zero_lpp`. -/
theorem IsCRNComputable.isLPPComputable {α : ℝ} (h : IsCRNComputable α) (h0 : 0 ≤ α)
    (h1 : α ≤ 1) : IsLPPComputable α := by
  rcases h0.eq_or_lt with h0' | hpos
  · rw [← h0']; exact zero_lpp
  · obtain ⟨d, ⟨btc⟩⟩ := h
    obtain ⟨d', btc', ⟨pcd⟩, -⟩ := crn_of_certified btc hpos
    exact isLPPComputable_of_certified ⟨hpos.le, h1⟩ btc' pcd

/-- [BAC] journal draft Cor 6.5 (`cor:crn-power`): `α^β` (`α > 0`) is computed by a mass-action
CRN with zero initial values, in polynomial time of degree `n ≥ 1` when `α` and `β` are. The CRN
is the full dual rail of the construction of `con:power` followed by the double-inversion readout
(BAC2-PAPER.md §7.5); the selective encoding in which `z` itself is a species is not formalized. -/
theorem isPolyTimeCRNComputable_rpow {α β : ℝ} {n : ℕ} (hn : 1 ≤ n) (hα : 0 < α)
    (ha : IsPolyTimeComputable α n) (hb : IsPolyTimeComputable β n) :
    IsPolyTimeCRNComputable (α ^ β) n :=
  (isPolyTimeComputable_rpow hn hα ha hb).isPolyTimeCRNComputable hn (Real.rpow_pos_of_pos hα β)

/-- Non-vacuity of `isPolyTimeCRNComputable_rpow` and `crn_of_certified`: `√2 = 2^{1/2}` is
computed in real time by a mass-action CRN with zero initial values. -/
theorem sqrt_two_rpow_crn : IsPolyTimeCRNComputable ((2 : ℝ) ^ (1 / 2 : ℝ)) 1 :=
  sqrt_two_rpow_polyTime.isPolyTimeCRNComputable le_rfl (by positivity)

/-- Non-vacuity of `IsCRNComputable.isLPPComputable`: `(1/2)^{1/2} = 1/√2 ∈ [0, 1]` is
LPP-computable. -/
theorem inv_sqrt_two_lpp : IsLPPComputable ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) := by
  have hc : ∀ q : ℚ, IsCRNComputable (q : ℝ) := fun q => (realtime_rat_const q).isCRNComputable
  have ha : IsCRNComputable (1 / 2 : ℝ) := by simpa using hc (1 / 2)
  have hb : IsCRNComputable (1 / 2 : ℝ) := ha
  refine (isCRNComputable_rpow (by norm_num) ha hb).isLPPComputable
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num))

/-! ## The linear filter: Lemmas 7.1 and 7.2 of the draft -/

namespace CRNReadout

/-- [BAC] journal draft Lemma 7.2 (`lem:module-limited`): for `δ' = −αδ + αC e^{−βt}` on
`[0, ∞)` with `β ≠ α`, `δ(t) = (δ(0) + αC/(β − α)) e^{−αt} − (αC/(β − α)) e^{−βt}` exactly; for
`β > α` this is the draft's `(δ(0) + αC/(β−α)) e^{−αt} + O(e^{−βt})`. -/
theorem module_limited {α β Cε : ℝ} (hαβ : α ≠ β) {δ : ℝ → ℝ}
    (hδ : ∀ t, 0 ≤ t → HasDerivAt δ (-α * δ t + α * (Cε * Real.exp (-β * t))) t) {t : ℝ}
    (ht : 0 ≤ t) :
    δ t = (δ 0 + α * Cε / (β - α)) * Real.exp (-α * t) -
      α * Cε / (β - α) * Real.exp (-β * t) := by
  set D : ℝ := α * Cε / (β - α) with hD_def
  have hD : (β - α) * D = α * Cε := by
    rw [hD_def]; field_simp [sub_ne_zero.mpr hαβ.symm]
  set F : ℝ → ℝ := fun s => (δ 0 + D) * Real.exp (-α * s) - D * Real.exp (-β * s) with hF_def
  have hexp : ∀ (a s : ℝ), HasDerivAt (fun s => Real.exp (a * s)) (Real.exp (a * s) * a) s :=
    fun a s => by simpa using ((hasDerivAt_id s).const_mul a).exp
  have hF : ∀ s, HasDerivAt F ((δ 0 + D) * (Real.exp (-α * s) * (-α)) -
      D * (Real.exp (-β * s) * (-β))) s :=
    fun s => ((hexp (-α) s).const_mul (δ 0 + D)).sub ((hexp (-β) s).const_mul D)
  have hg : ∀ s, 0 ≤ s → HasDerivAt (fun s => Real.exp (α * s) * (δ s - F s)) 0 s := by
    intro s hs
    refine ((hexp α s).mul ((hδ s hs).sub (hF s))).congr_deriv ?_
    simp only [hF_def, Pi.sub_apply]
    linear_combination (-(Real.exp (α * s) * Real.exp (-β * s))) * hD
  have hconst := constant_of_has_deriv_right_zero (f := fun s => Real.exp (α * s) * (δ s - F s))
    (a := 0) (b := t) (fun s hs => (hg s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hg s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  beta_reduce at hconst
  have hF0 : Real.exp (α * 0) * (δ 0 - F 0) = 0 := by simp [hF_def]
  rw [hF0] at hconst
  have he := Real.exp_pos (α * t)
  rcases mul_eq_zero.mp hconst with h | h
  · exact absurd h he.ne'
  · exact sub_eq_zero.mp h

/-- [BAC] journal draft Lemma 7.1 (`lem:input-limited`), with the repaired hypothesis
(BAC2-PAPER.md §7.6, erratum E7.4: the draft's hypotheses `ε' → 0`, `e^{αt}|ε| → ∞` do not
suffice, e.g. `ε = (2 + sin t)/(t + 1)`): for `δ' = −αδ + αε` on `[0, ∞)`, if `ε(t) ≠ 0` for
`t ≥ T` and `ε'(t)/ε(t) → 0`, then `δ(t)/ε(t) → 1`, i.e. `δ ∼ ε`. -/
theorem input_limited {α : ℝ} (hα : 0 < α) {ε ε' δ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hε : ∀ t, 0 ≤ t → HasDerivAt ε (ε' t) t)
    (hδ : ∀ t, 0 ≤ t → HasDerivAt δ (-α * δ t + α * ε t) t)
    (hne : ∀ t, T ≤ t → ε t ≠ 0)
    (hg : Tendsto (fun t => ε' t / ε t) atTop (𝓝 0)) :
    Tendsto (fun t => δ t / ε t) atTop (𝓝 1) := by
  set u : ℝ → ℝ := fun t => (δ t - ε t) / ε t with hu_def
  set g : ℝ → ℝ := fun t => ε' t / ε t with hg_def
  set w : ℝ := 1 / α with hw_def
  have hw : α * w = 1 := by rw [hw_def]; exact mul_one_div_cancel hα.ne'
  have hw0 : 0 < w := by positivity
  have hud : ∀ s, T ≤ s → HasDerivAt u (-(α + g s) * u s - g s) s := by
    intro s hs
    have hs0 : 0 ≤ s := hT.trans hs
    have hne' := hne s hs
    refine (((hδ s hs0).sub (hε s hs0)).div (hε s hs0) hne').congr_deriv ?_
    simp only [hu_def, hg_def, Pi.sub_apply]
    field_simp
    ring
  have hVd : ∀ s, T ≤ s → HasDerivAt (fun s => u s ^ 2)
      (2 * u s * (-(α + g s) * u s - g s)) s := by
    intro s hs
    refine ((hud s hs).pow 2).congr_deriv ?_
    norm_num
  have hu0 : Tendsto u atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro e he
    set η : ℝ := min (α / 2) (α * e / 4) with hη
    have hη0 : 0 < η := lt_min (by positivity) (by positivity)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hg η hη0
    set Tη : ℝ := max N T with hTη
    have hTηT : T ≤ Tη := le_max_right _ _
    have hgη : ∀ s, Tη ≤ s → |g s| ≤ η := by
      intro s hs
      have := hN s ((le_max_left _ _).trans hs)
      rw [Real.dist_eq, sub_zero] at this
      exact this.le
    -- the bound `u² ≤ 4η²w² + u(Tη)² e^{−(α/2)(t − Tη)}`
    have hbound : ∀ t, Tη ≤ t → u t ^ 2 ≤ 4 * η ^ 2 * w ^ 2 +
        (u Tη ^ 2 - 4 * η ^ 2 * w ^ 2) * Real.exp (-(α / 2 * (t - Tη))) := by
      intro t ht
      refine comparison (V := fun s => u s ^ 2) ht
        (fun s hs => ((hVd s (hTηT.trans hs.1)).continuousAt).continuousWithinAt)
        (fun s hs => hVd s (hTηT.trans hs.1.le)) (fun s hs => ?_)
      have hgs := hgη s hs.1.le
      have hgs' := abs_le.mp hgs
      have hη2 : η ≤ α / 2 := min_le_left _ _
      have h1 : 0 ≤ (α + g s - α / 2) * u s ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have h2 : 0 ≤ (α / 2) * (u s + 2 * g s * w) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have h2' : (α / 2) * (u s + 2 * g s * w) ^ 2 =
          (α / 2) * u s ^ 2 + 2 * g s * u s + 2 * g s ^ 2 * w := by
        linear_combination (2 * g s * u s + 2 * g s ^ 2 * w) * hw
      have h3 : g s ^ 2 ≤ η ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hgs 2
      have h4 : g s ^ 2 * w ≤ η ^ 2 * w := mul_le_mul_of_nonneg_right h3 hw0.le
      have h5 : (α / 2) * (4 * η ^ 2 * w ^ 2) = 2 * η ^ 2 * w := by
        linear_combination (2 * η ^ 2 * w) * hw
      nlinarith
    -- the decaying term
    have hlin : Tendsto (fun t => -(α / 2 * (t - Tη))) atTop atBot := by
      refine tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop (by positivity) ?_)
      exact (tendsto_atTop_atTop.2 fun b => ⟨b + Tη, fun t ht => by linarith⟩ :
        Tendsto (fun t : ℝ => t - Tη) atTop atTop)
    have hdec : Tendsto (fun t => u Tη ^ 2 * Real.exp (-(α / 2 * (t - Tη)))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul (u Tη ^ 2)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hdec (e ^ 2 / 2) (by positivity)
    refine ⟨max Tη N₂, fun t ht => ?_⟩
    have htη : Tη ≤ t := (le_max_left _ _).trans ht
    have hb := hbound t htη
    have hd := hN₂ t ((le_max_right _ _).trans ht)
    rw [Real.dist_eq, sub_zero] at hd
    have hd' := (le_abs_self _).trans_lt hd
    have hE0 := Real.exp_pos (-(α / 2 * (t - Tη)))
    have hc0 : 0 ≤ 4 * η ^ 2 * w ^ 2 := by positivity
    have hηe : η ≤ α * e / 4 := min_le_right _ _
    have hc1 : 4 * η ^ 2 * w ^ 2 ≤ e ^ 2 / 4 := by
      have h1 : η * w ≤ e / 4 := by
        have := mul_le_mul_of_nonneg_right hηe hw0.le
        have h2 : α * e / 4 * w = e / 4 := by linear_combination (e / 4) * hw
        linarith
      have h3 : 0 ≤ η * w := by positivity
      have h4 := mul_le_mul h1 h1 h3 (by positivity)
      nlinarith
    have hlt : u t ^ 2 < e ^ 2 := by nlinarith
    rw [Real.dist_eq, sub_zero]
    exact abs_lt_of_sq_lt_sq hlt he.le
  have hev : (fun t => u t + 1) =ᶠ[atTop] fun t => δ t / ε t := by
    filter_upwards [eventually_ge_atTop T] with t ht
    have := hne t ht
    simp only [hu_def]
    rw [div_add_one this, sub_add_cancel]
  simpa using (hu0.add_const 1).congr' hev

end CRNReadout

end Ripple

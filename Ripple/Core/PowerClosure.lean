/-
  Ripple.Core.PowerClosure — bounded GPACs are closed under `α^β` ([BAC] §6)

  [BAC] = Chen and Huang, *Bounded Analog Complexity*, journal draft (repository `Bounded`,
  branch `BAC-Journal`). Labels: Thm 6.1 `thm:power`, Construction 6.2 `con:power`,
  Thm 6.4 `thm:power-complexity`. Repairs: `docs/refactor/BAC2-PAPER.md` §6 (signed after a cold
  review):
  - E6.1: the draft's claim `1 + x₁(t) > 0` fails when the upstream output is negative early
    (`x' = 2 − x`, `x(0) = −11`), and then the draft's system has no global solution. The
    construction here drives the low-pass filter with `x² ≥ 0` and halves the exponent
    (`powerSqCompile`, BAC2-PAPER §6.1).
  - E6.2: the draft's modulus `max(μ_α(r + C), μ_β(r + C)) + O(1)` is false (`α = 2`,
    `β = 1/2` with constant inputs); the corrected bound has an additive `r`:
    `max(max(μ_α(r + C), 0) + r + C, μ_β(r + C))` (BAC2-PAPER §6.4).

  The system, for upstream bounded ℚ-PIVPs `X' = F(X)` (output `x → α > 0`) and
  `Y' = H(Y)` (output `y → β`):
      `x₁' = (x² − 1) − x₁`, `u' = (1 − v) x₁'`, `v' = (1 − v)² x₁'`,
      `z' = ½ z (H_y(Y) u + y (1 − v) x₁')`,
  `x₁(0) = u(0) = v(0) = 0`, `z(0) = 1`, output `z`. Its solution is explicit: with
  `w(t) = e^{−t}(1 + ∫₀ᵗ eˢ x(s)² ds)` (`lowpassSq`), `x₁ = w − 1`, `u = ln w`,
  `v = 1 − 1/w`, `z = exp(½ y ln w)`.

  Main results: `rpow_certified` (Thm 6.1 with the corrected Thm 6.4 modulus, certificate
  pinned to `powerSqCompile`), `isCRNComputable_rpow` (Thm 6.1),
  `isPolyTimeComputable_rpow` (Thm 6.4, "exponentiation preserves the time complexity class",
  for every polynomial class `n ≥ 1`).
-/

import Ripple.Core.SurrogateCompilation
import Ripple.DualRail.PowerGadgetInvariant
import Mathlib.Tactic.DeriveFintype

namespace Ripple

open MvPolynomial Filter MeasureTheory Topology

/-! ## The squared low-pass filter -/

/-- `w(t) = e^{−t} (1 + ∫₀ᵗ eˢ x(s)² ds)`, the solution of `w' = x² − w`, `w(0) = 1`. -/
noncomputable def lowpassSq (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t) * (1 + ∫ s in (0 : ℝ)..t, Real.exp s * x s ^ 2)

theorem lowpassSq_zero (x : ℝ → ℝ) : lowpassSq x 0 = 1 := by
  simp [lowpassSq]

theorem lowpassSq_hasDerivAt {x : ℝ → ℝ} (hx : Continuous x) (t : ℝ) :
    HasDerivAt (lowpassSq x) (x t ^ 2 - lowpassSq x t) t := by
  have hcont : Continuous fun s => Real.exp s * x s ^ 2 :=
    Real.continuous_exp.mul (hx.pow 2)
  have hF := (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hexp : HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-t)) t := by
    have := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    simpa using this
  have h := hexp.mul (hF.const_add 1)
  have he : Real.exp (-t) * (Real.exp t * x t ^ 2) = x t ^ 2 := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  refine h.congr_deriv ?_
  rw [he]
  unfold lowpassSq
  ring

theorem exp_neg_le_lowpassSq (x : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ lowpassSq x t := by
  have h : 0 ≤ ∫ s in (0 : ℝ)..t, Real.exp s * x s ^ 2 :=
    intervalIntegral.integral_nonneg ht fun s _ => mul_nonneg (Real.exp_pos s).le (sq_nonneg _)
  unfold lowpassSq
  nlinarith [Real.exp_pos (-t)]

theorem lowpassSq_pos (x : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 < lowpassSq x t :=
  (Real.exp_pos _).trans_le (exp_neg_le_lowpassSq x ht)

/-- `w ≤ max(1, B²)` when `|x| ≤ B` on `[0, t]`. -/
theorem lowpassSq_le {x : ℝ → ℝ} (hx : Continuous x) {B t : ℝ} (ht : 0 ≤ t)
    (hB : ∀ s ∈ Set.Icc 0 t, |x s| ≤ B) : lowpassSq x t ≤ max 1 (B ^ 2) := by
  have hint : (∫ s in (0 : ℝ)..t, Real.exp s * x s ^ 2) ≤ (Real.exp t - 1) * B ^ 2 := by
    have hi1 : IntervalIntegrable (fun s => Real.exp s * x s ^ 2) volume 0 t :=
      (Real.continuous_exp.mul (hx.pow 2)).intervalIntegrable 0 t
    have hi2 : IntervalIntegrable (fun s => Real.exp s * B ^ 2) volume 0 t :=
      (Real.continuous_exp.mul continuous_const).intervalIntegrable 0 t
    have h : (∫ s in (0 : ℝ)..t, Real.exp s * x s ^ 2) ≤ ∫ s in (0 : ℝ)..t, Real.exp s * B ^ 2 :=
      intervalIntegral.integral_mono_on ht hi1 hi2 (fun s hs => mul_le_mul_of_nonneg_left
        (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB s hs) 2)
        (Real.exp_pos s).le)
    rw [intervalIntegral.integral_mul_const, integral_exp, Real.exp_zero] at h
    exact h
  have he : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hm1 : (1 : ℝ) ≤ max 1 (B ^ 2) := le_max_left _ _
  have hmB : B ^ 2 ≤ max 1 (B ^ 2) := le_max_right _ _
  have hel : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hep := Real.exp_pos (-t)
  unfold lowpassSq
  calc Real.exp (-t) * (1 + ∫ s in (0 : ℝ)..t, Real.exp s * x s ^ 2)
      ≤ Real.exp (-t) * (1 + (Real.exp t - 1) * B ^ 2) := by gcongr
    _ = Real.exp (-t) + (1 - Real.exp (-t)) * B ^ 2 := by
        rw [mul_add, mul_one, ← mul_assoc, mul_sub, he, mul_one]
    _ ≤ Real.exp (-t) * max 1 (B ^ 2) + (1 - Real.exp (-t)) * max 1 (B ^ 2) := by
        have h1 := mul_le_mul_of_nonneg_left hm1 hep.le
        have h2 := mul_le_mul_of_nonneg_left hmB (sub_nonneg.mpr hel)
        linarith
    _ = max 1 (B ^ 2) := by ring

/-- The tracking estimate of the filter (BAC2-PAPER §6.4 step 1): if `|x² − c| ≤ G` on
`[0, t]` and `|x² − c| ≤ η` on `[T, t]` with `0 ≤ T ≤ t`, then
`|w(t) − c| ≤ (|1 − c| + G) e^{−(t − T)} + η`. -/
theorem abs_lowpassSq_sub_le {x : ℝ → ℝ} (hx : Continuous x) {c G η T t : ℝ} (hT : 0 ≤ T)
    (hTt : T ≤ t) (hG : ∀ s ∈ Set.Icc 0 t, |x s ^ 2 - c| ≤ G)
    (hη : ∀ s ∈ Set.Icc T t, |x s ^ 2 - c| ≤ η) :
    |lowpassSq x t - c| ≤ (|1 - c| + G) * Real.exp (-(t - T)) + η := by
  have ht : 0 ≤ t := hT.trans hTt
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0 ⟨le_rfl, ht⟩)
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη T ⟨le_rfl, hTt⟩)
  set g : ℝ → ℝ := fun s => Real.exp s * (x s ^ 2 - c) with hg
  have hgc : Continuous g := Real.continuous_exp.mul ((hx.pow 2).sub continuous_const)
  have hid : lowpassSq x t - c =
      Real.exp (-t) * (1 - c) + Real.exp (-t) * ∫ s in (0 : ℝ)..t, g s := by
    have h1 : (∫ s in (0 : ℝ)..t, g s) =
        (∫ s in (0 : ℝ)..t, Real.exp s * x s ^ 2) - c * (Real.exp t - 1) := by
      have : (fun s => g s) = fun s => Real.exp s * x s ^ 2 - c * Real.exp s := by
        funext s; simp only [hg]; ring
      have hi1 : IntervalIntegrable (fun s => Real.exp s * x s ^ 2) volume 0 t :=
        (Real.continuous_exp.mul (hx.pow 2)).intervalIntegrable 0 t
      have hi2 : IntervalIntegrable (fun s => c * Real.exp s) volume 0 t :=
        (continuous_const.mul Real.continuous_exp).intervalIntegrable 0 t
      rw [this, intervalIntegral.integral_sub hi1 hi2,
        intervalIntegral.integral_const_mul, integral_exp, Real.exp_zero]
    have he : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [h1]
    unfold lowpassSq
    linear_combination c * he
  have hsplit : (∫ s in (0 : ℝ)..t, g s) =
      (∫ s in (0 : ℝ)..T, g s) + ∫ s in T..t, g s :=
    (intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable 0 T)
      (hgc.intervalIntegrable T t)).symm
  have hb1 : |∫ s in (0 : ℝ)..T, g s| ≤ G * (Real.exp T - 1) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hT).trans ?_
    have hi : IntervalIntegrable (fun s => G * Real.exp s) volume 0 T :=
      (continuous_const.mul Real.continuous_exp).intervalIntegrable 0 T
    have h : (∫ s in (0 : ℝ)..T, |g s|) ≤ ∫ s in (0 : ℝ)..T, G * Real.exp s :=
      intervalIntegral.integral_mono_on hT (hgc.abs.intervalIntegrable 0 T) hi
      (fun s hs => by
        show |Real.exp s * (x s ^ 2 - c)| ≤ G * Real.exp s
        rw [abs_mul, abs_of_pos (Real.exp_pos s), mul_comm]
        exact mul_le_mul_of_nonneg_right (hG s ⟨hs.1, hs.2.trans hTt⟩) (Real.exp_pos s).le)
    rwa [intervalIntegral.integral_const_mul, integral_exp, Real.exp_zero] at h
  have hb2 : |∫ s in T..t, g s| ≤ η * (Real.exp t - Real.exp T) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hTt).trans ?_
    have hi : IntervalIntegrable (fun s => η * Real.exp s) volume T t :=
      (continuous_const.mul Real.continuous_exp).intervalIntegrable T t
    have h : (∫ s in T..t, |g s|) ≤ ∫ s in T..t, η * Real.exp s :=
      intervalIntegral.integral_mono_on hTt (hgc.abs.intervalIntegrable T t) hi
      (fun s hs => by
        show |Real.exp s * (x s ^ 2 - c)| ≤ η * Real.exp s
        rw [abs_mul, abs_of_pos (Real.exp_pos s), mul_comm]
        exact mul_le_mul_of_nonneg_right (hη s hs) (Real.exp_pos s).le)
    rwa [intervalIntegral.integral_const_mul, integral_exp] at h
  have hpos := Real.exp_pos (-t)
  have hle : Real.exp (-t) ≤ Real.exp (-(t - T)) := Real.exp_le_exp.mpr (by linarith)
  have hT' : Real.exp (-t) * Real.exp T = Real.exp (-(t - T)) := by
    rw [← Real.exp_add]; ring_nf
  have he : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [hid, hsplit]
  calc |Real.exp (-t) * (1 - c) +
        Real.exp (-t) * ((∫ s in (0 : ℝ)..T, g s) + ∫ s in T..t, g s)|
      ≤ Real.exp (-t) * |1 - c| + Real.exp (-t) * (|∫ s in (0 : ℝ)..T, g s| +
          |∫ s in T..t, g s|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hpos]
        gcongr
        exact abs_add_le _ _
    _ ≤ Real.exp (-t) * |1 - c| + Real.exp (-t) * (G * (Real.exp T - 1) +
          η * (Real.exp t - Real.exp T)) := by gcongr
    _ = Real.exp (-t) * |1 - c| + G * (Real.exp (-t) * Real.exp T) - G * Real.exp (-t) +
          η * (Real.exp (-t) * Real.exp t) - η * (Real.exp (-t) * Real.exp T) := by ring
    _ ≤ (|1 - c| + G) * Real.exp (-(t - T)) + η := by
        rw [hT', he]
        have h1 : Real.exp (-t) * |1 - c| ≤ Real.exp (-(t - T)) * |1 - c| :=
          mul_le_mul_of_nonneg_right hle (abs_nonneg _)
        have h2 : 0 ≤ G * Real.exp (-t) := mul_nonneg hG0 hpos.le
        have h3 : 0 ≤ η * Real.exp (-(t - T)) := mul_nonneg hη0 (Real.exp_pos _).le
        nlinarith

/-! ## The construction ([BAC] Construction 6.2, repaired) -/

/-- The four new coordinates `x₁, u, v, z`. -/
inductive PowSlot
  | x1 | u | v | z
  deriving DecidableEq, Fintype

/-- Coordinates of the combined system: the first upstream system, the second, the new slots. -/
abbrev PowIndex (d₁ d₂ : ℕ) := Fin d₁ ⊕ (Fin d₂ ⊕ PowSlot)

variable {d₁ d₂ : ℕ}

/-- `x₁' = (x² − 1) − x₁`. -/
noncomputable def powX1RHS (Px : PolyPIVP d₁) : MvPolynomial (PowIndex d₁ d₂) ℚ :=
  X (Sum.inl Px.output) ^ 2 - 1 - X (Sum.inr (Sum.inr PowSlot.x1))

/-- The combined field: the upstream fields, then the repaired [BAC] Construction 6.2
(BAC2-PAPER §6.1). -/
noncomputable def powField (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    PowIndex d₁ d₂ → MvPolynomial (PowIndex d₁ d₂) ℚ
  | Sum.inl i => rename Sum.inl (Px.field i)
  | Sum.inr (Sum.inl j) => rename (fun k => Sum.inr (Sum.inl k)) (Py.field j)
  | Sum.inr (Sum.inr PowSlot.x1) => powX1RHS Px
  | Sum.inr (Sum.inr PowSlot.u) => (1 - X (Sum.inr (Sum.inr PowSlot.v))) * powX1RHS Px
  | Sum.inr (Sum.inr PowSlot.v) => (1 - X (Sum.inr (Sum.inr PowSlot.v))) ^ 2 * powX1RHS Px
  | Sum.inr (Sum.inr PowSlot.z) =>
      C (1 / 2 : ℚ) * X (Sum.inr (Sum.inr PowSlot.z)) *
        (rename (fun k => Sum.inr (Sum.inl k)) (Py.field Py.output) *
            X (Sum.inr (Sum.inr PowSlot.u)) +
          X (Sum.inr (Sum.inl Py.output)) * (1 - X (Sum.inr (Sum.inr PowSlot.v))) *
            powX1RHS Px)

/-- The combined initial value: the upstream ones, `x₁ = u = v = 0`, `z = 1`. -/
noncomputable def powInit (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) : PowIndex d₁ d₂ → ℚ
  | Sum.inl i => Px.init i
  | Sum.inr (Sum.inl j) => Py.init j
  | Sum.inr (Sum.inr PowSlot.z) => 1
  | Sum.inr (Sum.inr _) => 0

/-- [BAC] Construction 6.2, repaired (BAC2-PAPER §6.1, squared driving signal): the `α^β`
system as a ℚ-PIVP of dimension `d₁ + d₂ + 4`, output `z`. -/
noncomputable def PolyPIVP.powerSqCompile (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    PolyPIVP (Fintype.card (PowIndex d₁ d₂)) :=
  PolyPIVP.ofIndexed (powField Px Py) (powInit Px Py) (Sum.inr (Sum.inr PowSlot.z))

theorem card_powIndex (d₁ d₂ : ℕ) : Fintype.card (PowIndex d₁ d₂) = d₁ + (d₂ + 4) := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  rfl

/-- The explicit trajectory over the index type (BAC2-PAPER §6.2). -/
noncomputable def powCurve (X : ℝ → Fin d₁ → ℝ) (Y : ℝ → Fin d₂ → ℝ) (o₂ : Fin d₂)
    (w : ℝ → ℝ) (t : ℝ) : PowIndex d₁ d₂ → ℝ
  | Sum.inl i => X t i
  | Sum.inr (Sum.inl j) => Y t j
  | Sum.inr (Sum.inr PowSlot.x1) => w t - 1
  | Sum.inr (Sum.inr PowSlot.u) => Real.log (w t)
  | Sum.inr (Sum.inr PowSlot.v) => 1 - 1 / w t
  | Sum.inr (Sum.inr PowSlot.z) => Real.exp (1 / 2 * Y t o₂ * Real.log (w t))

/-- `|x(s) − α| ≤ e^{−r}` also at `s = μ(r)`, by continuity. -/
theorem abs_sub_le_of_modulus {f : ℝ → ℝ} (hf : Continuous f) {α : ℝ} {μ : TimeModulus}
    (h : ∀ r : ℕ, ∀ t : ℝ, t > μ r → |f t - α| < Real.exp (-(r : ℝ))) (r : ℕ) {s : ℝ}
    (hs : μ r ≤ s) : |f s - α| ≤ Real.exp (-(r : ℝ)) := by
  rcases hs.lt_or_eq with hlt | heq
  · exact (h r s hlt).le
  · subst heq
    have hca : ContinuousAt (fun u => |f u - α|) (μ r) :=
      ((hf.sub continuous_const).abs).continuousAt
    have hev : ∀ᶠ u in 𝓝[>] (μ r), |f u - α| ≤ Real.exp (-(r : ℝ)) :=
      eventually_nhdsWithin_of_forall fun u hu => (h r u hu).le
    exact le_of_tendsto (hca.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- For `K ≥ 0` and `ε > 0` there is `n : ℕ` with `K e^{−n} ≤ ε`. -/
theorem exists_nat_mul_exp_neg_le {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ n : ℕ, K * Real.exp (-(n : ℝ)) ≤ ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.log ((K + 1) / ε))
  refine ⟨n, ?_⟩
  have h1 : Real.exp (-(n : ℝ)) ≤ ε / (K + 1) := by
    have : Real.exp (-(n : ℝ)) < Real.exp (-Real.log ((K + 1) / ε)) :=
      Real.exp_lt_exp.mpr (by linarith)
    have he : Real.exp (-Real.log ((K + 1) / ε)) = ε / (K + 1) := by
      rw [Real.exp_neg, Real.exp_log (div_pos (by linarith) hε), inv_div]
    rw [he] at this
    exact this.le
  calc K * Real.exp (-(n : ℝ)) ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left h1 hK
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

/-! ## [BAC] Thm 6.1 and the corrected Thm 6.4 -/

/-- [BAC] Thm 6.1 (journal draft `thm:power`) with the corrected modulus of Thm 6.4
(`thm:power-complexity`, BAC2-PAPER §6.4): if `α > 0` and `β` are computed by bounded
ℚ-PIVPs with time moduli `μ_α`, `μ_β`, then the repaired construction `powerSqCompile`
computes `α^β` with a bounded trajectory and a time modulus at most
`max(max(μ_α(r + C), 0) + r + C, μ_β(r + C))` for a constant `C ∈ ℕ` (depending on `α`, `β` and
the upstream systems). The additive `r` cannot be dropped in general (E6.2). -/
theorem rpow_certified {α β : ℝ} (hα : 0 < α) (bα : CertifiedBoundedTimeComputable d₁ α)
    (bβ : CertifiedBoundedTimeComputable d₂ β) :
    ∃ (C : ℕ) (btc : CertifiedBoundedTimeComputable (Fintype.card (PowIndex d₁ d₂)) (α ^ β)),
      btc.pivp = bα.pivp.powerSqCompile bβ.pivp ∧
      ∀ r : ℕ, btc.modulus r ≤
        max (max (bα.modulus (r + C)) 0 + r + C) (bβ.modulus (r + C)) := by
  set Px := bα.pivp
  set Py := bβ.pivp
  set Xt := bα.sol.trajectory
  set Yt := bβ.sol.trajectory
  have hXc : Continuous Xt := bα.trajectory_continuous
  have hYc : Continuous Yt := bβ.trajectory_continuous
  set x : ℝ → ℝ := fun t => Xt t Px.output with hx_def
  set y : ℝ → ℝ := fun t => Yt t Py.output with hy_def
  have hxc : Continuous x := (continuous_apply _).comp hXc
  have hyc : Continuous y := (continuous_apply _).comp hYc
  obtain ⟨Bx, hBx0, hBx⟩ := bα.bounded
  obtain ⟨By, hBy0, hBy⟩ := bβ.bounded
  have hxB : ∀ t, 0 ≤ t → |x t| ≤ Bx := fun t ht =>
    (by simpa using norm_le_pi_norm (Xt t) Px.output : |x t| ≤ ‖Xt t‖).trans (hBx t ht)
  have hyB : ∀ t, 0 ≤ t → |y t| ≤ By := fun t ht =>
    (by simpa using norm_le_pi_norm (Yt t) Py.output : |y t| ≤ ‖Yt t‖).trans (hBy t ht)
  set w := lowpassSq x with hw_def
  have hwpos : ∀ t, 0 ≤ t → 0 < w t := fun t ht => lowpassSq_pos x ht
  -- the filter estimate
  set G := Bx ^ 2 + α ^ 2
  set A₁ := |1 - α ^ 2| + G + (Bx + α)
  have hA₁ : 0 ≤ A₁ := by positivity
  have hGb : ∀ t, 0 ≤ t → ∀ s ∈ Set.Icc 0 t, |x s ^ 2 - α ^ 2| ≤ G := by
    intro t _ s hs
    have h1 := hxB s hs.1
    have h2 : x s ^ 2 ≤ Bx ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x s), sq_nonneg α]
  have hηb : ∀ ρ : ℕ, ∀ s, max (bα.modulus ρ) 0 ≤ s →
      |x s ^ 2 - α ^ 2| ≤ (Bx + α) * Real.exp (-(ρ : ℝ)) := by
    intro ρ s hs
    have h1 := abs_sub_le_of_modulus hxc bα.convergence ρ ((le_max_left _ _).trans hs)
    have h2 := hxB s ((le_max_right _ _).trans hs)
    have hf : x s ^ 2 - α ^ 2 = (x s - α) * (x s + α) := by ring
    rw [hf, abs_mul]
    have h3 : |x s + α| ≤ Bx + α := (abs_add_le _ _).trans (by rw [abs_of_pos hα]; linarith)
    calc |x s - α| * |x s + α| ≤ Real.exp (-(ρ : ℝ)) * (Bx + α) :=
          mul_le_mul h1 h3 (abs_nonneg _) (Real.exp_pos _).le
      _ = (Bx + α) * Real.exp (-(ρ : ℝ)) := mul_comm _ _
  have hE : ∀ ρ : ℕ, ∀ t, max (bα.modulus ρ) 0 + ρ ≤ t →
      |w t - α ^ 2| ≤ A₁ * Real.exp (-(ρ : ℝ)) := by
    intro ρ t ht
    set T := max (bα.modulus ρ) 0
    have hT : 0 ≤ T := le_max_right _ _
    have hρ : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
    have hTt : T ≤ t := by linarith
    have h := abs_lowpassSq_sub_le hxc hT hTt (hGb t (hT.trans hTt))
      (fun s hs => hηb ρ s hs.1)
    have hexp : Real.exp (-(t - T)) ≤ Real.exp (-(ρ : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    have hG0 : 0 ≤ |1 - α ^ 2| + G := by positivity
    calc |w t - α ^ 2| ≤ (|1 - α ^ 2| + G) * Real.exp (-(t - T)) +
          (Bx + α) * Real.exp (-(ρ : ℝ)) := h
      _ ≤ (|1 - α ^ 2| + G) * Real.exp (-(ρ : ℝ)) + (Bx + α) * Real.exp (-(ρ : ℝ)) := by
          gcongr
      _ = A₁ * Real.exp (-(ρ : ℝ)) := by ring
  -- uniform bounds on `w` (BAC2-PAPER §6.3 (a), (c))
  obtain ⟨ρ₀, hρ₀⟩ := exists_nat_mul_exp_neg_le hA₁ (by positivity : (0 : ℝ) < α ^ 2 / 2)
  set T₀ := max (bα.modulus ρ₀) 0 + ρ₀
  set wmin := min (α ^ 2 / 2) (Real.exp (-T₀))
  have hwmin : 0 < wmin := lt_min (by positivity) (Real.exp_pos _)
  have hwmin_le : ∀ t, 0 ≤ t → wmin ≤ w t := by
    intro t ht
    by_cases hT : T₀ ≤ t
    · have h := hE ρ₀ t hT
      have : α ^ 2 / 2 ≤ w t := by
        have := (abs_le.mp (h.trans hρ₀)).1
        linarith
      exact (min_le_left _ _).trans this
    · push_neg at hT
      refine (min_le_right _ _).trans ((Real.exp_le_exp.mpr ?_).trans
        (exp_neg_le_lowpassSq x ht))
      linarith
  have hα2 : wmin ≤ α ^ 2 := (min_le_left _ _).trans (by linarith [sq_nonneg α])
  set wmax := max 1 (Bx ^ 2)
  have hwmax : ∀ t, 0 ≤ t → w t ≤ wmax := fun t ht =>
    lowpassSq_le hxc ht (fun s hs => hxB s hs.1)
  set LU := |Real.log wmin| + |Real.log wmax|
  have hLU : ∀ t, 0 ≤ t → |Real.log (w t)| ≤ LU := by
    intro t ht
    have h1 : Real.log wmin ≤ Real.log (w t) := Real.log_le_log hwmin (hwmin_le t ht)
    have h2 : Real.log (w t) ≤ Real.log wmax := Real.log_le_log (hwpos t ht) (hwmax t ht)
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log wmin), abs_nonneg (Real.log wmax)]
    · linarith [le_abs_self (Real.log wmax), abs_nonneg (Real.log wmin)]
  -- the explicit solution
  set Z := powCurve Xt Yt Py.output w with hZ_def
  have hZ0 : ∀ k, Z 0 k = (powInit Px Py k : ℝ) := by
    intro k
    have hX0 : ∀ i, Xt 0 i = (Px.init i : ℝ) := fun i => by
      have := congrFun bα.sol.init_cond i; simpa using this
    have hY0 : ∀ j, Yt 0 j = (Py.init j : ℝ) := fun j => by
      have := congrFun bβ.sol.init_cond j; simpa using this
    rcases k with i | j | s
    · exact hX0 i
    · exact hY0 j
    · cases s <;> simp [hZ_def, powCurve, powInit, hw_def, lowpassSq_zero]
  have hZd : ∀ τ, 0 ≤ τ → ∀ k, HasDerivAt (fun σ => Z σ k)
      ((powField Px Py k).eval₂ (Rat.castHom ℝ) (Z τ)) τ := by
    intro τ hτ k
    have hw' := lowpassSq_hasDerivAt hxc τ
    have hw0 : w τ ≠ 0 := (hwpos τ hτ).ne'
    have hZX : (fun i => Z τ (Sum.inl i)) = Xt τ := rfl
    have hZY : (fun j => Z τ (Sum.inr (Sum.inl j))) = Yt τ := rfl
    have hx1 : (powX1RHS (d₂ := d₂) Px).eval₂ (Rat.castHom ℝ) (Z τ) = x τ ^ 2 - w τ := by
      simp only [powX1RHS, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one, hZ_def, powCurve]
      ring
    have hyd : HasDerivAt y (Py.evalField (Yt τ) Py.output) τ :=
      hasDerivAt_pi.mp (bβ.sol.is_solution τ hτ) Py.output
    have hHy : (rename (fun k => (Sum.inr (Sum.inl k) : PowIndex d₁ d₂))
        (Py.field Py.output)).eval₂ (Rat.castHom ℝ) (Z τ) = Py.evalField (Yt τ) Py.output := by
      rw [eval₂_rename]; rfl
    rcases k with i | j | s
    · show HasDerivAt (fun σ => Xt σ i)
        ((rename Sum.inl (Px.field i)).eval₂ (Rat.castHom ℝ) (Z τ)) τ
      rw [eval₂_rename]
      exact hasDerivAt_pi.mp (bα.sol.is_solution τ hτ) i
    · show HasDerivAt (fun σ => Yt σ j)
        ((rename (fun k => (Sum.inr (Sum.inl k) : PowIndex d₁ d₂)) (Py.field j)).eval₂
          (Rat.castHom ℝ) (Z τ)) τ
      rw [eval₂_rename]
      exact hasDerivAt_pi.mp (bβ.sol.is_solution τ hτ) j
    · cases s with
      | x1 =>
        show HasDerivAt (fun σ => w σ - 1) ((powX1RHS Px).eval₂ (Rat.castHom ℝ) (Z τ)) τ
        rw [hx1]
        exact hw'.sub_const 1
      | u =>
        show HasDerivAt (fun σ => Real.log (w σ))
          (((1 - X (Sum.inr (Sum.inr PowSlot.v))) * powX1RHS Px).eval₂ (Rat.castHom ℝ) (Z τ)) τ
        rw [eval₂_mul, hx1]
        refine (hw'.log hw0).congr_deriv ?_
        simp only [eval₂_sub, eval₂_one, eval₂_X, hZ_def, powCurve]
        ring
      | v =>
        show HasDerivAt (fun σ => 1 - 1 / w σ)
          (((1 - X (Sum.inr (Sum.inr PowSlot.v))) ^ 2 * powX1RHS Px).eval₂ (Rat.castHom ℝ)
            (Z τ)) τ
        rw [eval₂_mul, hx1]
        have h := (hw'.inv hw0).const_sub 1
        simp only [one_div]
        refine h.congr_deriv ?_
        simp only [eval₂_sub, eval₂_one, eval₂_X, eval₂_pow, hZ_def, powCurve]
        ring
      | z =>
        show HasDerivAt (fun σ => Real.exp (1 / 2 * Yt σ Py.output * Real.log (w σ)))
          ((C (1 / 2 : ℚ) * X (Sum.inr (Sum.inr PowSlot.z)) *
            (rename (fun k => (Sum.inr (Sum.inl k) : PowIndex d₁ d₂)) (Py.field Py.output) *
                X (Sum.inr (Sum.inr PowSlot.u)) +
              X (Sum.inr (Sum.inl Py.output)) * (1 - X (Sum.inr (Sum.inr PowSlot.v))) *
                powX1RHS Px)).eval₂ (Rat.castHom ℝ) (Z τ)) τ
        rw [eval₂_mul, eval₂_mul, eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, hHy, hx1]
        have hc : (Rat.castHom ℝ) (1 / 2 : ℚ) = (1 / 2 : ℝ) := by simp
        simp only [eval₂_C, eval₂_sub, eval₂_one, eval₂_X, hZ_def, powCurve, hc]
        have hR := ((hyd.const_mul (1 / 2 : ℝ)).fun_mul (hw'.log hw0)).exp
        refine hR.congr_deriv ?_
        simp only [hy_def]
        ring
  obtain ⟨sol', hsol'⟩ := PolyPIVP.ofIndexed_solution (powField Px Py) (powInit Px Py)
    (Sum.inr (Sum.inr PowSlot.z)) Z hZ0 hZd
  set e := Fintype.equivFin (PowIndex d₁ d₂)
  have hcoord : ∀ τ k, sol'.trajectory τ (e k) = Z τ k := by
    intro τ k; rw [hsol']; simp [e]
  have hout : ∀ τ, sol'.trajectory τ (bα.pivp.powerSqCompile bβ.pivp).output =
      Real.exp (1 / 2 * y τ * Real.log (w τ)) := fun τ => hcoord τ _
  -- boundedness (BAC2-PAPER §6.3 (d))
  set M := Bx + By + (wmax + 1) + LU + (1 + 1 / wmin) + Real.exp (1 / 2 * By * LU) + 1
  have hbd : (bα.pivp.powerSqCompile bβ.pivp).toPIVP.IsBounded sol'.trajectory := by
    have hLU0 : 0 ≤ LU := by positivity
    have hwmax0 : 0 ≤ wmax + 1 := by positivity
    have hv0 : 0 ≤ 1 + 1 / wmin := by positivity
    have hex0 := Real.exp_pos (1 / 2 * By * LU)
    refine ⟨M, by positivity, fun τ hτ => ?_⟩
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    obtain ⟨k, rfl⟩ := e.surjective j
    rw [hcoord τ k]
    rcases k with i | j | s
    · have : |Xt τ i| ≤ Bx :=
        (show |Xt τ i| ≤ ‖Xt τ‖ by simpa using norm_le_pi_norm (Xt τ) i).trans (hBx τ hτ)
      show |Xt τ i| ≤ M
      linarith
    · have : |Yt τ j| ≤ By :=
        (show |Yt τ j| ≤ ‖Yt τ‖ by simpa using norm_le_pi_norm (Yt τ) j).trans (hBy τ hτ)
      show |Yt τ j| ≤ M
      linarith
    · cases s with
      | x1 =>
        show |w τ - 1| ≤ M
        have h1 := hwpos τ hτ
        have h2 := hwmax τ hτ
        rw [abs_le]; constructor <;> linarith
      | u =>
        show |Real.log (w τ)| ≤ M
        have := hLU τ hτ
        linarith
      | v =>
        show |1 - 1 / w τ| ≤ M
        have h1 : 1 / w τ ≤ 1 / wmin := one_div_le_one_div_of_le hwmin (hwmin_le τ hτ)
        have h2 : 0 < 1 / w τ := one_div_pos.mpr (hwpos τ hτ)
        rw [abs_le]; constructor <;> linarith
      | z =>
        show |Real.exp (1 / 2 * Yt τ Py.output * Real.log (w τ))| ≤ M
        rw [abs_of_pos (Real.exp_pos _)]
        have hR : 1 / 2 * Yt τ Py.output * Real.log (w τ) ≤ 1 / 2 * By * LU := by
          have h1 := hyB τ hτ
          have h2 := hLU τ hτ
          calc 1 / 2 * Yt τ Py.output * Real.log (w τ)
              ≤ |1 / 2 * Yt τ Py.output * Real.log (w τ)| := le_abs_self _
            _ = 1 / 2 * (|y τ| * |Real.log (w τ)|) := by
                rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; ring
            _ ≤ 1 / 2 * (By * LU) := by gcongr
            _ = 1 / 2 * By * LU := by ring
        have := Real.exp_le_exp.mpr hR
        linarith
  -- the modulus (BAC2-PAPER §6.4)
  set LR := max (1 / 2 * By * LU) |Real.log α * β|
  set A := Real.exp LR * (1 / 2 * By * A₁ / wmin + |Real.log α|)
  have hA : 0 ≤ A := by positivity
  obtain ⟨C, hC⟩ := exists_nat_gt (Real.log (A + 1))
  have hAC : A * Real.exp (-(C : ℝ)) < 1 := by
    have h1 : Real.exp (-(C : ℝ)) < 1 / (A + 1) := by
      have : Real.exp (-(C : ℝ)) < Real.exp (-Real.log (A + 1)) :=
        Real.exp_lt_exp.mpr (by linarith)
      have he : Real.exp (-Real.log (A + 1)) = 1 / (A + 1) := by
        rw [Real.exp_neg, Real.exp_log (by linarith), one_div]
      rwa [he] at this
    calc A * Real.exp (-(C : ℝ)) ≤ A * (1 / (A + 1)) :=
          mul_le_mul_of_nonneg_left h1.le hA
      _ < 1 := by rw [mul_one_div, div_lt_one (by linarith)]; linarith
  set μ : TimeModulus := fun r =>
    max (max (bα.modulus (r + C)) 0 + r + C) (bβ.modulus (r + C))
  have hconv : ∀ r : ℕ, ∀ t : ℝ, t > μ r →
      |sol'.trajectory t (bα.pivp.powerSqCompile bβ.pivp).output - α ^ β| <
        Real.exp (-(r : ℝ)) := by
    intro r t ht
    set ρ := r + C
    have hρ : ((ρ : ℕ) : ℝ) = (r : ℝ) + C := by push_cast [ρ]; ring
    have ht1 : max (bα.modulus ρ) 0 + ρ ≤ t := by
      have := (le_max_left _ _).trans_lt ht
      rw [hρ]; linarith
    have ht2 : t > bβ.modulus ρ := (le_max_right _ _).trans_lt ht
    have ht0 : 0 ≤ t := by
      have : (0 : ℝ) ≤ max (bα.modulus ρ) 0 + ρ := by positivity
      linarith
    have hw := hE ρ t ht1
    have hwα : |Real.log (w t) - 2 * Real.log α| ≤ A₁ * Real.exp (-(ρ : ℝ)) / wmin := by
      have hlog2 : Real.log (α ^ 2) = 2 * Real.log α := by
        rw [Real.log_pow]; push_cast; ring
      rw [← hlog2]
      exact (DualRail.Power.abs_log_sub_log_le_div hwmin (hwmin_le t ht0) hα2).trans
        (div_le_div_of_nonneg_right hw hwmin.le)
    have hyβ : |y t - β| < Real.exp (-(ρ : ℝ)) := bβ.convergence ρ t ht2
    have hRR : |1 / 2 * y t * Real.log (w t) - Real.log α * β| ≤
        (1 / 2 * By * A₁ / wmin + |Real.log α|) * Real.exp (-(ρ : ℝ)) := by
      have hid : 1 / 2 * y t * Real.log (w t) - Real.log α * β =
          1 / 2 * y t * (Real.log (w t) - 2 * Real.log α) + (y t - β) * Real.log α := by ring
      rw [hid]
      have h1 : |1 / 2 * y t * (Real.log (w t) - 2 * Real.log α)| ≤
          1 / 2 * By * (A₁ * Real.exp (-(ρ : ℝ)) / wmin) := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        gcongr
        exact hyB t ht0
      have h2 : |(y t - β) * Real.log α| ≤ Real.exp (-(ρ : ℝ)) * |Real.log α| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hyβ.le (abs_nonneg _)
      calc _ ≤ |1 / 2 * y t * (Real.log (w t) - 2 * Real.log α)| +
            |(y t - β) * Real.log α| := abs_add_le _ _
        _ ≤ 1 / 2 * By * (A₁ * Real.exp (-(ρ : ℝ)) / wmin) +
            Real.exp (-(ρ : ℝ)) * |Real.log α| := add_le_add h1 h2
        _ = (1 / 2 * By * A₁ / wmin + |Real.log α|) * Real.exp (-(ρ : ℝ)) := by ring
    have hR1 : 1 / 2 * y t * Real.log (w t) ≤ LR := by
      refine le_trans ?_ (le_max_left _ _)
      calc 1 / 2 * y t * Real.log (w t) ≤ |1 / 2 * y t * Real.log (w t)| := le_abs_self _
        _ = 1 / 2 * (|y t| * |Real.log (w t)|) := by
            rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; ring
        _ ≤ 1 / 2 * (By * LU) := by gcongr; exacts [hyB t ht0, hLU t ht0]
        _ = 1 / 2 * By * LU := by ring
    have hR2 : Real.log α * β ≤ LR := (le_abs_self _).trans (le_max_right _ _)
    rw [hout t, Real.rpow_def_of_pos hα]
    calc |Real.exp (1 / 2 * y t * Real.log (w t)) - Real.exp (Real.log α * β)|
        ≤ Real.exp LR * |1 / 2 * y t * Real.log (w t) - Real.log α * β| :=
          DualRail.Power.abs_exp_sub_exp_le_mul hR1 hR2
      _ ≤ Real.exp LR * ((1 / 2 * By * A₁ / wmin + |Real.log α|) * Real.exp (-(ρ : ℝ))) :=
          mul_le_mul_of_nonneg_left hRR (Real.exp_pos _).le
      _ = A * Real.exp (-(C : ℝ)) * Real.exp (-(r : ℝ)) := by
          rw [hρ, neg_add, Real.exp_add]; ring
      _ < 1 * Real.exp (-(r : ℝ)) := by gcongr
      _ = Real.exp (-(r : ℝ)) := one_mul _
  obtain ⟨btc, hbtc, hmod, -⟩ :=
    CertifiedBoundedTimeComputable.exists_of_solution _ sol' hbd μ hconv
  refine ⟨C, btc, hbtc, fun r => ?_⟩
  rw [hmod r]
  refine max_le ?_ le_rfl
  refine le_trans ?_ (le_max_left _ _)
  have : (0 : ℝ) ≤ max (bα.modulus (r + C)) 0 := le_max_right _ _
  positivity

/-- [BAC] Thm 6.1 (journal draft `thm:power`): bounded GPACs are closed under `α^β`
(`α > 0`, `β ∈ ℝ`). -/
theorem isCRNComputable_rpow {α β : ℝ} (hα : 0 < α) (ha : IsCRNComputable α)
    (hb : IsCRNComputable β) : IsCRNComputable (α ^ β) := by
  obtain ⟨d₁, ⟨bα⟩⟩ := ha
  obtain ⟨d₂, ⟨bβ⟩⟩ := hb
  obtain ⟨-, btc, -, -⟩ := rpow_certified hα bα bβ
  exact ⟨_, ⟨btc⟩⟩

/-- [BAC] Thm 6.4 (journal draft `thm:power-complexity`), "exponentiation preserves the time
complexity class", for the polynomial classes: if `α > 0` and `β` are computable in time
`O((r+1)^n)` with `n ≥ 1`, so is `α^β`. (The corrected modulus of `rpow_certified` adds `r + C`,
which is absorbed for `n ≥ 1`.) -/
theorem isPolyTimeComputable_rpow {α β : ℝ} {n : ℕ} (hn : 1 ≤ n) (hα : 0 < α)
    (ha : IsPolyTimeComputable α n) (hb : IsPolyTimeComputable β n) :
    IsPolyTimeComputable (α ^ β) n := by
  obtain ⟨d₁, bα, Ka, hKa, hμa⟩ := ha
  obtain ⟨d₂, bβ, Kb, hKb, hμb⟩ := hb
  obtain ⟨C, btc, -, hmod⟩ := rpow_certified hα bα bβ
  refine ⟨_, btc, (Ka + Kb) * ((C : ℝ) + 1) ^ n + ((C : ℝ) + 1), by positivity, fun r => ?_⟩
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  have hshift : (((r + C : ℕ) : ℝ) + 1) ^ n ≤ ((C : ℝ) + 1) ^ n * ((r : ℝ) + 1) ^ n := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    push_cast
    nlinarith
  have hlin : (r : ℝ) + C ≤ ((C : ℝ) + 1) * ((r : ℝ) + 1) ^ n := by
    have : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ n := le_self_pow₀ hr1 (by omega)
    nlinarith
  have hpow0 : (0 : ℝ) ≤ ((r : ℝ) + 1) ^ n := by positivity
  have hCn : (0 : ℝ) ≤ ((C : ℝ) + 1) ^ n := by positivity
  refine (hmod r).trans (max_le ?_ ?_)
  · have h1 : max (bα.modulus (r + C)) 0 ≤ Ka * (((C : ℝ) + 1) ^ n * ((r : ℝ) + 1) ^ n) :=
      max_le ((hμa (r + C)).trans (mul_le_mul_of_nonneg_left hshift hKa.le)) (by positivity)
    have h2 : Kb * (((C : ℝ) + 1) ^ n * ((r : ℝ) + 1) ^ n) ≥ 0 := by positivity
    calc max (bα.modulus (r + C)) 0 + r + C
        ≤ Ka * (((C : ℝ) + 1) ^ n * ((r : ℝ) + 1) ^ n) + ((C : ℝ) + 1) * ((r : ℝ) + 1) ^ n := by
          linarith
      _ ≤ ((Ka + Kb) * ((C : ℝ) + 1) ^ n + ((C : ℝ) + 1)) * ((r : ℝ) + 1) ^ n := by nlinarith
  · calc bβ.modulus (r + C) ≤ Kb * (((r + C : ℕ) : ℝ) + 1) ^ n := hμb (r + C)
      _ ≤ Kb * (((C : ℝ) + 1) ^ n * ((r : ℝ) + 1) ^ n) :=
          mul_le_mul_of_nonneg_left hshift hKb.le
      _ ≤ ((Ka + Kb) * ((C : ℝ) + 1) ^ n + ((C : ℝ) + 1)) * ((r : ℝ) + 1) ^ n := by
          have : 0 ≤ Ka * (((C : ℝ) + 1) ^ n * ((r : ℝ) + 1) ^ n) := by positivity
          nlinarith

/-- Non-vacuity of `isPolyTimeComputable_rpow` (and of `rpow_certified`): `2^{1/2} = √2` is
computed in real time (`n = 1`) by the repaired construction applied to two constant systems.
This is the instance of erratum E6.2: here the corrected modulus has the additive `r`. -/
theorem sqrt_two_rpow_polyTime : IsPolyTimeComputable ((2 : ℝ) ^ (1 / 2 : ℝ)) 1 := by
  have hc : ∀ q : ℚ, IsPolyTimeComputable (q : ℝ) 1 := fun q => by
    obtain ⟨d, btc, C, hC, h⟩ := realtime_rat_const q
    exact ⟨d, btc, C, hC, fun r => by simpa using h r⟩
  have h := isPolyTimeComputable_rpow le_rfl (by norm_num : (0 : ℝ) < ((2 : ℚ) : ℝ)) (hc 2)
    (hc (1 / 2))
  have e : ((2 : ℚ) : ℝ) ^ (((1 / 2 : ℚ)) : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by norm_num
  rwa [e] at h

end Ripple

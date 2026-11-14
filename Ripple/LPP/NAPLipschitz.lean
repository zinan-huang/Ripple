/-
  Ripple.LPP.NAPLipschitz — the balance field of a weighted protocol is Lipschitz on every ball,
  with an explicit constant; hence Proposition 4.2 of the PP-to-NAP write-up holds without a
  Lipschitz hypothesis (and without an a-priori bound on the competing solution).

  * `balanceLip w R = 2 R Σ_sh Σ_α |w sh| |net sh α|`;
  * `balanceFun_lipschitzOnWith`: `balanceFun w` is `balanceLip w R`-Lipschitz on `closedBall 0 R`
    (sup norm), by `|ab − a'b'| ≤ |a||b − b'| + |a − a'||b'| ≤ 2 R ‖v − v'‖`;
  * `lifted_solution_eq'`: `lifted_solution_eq` without `hlip`;
  * `lifted_solution_unique`: also without the bound `‖u t‖ ≤ M` (a continuous `u` is bounded on
    the compact `[0,T]`) and without `0 < T`.
-/

import Ripple.LPP.NAPConjugacy

namespace Ripple
namespace NAPTransport

open Set Filter Topology Finset

variable (n : ℕ)

/-- Explicit Lipschitz constant of `balanceFun w` on the closed ball of radius `R`. -/
noncomputable def balanceLip (w : WProtocol (MI n 3)) (R : ℝ) : ℝ :=
  2 * R * ∑ sh, ∑ α, |(w sh : ℝ)| * |(net sh α : ℝ)|

theorem abs_mul_sub_mul_le {a b a' b' R d : ℝ} (ha : |a| ≤ R) (hb' : |b'| ≤ R)
    (hda : |a - a'| ≤ d) (hdb : |b - b'| ≤ d) : |a * b - a' * b'| ≤ 2 * R * d := by
  have hR : 0 ≤ R := le_trans (abs_nonneg _) ha
  have hd : 0 ≤ d := le_trans (abs_nonneg _) hda
  have e : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [e]
  calc |a * (b - b') + (a - a') * b'| ≤ |a * (b - b')| + |(a - a') * b'| := abs_add_le _ _
    _ = |a| * |b - b'| + |a - a'| * |b'| := by rw [abs_mul, abs_mul]
    _ ≤ R * d + d * R :=
        add_le_add (mul_le_mul ha hdb (abs_nonneg _) hR) (mul_le_mul hda hb' (abs_nonneg _) hd)
    _ = 2 * R * d := by ring

theorem balanceLip_nonneg (w : WProtocol (MI n 3)) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ balanceLip n w R := by
  unfold balanceLip
  apply mul_nonneg (by linarith)
  exact Finset.sum_nonneg fun sh _ => Finset.sum_nonneg fun α _ =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- **Lipschitz bound.** The balance field of any weighted protocol is Lipschitz on the closed
ball of radius `R` (sup norm) with constant `balanceLip w R`. -/
theorem balanceFun_lipschitzOnWith (w : WProtocol (MI n 3)) (R : ℝ) :
    LipschitzOnWith (Real.toNNReal (balanceLip n w R)) (balanceFun n w)
      (Metric.closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv v' hv'
  rw [Metric.mem_closedBall, dist_zero_right] at hv hv'
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hv
  have hK : 0 ≤ balanceLip n w R := balanceLip_nonneg n w hR
  rw [Real.coe_toNNReal _ hK]
  have hd : 0 ≤ dist v v' := dist_nonneg
  have hcv : ∀ a, |v a| ≤ R := fun a => by
    have := norm_le_pi_norm v a
    rw [Real.norm_eq_abs] at this
    linarith
  have hcv' : ∀ a, |v' a| ≤ R := fun a => by
    have := norm_le_pi_norm v' a
    rw [Real.norm_eq_abs] at this
    linarith
  have hdc : ∀ a, |v a - v' a| ≤ dist v v' := fun a => by
    have := dist_le_pi_dist v v' a
    rwa [Real.dist_eq] at this
  rw [dist_pi_le_iff (mul_nonneg hK hd)]
  intro α
  rw [Real.dist_eq]
  unfold balanceFun
  rw [← Finset.sum_sub_distrib]
  calc |∑ sh, ((w sh : ℝ) * v sh.1 * v sh.2.1 * (net sh α : ℝ)
          - (w sh : ℝ) * v' sh.1 * v' sh.2.1 * (net sh α : ℝ))|
      ≤ ∑ sh, |(w sh : ℝ) * v sh.1 * v sh.2.1 * (net sh α : ℝ)
          - (w sh : ℝ) * v' sh.1 * v' sh.2.1 * (net sh α : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ sh, |(w sh : ℝ)| * |(net sh α : ℝ)| * (2 * R * dist v v') := by
        apply Finset.sum_le_sum
        intro sh _
        have e : (w sh : ℝ) * v sh.1 * v sh.2.1 * (net sh α : ℝ)
            - (w sh : ℝ) * v' sh.1 * v' sh.2.1 * (net sh α : ℝ)
            = ((w sh : ℝ) * (net sh α : ℝ)) * (v sh.1 * v sh.2.1 - v' sh.1 * v' sh.2.1) := by
          ring
        rw [e, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left
          (abs_mul_sub_mul_le (hcv _) (hcv' _) (hdc _) (hdc _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ ∑ sh, (∑ α', |(w sh : ℝ)| * |(net sh α' : ℝ)|) * (2 * R * dist v v') := by
        apply Finset.sum_le_sum
        intro sh _
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Finset.single_le_sum (f := fun α' => |(w sh : ℝ)| * |(net sh α' : ℝ)|)
          (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ α)
    _ = balanceLip n w R * dist v v' := by
        unfold balanceLip
        rw [← Finset.sum_mul]
        ring

/-- **Proposition 4.2 without a Lipschitz hypothesis.** `lifted_solution_eq` with `hlip`
discharged by `balanceFun_lipschitzOnWith`. -/
theorem lifted_solution_eq' (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hr : Realizes (veroneseLift n 3) w (demand n f))
    {T M : ℝ} (hT : 0 < T)
    {z : ℝ → Fin n → ℝ}
    (hz : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt z (fieldFun n f (z t)) (Icc 0 T) t)
    (hzb : ∀ t ∈ Icc (0 : ℝ) T, ‖z t‖ ≤ 1)
    {u : ℝ → MI n 3 → ℝ}
    (hu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (balanceFun n w (u t)) (Icc 0 T) t)
    (hub : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ M)
    (hu0 : u 0 = fun α => ver n (z 0) α) :
    EqOn u (fun t α => ver n (z t) α) (Icc 0 T) :=
  lifted_solution_eq n f w hr (K := balanceLip n w (max M 6)) hT
    (balanceFun_lipschitzOnWith n w _) hz hzb hu hub hu0

/-- **Proposition 4.2, uniqueness form.** Let `w` realise `demand f` and `z` solve the quartic
field on `[0,T]` inside the unit ball. Then every solution `u` of the lifted field `balanceFun w` on
`[0,T]` with `u 0 = ver (z 0)` equals `ver ∘ z` on `[0,T]`. No Lipschitz hypothesis, no a-priori
bound on `u`, and no sign condition on `T` are needed. -/
theorem lifted_solution_unique (f : QuarticPP n) (w : WProtocol (MI n 3))
    (hr : Realizes (veroneseLift n 3) w (demand n f))
    {T : ℝ} {z : ℝ → Fin n → ℝ}
    (hz : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt z (fieldFun n f (z t)) (Icc 0 T) t)
    (hzb : ∀ t ∈ Icc (0 : ℝ) T, ‖z t‖ ≤ 1)
    {u : ℝ → MI n 3 → ℝ}
    (hu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt u (balanceFun n w (u t)) (Icc 0 T) t)
    (hu0 : u 0 = fun α => ver n (z 0) α) :
    EqOn u (fun t α => ver n (z t) α) (Icc 0 T) := by
  rcases lt_or_ge 0 T with hT | hT
  · have hcont : ContinuousOn u (Icc 0 T) := fun t ht => (hu t ht).continuousWithinAt
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    exact lifted_solution_eq' n f w hr hT hz hzb hu hM hu0
  · intro t ht
    have : t = 0 := le_antisymm (le_trans ht.2 hT) ht.1
    subst this
    exact hu0

end NAPTransport
end Ripple

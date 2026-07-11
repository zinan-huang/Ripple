/-
Ripple.BoundedUniversality.GPAC.ExplicitCompile
-----------------------------
Explicit construction of the compiled trajectory without ODE existence.

Key insight: the compiled trajectory is NOT obtained by solving the
compiled ODE. It is DEFINED algebraically:
- z̄_j(τ) = z_j(s(τ))  (time-reparameterized original variables)
- U_{N,m}(τ) = f(s(τ))^m / (1 + f(s(τ))^N)  (surrogates)

where s(τ) = ∫₀ᵗ 1/(1+f(s(u))^N) du is the time change.

The compiled ODE is then VERIFIED (not solved) for this explicit
trajectory using the chain rule + quotient rule.

Boundedness is AUTOMATIC: surrogates are bounded by algebraic identity
(surrogate_bounded), not by ODE invariance.
-/

import Ripple.BoundedUniversality.GPAC.SurrogateCompile
import Ripple.BoundedUniversality.GPAC.TimeChange
import Ripple.BoundedUniversality.GPAC.TimeChangeConstruct

namespace Ripple.BoundedUniversality.GPAC

open Ripple

/-- The surrogate function U_{N,m}(f) = f^m / (1 + f^N).
Bounded in [0,1] for f ≥ 0 by surrogate_bounded. -/
noncomputable def surrogateFunc (N m : ℕ) (f : ℝ) : ℝ :=
  boundedSurrogate N m f

/-- The explicit compiled trajectory: original vars via time change,
surrogates via algebraic definition. -/
noncomputable def explicitCompiledTraj
    {n : ℕ} (z : ℝ → Fin (n + 1) → ℝ) (s : ℝ → ℝ) (N : ℕ)
    (τ : ℝ) : Fin (n + N + 1) → ℝ :=
  fun j =>
    if hj : (j : ℕ) < n then
      z (s τ) ⟨j, by omega⟩
    else
      let m := (j : ℕ) - n
      surrogateFunc N m (z (s τ) ⟨n, by omega⟩)

/-- Surrogates in the explicit trajectory are bounded in [0,1]. -/
theorem explicitCompiledTraj_surrogates_bounded
    {n : ℕ} (z : ℝ → Fin (n + 1) → ℝ) (s : ℝ → ℝ) (N : ℕ)
    (hN : 1 ≤ N) (hf_nn : ∀ τ, 0 ≤ z (s τ) ⟨n, by omega⟩)
    (τ : ℝ) (j : Fin (n + N + 1)) (hj : ¬ ((j : ℕ) < n)) :
    0 ≤ explicitCompiledTraj z s N τ j ∧
    explicitCompiledTraj z s N τ j ≤ 1 := by
  simp only [explicitCompiledTraj, hj, ite_false]
  let m := (j : ℕ) - n
  have hm : m ≤ N := by omega
  exact surrogate_bounded N m hN hm (z (s τ) ⟨n, by omega⟩) (hf_nn τ)

/-- The arc-length-like function L(t) = ∫₀ᵗ (1 + z_n(u)^N) du.
L is strictly increasing (integrand > 0) and continuous.
The time change s = L⁻¹ satisfies s' = 1/(1+z_n(s)^N). -/
noncomputable def arcLengthFunc (z_n : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, (1 + z_n u ^ N)

/-- L is strictly increasing because the integrand is positive. -/
private theorem arcLength_integrand_cont (z_n : ℝ → ℝ) (hz_cont : Continuous z_n) (N : ℕ) :
    Continuous (fun u => 1 + z_n u ^ N) :=
  continuous_const.add (hz_cont.pow N)

private theorem arcLength_integrand_pos (z_n : ℝ → ℝ) (N : ℕ) (hN_even : Even N) :
    ∀ u, 0 < 1 + z_n u ^ N :=
  fun u => by linarith [Even.pow_nonneg hN_even (z_n u)]

private theorem arcLength_eq_timeChangeIntegral (z_n : ℝ → ℝ) (N : ℕ) :
    arcLengthFunc z_n N = timeChangeIntegral (fun u => 1 + z_n u ^ N) := rfl

theorem arcLengthFunc_strictMono
    (z_n : ℝ → ℝ) (hz_cont : Continuous z_n) (N : ℕ) (hN_even : Even N) :
    StrictMono (arcLengthFunc z_n N) := by
  rw [arcLength_eq_timeChangeIntegral]
  exact timeChangeIntegral_strictMono _
    (arcLength_integrand_cont z_n hz_cont N)
    (arcLength_integrand_pos z_n N hN_even)

theorem arcLengthFunc_hasDerivAt
    (z_n : ℝ → ℝ) (hz_cont : Continuous z_n) (N : ℕ) (τ : ℝ) :
    HasDerivAt (arcLengthFunc z_n N) (1 + z_n τ ^ N) τ := by
  rw [arcLength_eq_timeChangeIntegral]
  exact timeChangeIntegral_hasDerivAt _ (arcLength_integrand_cont z_n hz_cont N) τ

theorem arcLengthFunc_continuous
    (z_n : ℝ → ℝ) (hz_cont : Continuous z_n) (N : ℕ) :
    Continuous (arcLengthFunc z_n N) :=
  (Differentiable.continuous fun τ =>
    (arcLengthFunc_hasDerivAt z_n hz_cont N τ).differentiableAt)

theorem arcLengthFunc_zero (z_n : ℝ → ℝ) (N : ℕ) :
    arcLengthFunc z_n N 0 = 0 := by
  simp [arcLengthFunc, intervalIntegral.integral_same]

theorem arcLengthFunc_tendsto
    (z_n : ℝ → ℝ) (hz_cont : Continuous z_n) (N : ℕ) (hN_even : Even N) :
    Filter.Tendsto (arcLengthFunc z_n N) Filter.atTop Filter.atTop := by
  rw [arcLength_eq_timeChangeIntegral]
  exact timeChangeIntegral_tendsto _
    (arcLength_integrand_cont z_n hz_cont N)
    1 one_pos (fun t => by linarith [Even.pow_nonneg hN_even (z_n t)])

/-- The time change s is the inverse of L. Since L is continuous,
strictly increasing, and L → ∞, the inverse exists on [0, ∞) and
is also continuous and strictly increasing.

s(τ) = L⁻¹(τ) satisfies L(s(τ)) = τ, so by differentiating:
L'(s(τ)) · s'(τ) = 1, giving s'(τ) = 1/L'(s(τ)) = 1/(1+z_n(s(τ))^N). -/
-- s = L⁻¹ defined as Function.invFun (choosing a preimage for each τ)
noncomputable def arcLengthInv (z_n : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
  Function.invFun (arcLengthFunc z_n N)

-- For the time change, we only need surjectivity onto [0, ∞).
-- L(0)=0, L continuous, L → +∞, and L strictly increasing give this via IVT.
theorem arcLengthFunc_surjective_nonneg
    (z_n : ℝ → ℝ) (hz_cont : Continuous z_n) (N : ℕ) (hN_even : Even N)
    (y : ℝ) (hy : 0 ≤ y) :
    ∃ t, 0 ≤ t ∧ arcLengthFunc z_n N t = y := by
  obtain ⟨R₀, hR₀⟩ := (Filter.tendsto_atTop_atTop.mp
    (arcLengthFunc_tendsto z_n hz_cont N hN_even)) y
  let R := max R₀ 0
  have hR0 : 0 ≤ R := le_max_right R₀ 0
  have hLR : y ≤ arcLengthFunc z_n N R := hR₀ R (le_max_left R₀ 0)
  have hL0 : arcLengthFunc z_n N 0 ≤ y := by rw [arcLengthFunc_zero]; exact hy
  obtain ⟨t, ⟨ht0, _⟩, htL⟩ := intermediate_value_Icc hR0
    (arcLengthFunc_continuous z_n hz_cont N).continuousOn ⟨hL0, hLR⟩
  exact ⟨t, ht0, htL⟩

theorem timeChange_via_inverse
    (z_n : ℝ → ℝ) (hz_cont : Continuous z_n)
    (N : ℕ) (hN_even : Even N) (hN_pos : 0 < N) :
    ∃ s : ℝ → ℝ,
      s 0 = 0 ∧
      (∀ τ : ℝ, 0 ≤ τ → HasDerivAt s ((1 + z_n (s τ) ^ N)⁻¹) τ) ∧
      Continuous s ∧
      StrictMono s ∧
      Filter.Tendsto s Filter.atTop Filter.atTop := by
  classical
  let L : ℝ → ℝ := arcLengthFunc z_n N
  have hL0 : L 0 = 0 := by simpa [L] using arcLengthFunc_zero z_n N
  have hLderiv : ∀ x : ℝ, HasDerivAt L (1 + z_n x ^ N) x := by
    intro x; simpa [L] using arcLengthFunc_hasDerivAt z_n hz_cont N x
  have hLmono : StrictMono L := by
    simpa [L] using arcLengthFunc_strictMono z_n hz_cont N hN_even
  have hLcont : Continuous L := by
    simpa [L] using arcLengthFunc_continuous z_n hz_cont N
  have hge_one : ∀ u : ℝ, (1 : ℝ) ≤ 1 + z_n u ^ N := by
    intro u
    have hpow_nonneg : 0 ≤ z_n u ^ N := by
      rcases hN_even with ⟨k, rfl⟩
      simpa [pow_add] using mul_self_nonneg (z_n u ^ k)
    linarith
  have hpos : ∀ u : ℝ, 0 < 1 + z_n u ^ N :=
    fun u => lt_of_lt_of_le zero_lt_one (hge_one u)
  have hL_le_id_of_nonpos : ∀ t : ℝ, t ≤ 0 → L t ≤ t := by
    intro t ht
    have hf_cont : Continuous fun u : ℝ => (1 : ℝ) + z_n u ^ N :=
      continuous_const.add (hz_cont.pow N)
    have hmono_int :
        (∫ u in t..0, (1 : ℝ)) ≤ ∫ u in t..0, (1 + z_n u ^ N) :=
      intervalIntegral.integral_mono_on ht
        ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).intervalIntegrable t 0)
        (hf_cont.intervalIntegrable t 0)
        (fun u _ => hge_one u)
    have hsymm : L t = - ∫ u in t..0, (1 + z_n u ^ N) := by
      dsimp [L, arcLengthFunc]
      rw [intervalIntegral.integral_symm]
    calc L t = - ∫ u in t..0, (1 + z_n u ^ N) := hsymm
      _ ≤ - ∫ u in t..0, (1 : ℝ) := by linarith
      _ = t := by simp
  have hsurj : Function.Surjective L := by
    intro y
    by_cases hy : 0 ≤ y
    · rcases arcLengthFunc_surjective_nonneg z_n hz_cont N hN_even y hy
        with ⟨t, _, ht_eq⟩
      exact ⟨t, by simpa [L] using ht_eq⟩
    · have hylt : y < 0 := lt_of_not_ge hy
      let a : ℝ := y - 1
      have ha0 : a ≤ 0 := by dsimp [a]; linarith
      have hLa_le_y : L a ≤ y := by
        dsimp [a] at *; linarith [hL_le_id_of_nonpos a ha0]
      have hy_le_L0 : y ≤ L 0 := by linarith [hL0]
      obtain ⟨x, _, hx⟩ := intermediate_value_Icc ha0
        hLcont.continuousOn ⟨hLa_le_y, hy_le_L0⟩
      exact ⟨x, hx⟩
  let s : ℝ → ℝ := Function.invFun L
  have hs_inv : ∀ y : ℝ, L (s y) = y :=
    fun y => Function.invFun_eq (hsurj y)
  have hs0 : s 0 = 0 := by
    apply hLmono.injective; simpa [hL0] using hs_inv 0
  have hs_strict : StrictMono s := by
    intro a b hab; by_contra h; push_neg at h
    linarith [hLmono.monotone h, hs_inv a, hs_inv b]
  have hs_cont : Continuous s := by
    let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective L hLmono hsurj
    have hLe_symm : ∀ y, L (e.symm y) = y := by
      intro y
      have : e (e.symm y) = y := e.apply_symm_apply y
      show L (e.symm y) = y
      change (e (e.symm y) : ℝ) = y
      simp [this]
    have hs_eq_e : s = e.symm := by
      funext y; apply hLmono.injective
      exact (hs_inv y).trans (hLe_symm y).symm
    rw [hs_eq_e]; exact e.symm.continuous
  have hs_tendsto : Filter.Tendsto s Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop (L b)] with y hy
    by_contra hnot
    exact not_lt_of_ge (show L b ≤ L (s y) by simpa [hs_inv y] using hy)
      (hLmono (lt_of_not_ge hnot))
  refine ⟨s, hs0, ?_, hs_cont, hs_strict, hs_tendsto⟩
  intro τ hτ
  exact HasDerivAt.of_local_left_inverse
    hs_cont.continuousAt
    (hLderiv (s τ))
    (ne_of_gt (hpos (s τ)))
    (Filter.Eventually.of_forall hs_inv)

end Ripple.BoundedUniversality.GPAC

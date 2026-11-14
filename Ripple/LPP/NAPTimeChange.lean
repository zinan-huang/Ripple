/-
  Ripple.LPP.NAPTimeChange — the r²-trick is a time change (Proposition 4.1 of
  the PP-to-NAP write-up), with the time change constructed explicitly.

  Let `y : ℝ → E` be a trajectory with `y' = g (y t)` for `t > 0`, and `ρ : E → ℝ` a slack
  coordinate with `0 < ρ (y t) ≤ 1` for `t ≥ 0`. Put `φ σ = ρ (y (max σ 0))⁻² ≥ 1` and
  `T τ = ∫₀^τ φ`. `T` is a strictly increasing continuous bijection `ℝ → ℝ` (an order
  isomorphism `Tiso`), and `τ := T⁻¹` satisfies `τ 0 = 0`, `τ t > 0` for `t > 0`,
  `τ' t = ρ (y (τ t))²`, `τ → ∞`. Hence `z = y ∘ τ` solves `z' = ρ(z)² • g z` from `z 0 = y 0`
  (`timeChange_hasDerivAt`), and every readout limit of `y` is a readout limit of `z`
  (`timeChange_readout_tendsto`).
-/

import Ripple.LPP.NAPProtocol
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue

namespace Ripple
namespace NAPTimeChange

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The data of a slack coordinate along a trajectory. -/
structure SlackData (y : ℝ → E) (ρ : E → ℝ) : Prop where
  cont : Continuous y
  ρcont : Continuous ρ
  pos : ∀ t, 0 ≤ t → 0 < ρ (y t)
  le_one : ∀ t, 0 ≤ t → ρ (y t) ≤ 1

variable (y : ℝ → E) (ρ : E → ℝ)

/-- The integrand `ρ(y(max σ 0))⁻²`. -/
noncomputable def phi (σ : ℝ) : ℝ := (ρ (y (max σ 0)))⁻¹ ^ 2

/-- The clock `T τ = ∫₀^τ φ`. -/
noncomputable def Tfun (τ : ℝ) : ℝ := ∫ σ in (0 : ℝ)..τ, phi y ρ σ

variable {y ρ}

theorem phi_cont (h : SlackData y ρ) : Continuous (phi y ρ) := by
  have hmax : Continuous fun σ : ℝ => max σ 0 := continuous_id.max continuous_const
  have hρy : Continuous fun σ : ℝ => ρ (y (max σ 0)) := h.ρcont.comp (h.cont.comp hmax)
  have hne : ∀ σ : ℝ, ρ (y (max σ 0)) ≠ 0 := fun σ => (h.pos _ (le_max_right _ _)).ne'
  exact (hρy.inv₀ hne).pow 2

theorem phi_ge_one (h : SlackData y ρ) (σ : ℝ) : 1 ≤ phi y ρ σ := by
  unfold phi
  have hp := h.pos (max σ 0) (le_max_right _ _)
  have hl := h.le_one (max σ 0) (le_max_right _ _)
  have h1 : 1 ≤ (ρ (y (max σ 0)))⁻¹ := (one_le_inv₀ hp).mpr hl
  exact one_le_pow₀ h1

theorem phi_pos (h : SlackData y ρ) (σ : ℝ) : 0 < phi y ρ σ :=
  lt_of_lt_of_le one_pos (phi_ge_one h σ)

theorem Tfun_hasDerivAt (h : SlackData y ρ) (τ : ℝ) :
    HasDerivAt (Tfun y ρ) (phi y ρ τ) τ :=
  ((phi_cont h).integral_hasStrictDerivAt 0 τ).hasDerivAt

theorem Tfun_continuous (h : SlackData y ρ) : Continuous (Tfun y ρ) :=
  continuous_iff_continuousAt.mpr fun τ => (Tfun_hasDerivAt h τ).continuousAt

theorem Tfun_strictMono (h : SlackData y ρ) : StrictMono (Tfun y ρ) := by
  apply strictMono_of_deriv_pos
  intro τ
  rw [(Tfun_hasDerivAt h τ).deriv]
  exact phi_pos h τ

theorem Tfun_zero : Tfun y ρ 0 = 0 := by
  unfold Tfun
  exact intervalIntegral.integral_same

theorem Tfun_ge (h : SlackData y ρ) (τ : ℝ) (hτ : 0 ≤ τ) : τ ≤ Tfun y ρ τ := by
  unfold Tfun
  have hint : (∫ σ in (0 : ℝ)..τ, (1 : ℝ)) ≤ ∫ σ in (0 : ℝ)..τ, phi y ρ σ := by
    apply intervalIntegral.integral_mono_on hτ
    · exact continuous_const.intervalIntegrable _ _
    · exact (phi_cont h).intervalIntegrable _ _
    · intro σ _; exact phi_ge_one h σ
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at hint
  exact hint

theorem Tfun_le (h : SlackData y ρ) (τ : ℝ) (hτ : τ ≤ 0) : Tfun y ρ τ ≤ τ := by
  unfold Tfun
  rw [intervalIntegral.integral_symm]
  have hint : (∫ σ in τ..(0 : ℝ), (1 : ℝ)) ≤ ∫ σ in τ..(0 : ℝ), phi y ρ σ := by
    apply intervalIntegral.integral_mono_on hτ
    · exact continuous_const.intervalIntegrable _ _
    · exact (phi_cont h).intervalIntegrable _ _
    · intro σ _; exact phi_ge_one h σ
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, zero_sub] at hint
  linarith

theorem Tfun_tendsto_atTop (h : SlackData y ρ) : Tendsto (Tfun y ρ) atTop atTop :=
  tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono fun τ hτ => Tfun_ge h τ hτ) tendsto_id

theorem Tfun_tendsto_atBot (h : SlackData y ρ) : Tendsto (Tfun y ρ) atBot atBot :=
  tendsto_atBot_mono' atBot ((eventually_le_atBot 0).mono fun τ hτ => Tfun_le h τ hτ) tendsto_id

theorem Tfun_surjective (h : SlackData y ρ) : Function.Surjective (Tfun y ρ) :=
  (Tfun_continuous h).surjective (Tfun_tendsto_atTop h) (Tfun_tendsto_atBot h)

/-- The clock as an order isomorphism of `ℝ`. -/
noncomputable def Tiso (h : SlackData y ρ) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (Tfun y ρ) (Tfun_strictMono h) (Tfun_surjective h)

theorem Tiso_apply (h : SlackData y ρ) (τ : ℝ) : Tiso h τ = Tfun y ρ τ := rfl

/-- The time change `τ = T⁻¹`. -/
noncomputable def tau (h : SlackData y ρ) (t : ℝ) : ℝ := (Tiso h).symm t

theorem Tfun_tau (h : SlackData y ρ) (t : ℝ) : Tfun y ρ (tau h t) = t := by
  rw [← Tiso_apply]; exact (Tiso h).apply_symm_apply t

theorem tau_Tfun (h : SlackData y ρ) (τ : ℝ) : tau h (Tfun y ρ τ) = τ := by
  unfold tau; rw [← Tiso_apply]; exact (Tiso h).symm_apply_apply τ

theorem tau_zero (h : SlackData y ρ) : tau h 0 = 0 := by
  have := tau_Tfun h 0
  rwa [Tfun_zero] at this

theorem tau_strictMono (h : SlackData y ρ) : StrictMono (tau h) := (Tiso h).symm.strictMono

theorem tau_pos (h : SlackData y ρ) {t : ℝ} (ht : 0 < t) : 0 < tau h t := by
  have := tau_strictMono h ht
  rwa [tau_zero] at this

theorem tau_nonneg (h : SlackData y ρ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ tau h t := by
  have := (tau_strictMono h).monotone ht
  rwa [tau_zero] at this

theorem tau_continuous (h : SlackData y ρ) : Continuous (tau h) := (Tiso h).symm.continuous

theorem tau_tendsto_atTop (h : SlackData y ρ) : Tendsto (tau h) atTop atTop :=
  (Tiso h).symm.tendsto_atTop

/-- `τ' t = ρ (y (τ t))²` for `t ≥ 0`. -/
theorem tau_hasDerivAt (h : SlackData y ρ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (tau h) ((ρ (y (tau h t))) ^ 2) t := by
  have hτ := tau_nonneg h ht
  have hT : HasDerivAt (Tfun y ρ) (phi y ρ (tau h t)) (tau h t) := Tfun_hasDerivAt h _
  have hne : phi y ρ (tau h t) ≠ 0 := (phi_pos h _).ne'
  have hfg : ∀ᶠ s in 𝓝 t, Tfun y ρ (tau h s) = s := Eventually.of_forall (Tfun_tau h)
  have hinv := HasDerivAt.of_local_left_inverse (tau_continuous h).continuousAt hT hne hfg
  have hphi : (phi y ρ (tau h t))⁻¹ = (ρ (y (tau h t))) ^ 2 := by
    unfold phi
    rw [max_eq_left hτ, inv_pow, inv_inv]
  rwa [hphi] at hinv

/-- **Proposition 4.1 (conjugacy).** `z = y ∘ τ` solves `z' = ρ(z)² • g(z)` for `t ≥ 0`. -/
theorem timeChange_hasDerivAt (h : SlackData y ρ) {g : E → E}
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (g (y t)) t) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (y ∘ tau h) ((ρ (y (tau h t))) ^ 2 • g (y (tau h t))) t :=
  (hy _ (tau_nonneg h ht)).scomp t (tau_hasDerivAt h ht)

theorem timeChange_init (h : SlackData y ρ) : (y ∘ tau h) 0 = y 0 := by
  simp [tau_zero h]

/-- **Proposition 4.1 (limits).** A readout limit along `y` is a readout limit along `y ∘ τ`. -/
theorem timeChange_readout_tendsto (h : SlackData y ρ) {φ : E → ℝ} {L : ℝ}
    (hφ : Tendsto (fun τ => φ (y τ)) atTop (𝓝 L)) :
    Tendsto (fun t => φ (y (tau h t))) atTop (𝓝 L) :=
  hφ.comp (tau_tendsto_atTop h)

end NAPTimeChange
end Ripple

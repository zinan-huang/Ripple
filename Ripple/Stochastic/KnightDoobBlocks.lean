import Ripple.Stochastic.KnightTerminalValue

/-!
# Measurable block envelopes from continuous-time Doob

Dyadic maxima define measurable envelopes of unit-time increments. Continuous
paths identify them with the full block supremum on one event. Doob bounds the
sum of their second moments by four times the sum of the terminal increment
second moments. This closes the continuous-time convergence upgrade whenever
that increment energy is summable.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Ripple.ProbabilityTheory
open Ripple.Analysis Ripple.Stochastic.Doob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A shifted increment, extended constantly to negative elapsed time. -/
def blockIncrement (M : ℝ≥0 → Ω → ℝ) (n : ℕ) (r : ℝ) (ω : Ω) : ℝ :=
  M ((n : ℝ≥0) + r.toNNReal) ω - M n ω

/-- Countable dyadic envelope; this definition is measurable without needing
measurability of an uncountable supremum. -/
noncomputable def blockEnvelope (M : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ k : ℕ, (‖dyadicRunMax (blockIncrement M n) 1 k ω‖₊ : ℝ≥0∞)

theorem measurable_blockEnvelope {M : ℝ≥0 → Ω → ℝ}
    (hM : ∀ t, Measurable (M t)) (n : ℕ) : Measurable (blockEnvelope M n) :=
  Measurable.iSup fun k => measurable_enorm_dyadicRunMax
    (fun r => (hM _).sub (hM _)) 1 k

/-- The shifted increment is a martingale for the shifted common filtration. -/
theorem martingale_blockIncrement {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P) (n : ℕ) :
    Martingale (blockIncrement M n)
      (Ripple.Stochastic.Doob.Filtration.compMono mΩ F
        (fun r : ℝ => (n : ℝ≥0) + r.toNNReal)
        (fun _ _ h => add_le_add le_rfl (Real.toNNReal_le_toNNReal h))) P := by
  let G := Ripple.Stochastic.Doob.Filtration.compMono mΩ F
    (fun r : ℝ => (n : ℝ≥0) + r.toNNReal)
    (fun _ _ h => add_le_add le_rfl (Real.toNNReal_le_toNNReal h))
  have hshift : Martingale (fun r : ℝ => M ((n : ℝ≥0) + r.toNNReal)) G P :=
    martingale_compMono hM _ _
  have hconstant : Martingale (fun _ : ℝ => M n) G P := by
    refine ⟨fun r => (hM.stronglyAdapted n).mono
      (F.mono (le_add_of_nonneg_right bot_le)), ?_⟩
    intro r s hrs
    rw [condExp_of_stronglyMeasurable (G.le r)
      ((hM.stronglyAdapted n).mono (F.mono (le_add_of_nonneg_right bot_le))) (hM.integrable n)]
  exact hshift.sub hconstant

/-- Doob's dyadic estimate bounds the measurable envelope directly. -/
theorem lintegral_blockEnvelope_sq_le {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P) (n : ℕ) :
    (∫⁻ ω, blockEnvelope M n ω ^ 2 ∂P) ≤
      4 * ∫⁻ ω, (‖M ((n : ℝ≥0) + 1) ω - M n ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  simpa [blockEnvelope, blockIncrement] using
    lintegral_iSup_dyadicRunMax_sq_le (martingale_blockIncrement hM n) (by norm_num : (0 : ℝ) ≤ 1)

/-- Every actual block increment lies below the dyadic envelope on a continuous
path. The assertion is simultaneous in the time inside the block. -/
theorem block_increment_le_envelope
    {M : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (fun t => M t ω))
    (n : ℕ) {t : ℝ≥0} (hn : (n : ℝ≥0) ≤ t) (ht : t ≤ (n : ℝ≥0) + 1) :
    (‖M t ω - M n ω‖₊ : ℝ≥0∞) ≤ blockEnvelope M n ω := by
  have hcont : Continuous (fun r : ℝ => blockIncrement M n r ω) :=
    (hc.comp (continuous_const.add continuous_real_toNNReal)).sub continuous_const
  have heq := iSup_enorm_eq_iSup_dyadicRunMax (M := blockIncrement M n)
    (ω := ω) (by norm_num : (0 : ℝ) ≤ 1)
    (fun r => hcont.continuousAt.continuousWithinAt)
  change _ ≤ ⨆ k : ℕ, (‖dyadicRunMax (blockIncrement M n) 1 k ω‖₊ : ℝ≥0∞)
  rw [← heq]
  let r : ℝ := (t - (n : ℝ≥0) : ℝ≥0)
  have hr : r ∈ Icc (0 : ℝ) 1 := by
    refine ⟨(t - (n : ℝ≥0)).coe_nonneg, ?_⟩
    have hsub : t - (n : ℝ≥0) ≤ 1 := (tsub_le_iff_left).mpr ht
    exact_mod_cast hsub
  have hvalue : blockIncrement M n r ω = M t ω - M n ω := by
    simp [blockIncrement, r, add_tsub_cancel_of_le hn]
  exact le_iSup_of_le ⟨r, hr⟩ (le_of_eq (congrArg (fun x : ℝ => (‖x‖₊ : ℝ≥0∞)) hvalue.symm))

/-- Finite total increment energy gives finite total envelope energy. -/
theorem tsum_lintegral_blockEnvelope_sq_ne_top
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    (henergy : (∑' n : ℕ, ∫⁻ ω,
      (‖M ((n : ℝ≥0) + 1) ω - M n ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤) :
    (∑' n : ℕ, ∫⁻ ω, blockEnvelope M n ω ^ 2 ∂P) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) henergy)
  calc (∑' n : ℕ, ∫⁻ ω, blockEnvelope M n ω ^ 2 ∂P)
      ≤ ∑' n : ℕ, 4 * ∫⁻ ω,
          (‖M ((n : ℝ≥0) + 1) ω - M n ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        ENNReal.tsum_le_tsum (lintegral_blockEnvelope_sq_le hM)
    _ = _ := by rw [ENNReal.tsum_mul_left]

/-- Telescoping a bounded increasing sequence of mean clock values gives
finite total increment energy. This is the algebraic use of stopped isometry. -/
theorem increment_energy_ne_top_of_clock
    {P : Measure Ω} {M : ℝ≥0 → Ω → ℝ} (e : ℕ → ℝ≥0)
    (he : Monotone e) {C : ℝ≥0} (hC : ∀ n, e n ≤ C)
    (hisom : ∀ n : ℕ, (∫⁻ ω,
      (‖M ((n : ℝ≥0) + 1) ω - M n ω‖₊ : ℝ≥0∞) ^ 2 ∂P) =
        ((e (n + 1) - e n : ℝ≥0) : ℝ≥0∞)) :
    (∑' n : ℕ, ∫⁻ ω,
      (‖M ((n : ℝ≥0) + 1) ω - M n ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (show (C : ℝ≥0∞) ≠ ⊤ from ENNReal.coe_ne_top)
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  simp_rw [hisom]
  have hsum : ((∑ k ∈ Finset.range N, (e (k + 1) - e k) : ℝ≥0) : ℝ) =
      (e N : ℝ) - (e 0 : ℝ) := by
    simp only [NNReal.coe_sum]
    simp_rw [NNReal.coe_sub (he (Nat.le_succ _))]
    exact Finset.sum_range_sub (fun k => (e k : ℝ)) N
  have hnn : (∑ k ∈ Finset.range N, (e (k + 1) - e k)) ≤ C := by
    apply NNReal.coe_le_coe.mp
    rw [hsum]
    have hCN : (e N : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC N
    linarith [(e 0).coe_nonneg]
  exact_mod_cast hnn

/-- The full-time martingale limit from first-moment boundedness and finite
sum of consecutive increment second moments. For a bracket-capped stochastic
integral, the latter is supplied by telescoping its stopped-clock isometry. -/
theorem ae_tendsto_knightTerminalValue_of_increment_energy
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω)) {R : ℝ≥0}
    (hbound : ∀ n : ℕ, eLpNorm (M n) 1 P ≤ R)
    (henergy : (∑' n : ℕ, ∫⁻ ω,
      (‖M ((n : ℝ≥0) + 1) ω - M n ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto (fun t => M t ω) atTop (𝓝 (knightTerminalValue M ω)) := by
  have hmeas : ∀ t, Measurable (M t) := fun t =>
    ((hM.stronglyAdapted t).mono (F.le t)).measurable
  let S := blockEnvelope M
  let b : ℕ → Ω → ℝ := fun n ω => (S n ω).toReal
  have hS : ∀ n, Measurable (S n) := measurable_blockEnvelope hmeas
  have hb : ∀ n, Measurable (b n) := fun n => (hS n).ennreal_toReal
  have hsum := tsum_lintegral_blockEnvelope_sq_ne_top hM henergy
  have hfinite : ∀ᵐ ω ∂P, ∀ n, S n ω ≠ ⊤ := by
    apply ae_all_iff.mpr
    intro n
    have hint : (∫⁻ ω, S n ω ^ 2 ∂P) ≠ ⊤ :=
      ne_top_of_le_ne_top hsum (ENNReal.le_tsum n)
    filter_upwards [ae_lt_top' ((hS n).pow_const 2).aemeasurable hint] with ω hω
    intro htop
    simpa [htop] using hω
  have hbsum : (∑' n, ∫⁻ ω, (‖b n ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hsum
    apply ENNReal.tsum_le_tsum
    intro n
    apply lintegral_mono_ae
    filter_upwards [hfinite] with ω hω
    have heq : (‖b n ω‖₊ : ℝ≥0∞) = S n ω := by
      have h0 : 0 ≤ b n ω := ENNReal.toReal_nonneg
      calc (‖b n ω‖₊ : ℝ≥0∞) = ((b n ω).toNNReal : ℝ≥0∞) := by
            rw [Real.toNNReal_eq_nnnorm_of_nonneg h0]
        _ = S n ω := ENNReal.ofReal_toReal (hω n)
    rw [heq]
  apply ae_tendsto_knightTerminalValue_of_blocks hM hbound b hb hbsum
  filter_upwards [hc, hfinite] with ω hcω hω n t hn ht
  have hle := ENNReal.toReal_mono (hω n) (block_increment_le_envelope hcω n hn ht)
  simpa [b, S, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hle

/-- Full finite-clock convergence from the concrete stopped martingales and
clock-isometry data. All continuous-time work is discharged here by Doob;
random stopping and identification of the stopped clock are separate inputs. -/
theorem ae_finite_clock_convergence_of_stopped_isometry
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ≥0}
    (hM : ∀ k : ℕ, Measurable (M (k : ℝ≥0)))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hStoppedMartingale : ∀ n : ℕ, Martingale
      (fun t ω => clockStoppedPath (fun r => M r ω) (fun r => A r ω) n t) F P)
    (hStoppedFirstMoment : ∀ n : ℕ, ∃ R : ℝ≥0, ∀ k : ℕ,
      eLpNorm (fun ω => clockStoppedPath (fun r => M r ω) (fun r => A r ω) n k) 1 P ≤ R)
    (e : ℕ → ℕ → ℝ≥0) (he : ∀ n, Monotone (e n))
    (hcap : ∀ n k, e n k ≤ (n : ℝ≥0))
    (hStoppedIsometry : ∀ n k : ℕ, (∫⁻ ω,
      (‖clockStoppedPath (fun r => M r ω) (fun r => A r ω) n ((k : ℝ≥0) + 1) -
        clockStoppedPath (fun r => M r ω) (fun r => A r ω) n k‖₊ : ℝ≥0∞) ^ 2 ∂P) =
        ((e n (k + 1) - e n k : ℝ≥0) : ℝ≥0∞)) :
    Measurable (knightTerminalValue M) ∧
      ∀ᵐ ω ∂P, terminalClock (fun t => A t ω) ≠ ⊤ →
        Tendsto (fun t => M t ω) atTop (𝓝 (knightTerminalValue M ω)) := by
  refine ⟨measurable_knightTerminalValue hM, ?_⟩
  refine ae_tendsto_on_finite_terminalClock_of_stopped (M := M) (A := A) (P := P) ?_
  intro n
  obtain ⟨R, hR⟩ := hStoppedFirstMoment n
  have hcont : ∀ᵐ ω ∂P, Continuous
      (clockStoppedPath (fun r => M r ω) (fun r => A r ω) n) :=
    hc.mono fun ω hω => continuous_clockStoppedPath hω n
  have henergy := increment_energy_ne_top_of_clock (P := P)
    (M := fun t ω => clockStoppedPath (fun r => M r ω) (fun r => A r ω) n t) (e n) (he n)
    (hcap n) (hStoppedIsometry n)
  have hlim := ae_tendsto_knightTerminalValue_of_increment_energy (P := P) (F := F)
    (M := fun t ω => clockStoppedPath (fun r => M r ω) (fun r => A r ω) n t)
    (hStoppedMartingale n) hcont hR henergy
  exact hlim.mono fun ω hω => ⟨_, hω⟩

end Ripple.ProbabilityTheory

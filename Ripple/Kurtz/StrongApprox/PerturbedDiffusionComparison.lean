-- Ripple/Kurtz/StrongApprox/PerturbedDiffusionComparison.lean
import Ripple.Kurtz.StrongApprox.PerturbedClockBound
import Ripple.Kurtz.StrongApprox.RateLimitBound

/-!
# The deterministic comparison of the chain with the diffusion

Kurtz 1978, Lemma 3.2 (p. 231) and the proof of Theorem 3.3(a) (p. 232-233):
a pathwise comparison of the chain `X_N` (rates `f_l^N`, equation (1.3) with
a driver `Y_l`) and the diffusion `Z_N` of (1.6) (rates `f_l`, driver
`B_l(t) = t + W_l(t)`), given the rate assumptions (3.1) `f_l^N ≤ ε_l`,
(3.2) `|f_l - f_l^N| ≤ Γ ε_l / N`, (3.19) `|f_l(x) - f_l(y)| ≤ ε_l M ‖x - y‖`,
a KMT-type bound `|Y_l(u) - u - W_l(u)| ≤ R` on the clock horizon, and an
affine bound on the Brownian increments on that horizon.  The result is the
explicit bound
`‖X_N(t) - Z_N(t)‖ ≤ exp(257 M E T) (S R + 1024 S q + 257 Γ E T) / N`,
`S = Σ_l ‖v_l‖`, `E = Σ_l ‖v_l‖ ε_l`.  The proof subtracts the two equations
(`perturbed_timeChange_diffusion_sub`), bounds the clock difference using
`PerturbedClockBound`, and closes with the integral Gronwall lemma.
-/

noncomputable section
namespace Ripple.Kurtz.StrongApprox
open MeasureTheory Set Finset
open scoped BigOperators Interval

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The diffusion drift integral is the sum of its unscaled clocks. -/
theorem integral_tcDrift_eq_sum_clock
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {X : ℝ → Fin d → ℝ} {t : ℝ}
    (hbeta : ∀ l, IntervalIntegrable (fun s => beta l (X s)) volume 0 t) :
    (∫ s in (0 : ℝ)..t, tcDrift beta v (X s)) =
      ∑ l, clock beta X l t • v l := by
  classical
  unfold tcDrift clock
  rw [intervalIntegral.integral_finsetSum
    (fun l _ => intervalIntegrable_smul_const_vec (hbeta l) (v l))]
  exact Finset.sum_congr rfl fun l _ => intervalIntegral.integral_smul_const _ _

/-- Exact subtraction with the chain clock formed from `betaN` and the
 diffusion clock formed from `beta`. -/
theorem perturbed_timeChange_diffusion_sub
    {betaN beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {Y W : ι → ℝ → ℝ} {N : ℝ} {X Z : ℝ → Fin d → ℝ}
    {xZero : Fin d → ℝ} {t : ℝ} (hN : 0 < N)
    (hbetaZ : ∀ l, IntervalIntegrable (fun s => beta l (Z s)) volume 0 t)
    (hX : X t = xZero + ∑ l,
      (Y l (scaledTcClock N betaN X l t) / N) • v l)
    (hZ : Z t = xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s)) +
      ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l) :
    X t - Z t = ∑ l,
      ((Y l (scaledTcClock N betaN X l t) - scaledTcClock N beta Z l t -
        W l (scaledTcClock N beta Z l t)) / N) • v l := by
  classical
  rw [hX, hZ, integral_tcDrift_eq_sum_clock hbetaZ]
  have hid (a b c : Fin d → ℝ) : (xZero + a) - (xZero + b + c) = a - b - c := by
    abel
  rw [hid, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← sub_smul, ← sub_smul]
  congr 1
  unfold scaledTcClock
  field_simp [hN.ne']

/-- Rate error and state error produce a linear integral inequality.
The affine slope multiplies the clock error; the drift contributes one more copy. -/
theorem perturbed_diffusion_linear_inequality
    {betaN beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {B delta K : ι → ℝ} {Y W : ι → ℝ → ℝ}
    {N T H R qZero qSlope : ℝ} {X Z : ℝ → Fin d → ℝ}
    {xZero : Fin d → ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (hqSlope : 0 ≤ qSlope)
    (hB : ∀ l, 0 ≤ B l) (hdelta : ∀ l, 0 ≤ delta l) (hK : ∀ l, 0 ≤ K l)
    (hbetaN0 : ∀ l x, 0 ≤ betaN l x) (hbeta0 : ∀ l x, 0 ≤ beta l x)
    (hbetaNB : ∀ l x, betaN l x ≤ B l) (hbetaB : ∀ l x, beta l x ≤ B l)
    (hpert : ∀ l x, |betaN l x - beta l x| ≤ delta l / N)
    (hLip : ∀ l x y, |beta l x - beta l y| ≤ K l * ‖x - y‖)
    (hbetaNX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => betaN l (X s)) volume 0 t)
    (hbetaX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hbetaZ : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (Z s)) volume 0 t)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    (hHorizon : ∀ l, N * (B l * T) ≤ H)
    (hXeq : ∀ t ∈ Icc (0 : ℝ) T, X t = xZero + ∑ l,
      (Y l (scaledTcClock N betaN X l t) / N) • v l)
    (hZeq : ∀ t ∈ Icc (0 : ℝ) T,
      Z t = xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s)) +
        ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l)
    (hKMT : ∀ l u, u ∈ Icc (0 : ℝ) H → |Y l u - u - W l u| ≤ R)
    (hWaff : ∀ l u w, u ∈ Icc (0 : ℝ) H → w ∈ Icc (0 : ℝ) H →
      |W l u - W l w| ≤ qZero + qSlope * |u - w|)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖X t - Z t‖ ≤
      (channelWeight (fun l => ‖v l‖) * (R + qZero) +
        (1 + qSlope) * channelClockLip (fun l => ‖v l‖) delta * T) / N +
      (1 + qSlope) * channelClockLip (fun l => ‖v l‖) K *
        (∫ s in (0 : ℝ)..t, ‖X s - Z s‖) := by
  classical
  let I : ℝ := ∫ s in (0 : ℝ)..t, ‖X s - Z s‖
  have hclockX (l : ι) : scaledTcClock N betaN X l t ∈ Icc (0 : ℝ) H :=
    scaledTcClock_mem_horizon (U := Set.univ) hN hT hB
      (fun l x _ => hbetaN0 l x) (fun l x _ => hbetaNB l x)
      (fun _ _ => Set.mem_univ _) ht (hbetaNX l t ht) (hHorizon l)
  have hclockZ (l : ι) : scaledTcClock N beta Z l t ∈ Icc (0 : ℝ) H :=
    scaledTcClock_mem_horizon (U := Set.univ) hN hT hB
      (fun l x _ => hbeta0 l x) (fun l x _ => hbetaB l x)
      (fun _ _ => Set.mem_univ _) ht (hbetaZ l t ht) (hHorizon l)
  have hgap (l : ι) :
      |scaledTcClock N betaN X l t - scaledTcClock N beta Z l t| ≤
        delta l * t + N * K l * I :=
    abs_scaledTcClock_perturbed_sub_le (U := Set.univ) hN hK
      (fun l x _ => hpert l x) (fun l x y _ _ => hLip l x y)
      (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
      huint ht (hbetaNX l t ht) (hbetaX l t ht) (hbetaZ l t ht)
  have hchannel (l : ι) :
      |Y l (scaledTcClock N betaN X l t) - scaledTcClock N beta Z l t -
        W l (scaledTcClock N beta Z l t)| ≤
      R + qZero + (1 + qSlope) * (delta l * T + N * K l * I) := by
    let a := scaledTcClock N betaN X l t
    let b := scaledTcClock N beta Z l t
    have hdecomp : Y l a - b - W l b =
        (Y l a - a - W l a) + (W l a - W l b) + (a - b) := by ring
    have htri := (abs_add_le ((Y l a - a - W l a) + (W l a - W l b))
      (a - b)).trans (add_le_add
        (abs_add_le (Y l a - a - W l a) (W l a - W l b)) le_rfl)
    have hk := hKMT l a (hclockX l)
    have hw := hWaff l a b (hclockX l) (hclockZ l)
    have hg : |a - b| ≤ delta l * t + N * K l * I := hgap l
    have hTdelta := mul_le_mul_of_nonneg_left ht.2 (hdelta l)
    have hscaled := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1 + qSlope by linarith)
    have hscaledT := mul_le_mul_of_nonneg_left hTdelta
      (show 0 ≤ 1 + qSlope by linarith)
    change |Y l a - b - W l b| ≤ _
    rw [hdecomp]
    nlinarith only [htri, hk, hw, hscaled, hscaledT]
  rw [perturbed_timeChange_diffusion_sub hN (fun l => hbetaZ l t ht)
    (hXeq t ht) (hZeq t ht)]
  refine (norm_sum_le _ _).trans ?_
  calc
    (∑ l, ‖((Y l (scaledTcClock N betaN X l t) - scaledTcClock N beta Z l t -
        W l (scaledTcClock N beta Z l t)) / N) • v l‖) ≤
      ∑ l, (R + qZero + (1 + qSlope) * (delta l * T + N * K l * I)) / N * ‖v l‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hN]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (hchannel l) hN.le) (norm_nonneg _)
    _ = (channelWeight (fun l => ‖v l‖) * (R + qZero) +
        (1 + qSlope) * channelClockLip (fun l => ‖v l‖) delta * T) / N +
      (1 + qSlope) * channelClockLip (fun l => ‖v l‖) K * I := by
        unfold channelWeight channelClockLip
        calc
          _ = ∑ l, ((‖v l‖ * (R + qZero) +
              (1 + qSlope) * (‖v l‖ * delta l) * T) / N +
              (1 + qSlope) * (‖v l‖ * K l) * I) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            field_simp [hN.ne'] <;> ring
          _ = _ := by
            simp only [add_div, Finset.sum_add_distrib, Finset.sum_div,
              Finset.sum_mul, Finset.mul_sum]

/-- Perturbed affine comparison at a fixed scale. The constants are expressed
through the weighted rate error and weighted state Lipschitz constant. -/
theorem perturbed_diffusion_comparison_of_affine
    {betaN beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {B delta K : ι → ℝ} {Y W : ι → ℝ → ℝ}
    {N T H R qZero qSlope : ℝ} {X Z : ℝ → Fin d → ℝ}
    {xZero : Fin d → ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hqZero : 0 ≤ qZero) (hqSlope : 0 ≤ qSlope)
    (hB : ∀ l, 0 ≤ B l) (hdelta : ∀ l, 0 ≤ delta l) (hK : ∀ l, 0 ≤ K l)
    (hbetaN0 : ∀ l x, 0 ≤ betaN l x) (hbeta0 : ∀ l x, 0 ≤ beta l x)
    (hbetaNB : ∀ l x, betaN l x ≤ B l) (hbetaB : ∀ l x, beta l x ≤ B l)
    (hpert : ∀ l x, |betaN l x - beta l x| ≤ delta l / N)
    (hLip : ∀ l x y, |beta l x - beta l y| ≤ K l * ‖x - y‖)
    (hbetaNX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => betaN l (X s)) volume 0 t)
    (hbetaX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hbetaZ : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (Z s)) volume 0 t)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    (hurc : ∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt (fun s => ‖X s - Z s‖) (Ioi t) t)
    (hHorizon : ∀ l, N * (B l * T) ≤ H)
    (hXeq : ∀ t ∈ Icc (0 : ℝ) T, X t = xZero + ∑ l,
      (Y l (scaledTcClock N betaN X l t) / N) • v l)
    (hZeq : ∀ t ∈ Icc (0 : ℝ) T,
      Z t = xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s)) +
        ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l)
    (hKMT : ∀ l u, u ∈ Icc (0 : ℝ) H → |Y l u - u - W l u| ≤ R)
    (hWaff : ∀ l u w, u ∈ Icc (0 : ℝ) H → w ∈ Icc (0 : ℝ) H →
      |W l u - W l w| ≤ qZero + qSlope * |u - w|)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖X t - Z t‖ ≤
      Real.exp ((1 + qSlope) * channelClockLip (fun l => ‖v l‖) K * T) *
      (channelWeight (fun l => ‖v l‖) * (R + qZero) +
        (1 + qSlope) * channelClockLip (fun l => ‖v l‖) delta * T) / N := by
  let A := (channelWeight (fun l => ‖v l‖) * (R + qZero) +
    (1 + qSlope) * channelClockLip (fun l => ‖v l‖) delta * T) / N
  let b := (1 + qSlope) * channelClockLip (fun l => ‖v l‖) K
  have hS := channelWeight_nonneg (fun l => norm_nonneg (v l))
  have hDelta := channelClockLip_nonneg (fun l => norm_nonneg (v l)) hdelta
  have hKsum := channelClockLip_nonneg (fun l => norm_nonneg (v l)) hK
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hraw : ∀ r ∈ Icc (0 : ℝ) T,
      ‖X r - Z r‖ ≤ A + ∫ s in (0 : ℝ)..r, b * ‖X s - Z s‖ := by
    intro r hr
    rw [intervalIntegral.integral_const_mul]
    exact perturbed_diffusion_linear_inequality hN hT hqSlope hB hdelta hK
      hbetaN0 hbeta0 hbetaNB hbetaB hpert hLip hbetaNX hbetaX hbetaZ
      huint hHorizon hXeq hZeq hKMT hWaff hr
  have hbu : IntegrableOn (fun s => b * ‖X s - Z s‖) (Icc (0 : ℝ) T) :=
    huint.const_mul b
  have hmain := Ripple.Kurtz.integral_gronwall
    (T := T) (α := A) (β := b) (u := fun s => ‖X s - Z s‖)
    hT hA hb (fun _ _ => norm_nonneg _) hraw
    (fun r hr => (intervalIntegrable_iff_integrableOn_Icc_of_le hr.1).mpr
      (hbu.mono_set (Icc_subset_Icc_right hr.2.le)))
    (fun r hr => tendsto_const_nhds.mul (hurc r hr))
    (fun r hr => ⟨Icc 0 T, Icc_mem_nhdsGT_of_mem hr, hbu.aestronglyMeasurable⟩)
    (by
      have hint : IntegrableOn (fun s => b * ‖X s - Z s‖) (uIcc 0 T) volume := by
        rw [uIcc_of_le hT]
        exact hbu
      have hprim := intervalIntegral.continuousOn_primitive_interval hint
      rw [uIcc_of_le hT] at hprim
      exact continuousOn_const.add hprim)
    t ht
  have hexp : Real.exp (b * t) ≤ Real.exp (b * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hb)
  calc
    ‖X t - Z t‖ ≤ A * Real.exp (b * t) := hmain
    _ ≤ A * Real.exp (b * T) := mul_le_mul_of_nonneg_left hexp hA
    _ = _ := by dsimp [A, b]; ring

/-- Kurtz (3.1), (3.2), and (3.19) give the advertised constant `257`.
Here `S = ∑ l, ‖v l‖` and `E = ∑ l, ‖v l‖ * eps l`. The covering
horizon stays `H` in both driver assumptions. -/
theorem perturbed_diffusion_comparison
    {f : ι → (Fin d → ℝ) → ℝ} {fN : ℕ → ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {eps : ι → ℝ} {Y W : ι → ℝ → ℝ}
    {N : ℕ} {Gamma M T H R q : ℝ} {X Z : ℝ → Fin d → ℝ}
    {xZero : Fin d → ℝ}
    (hN : 2 ≤ N) (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (heps : ∀ l, 0 ≤ eps l)
    (hf : ∀ l x, 0 ≤ f l x)
    (hfN : ∀ n : ℕ, 2 ≤ n → ∀ l x, 0 ≤ fN n l x)
    (hbound : ∀ n : ℕ, 2 ≤ n → ∀ l x, fN n l x ≤ eps l)
    (hpert : ∀ n : ℕ, 2 ≤ n → ∀ l x,
      |f l x - fN n l x| ≤ Gamma * eps l / (n : ℝ))
    (hLip : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hfNX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => fN N l (X s)) volume 0 t)
    (hfX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => f l (X s)) volume 0 t)
    (hfZ : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => f l (Z s)) volume 0 t)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    (hurc : ∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt (fun s => ‖X s - Z s‖) (Ioi t) t)
    (hHorizon : ∀ l, (N : ℝ) * (eps l * T) ≤ H)
    (hXeq : ∀ t ∈ Icc (0 : ℝ) T, X t = xZero + ∑ l,
      (Y l (scaledTcClock (N : ℝ) (fN N) X l t) / (N : ℝ)) • v l)
    (hZeq : ∀ t ∈ Icc (0 : ℝ) T,
      Z t = xZero + (∫ s in (0 : ℝ)..t, tcDrift f v (Z s)) +
        ∑ l, (W l (scaledTcClock (N : ℝ) f Z l t) / (N : ℝ)) • v l)
    (hKMT : ∀ l u, u ∈ Icc (0 : ℝ) H → |Y l u - u - W l u| ≤ R)
    (hWaff : ∀ l u w, u ∈ Icc (0 : ℝ) H → w ∈ Icc (0 : ℝ) H →
      |W l u - W l w| ≤ 1024 * q + 256 * |u - w|)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖X t - Z t‖ ≤
      Real.exp (257 * M * channelClockLip (fun l => ‖v l‖) eps * T) *
      (channelWeight (fun l => ‖v l‖) * R +
        1024 * channelWeight (fun l => ‖v l‖) * q +
        257 * Gamma * channelClockLip (fun l => ‖v l‖) eps * T) / (N : ℝ) := by
  classical
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hupper : ∀ l x, f l x ≤ eps l := rate_limit_le hbound hpert
  have hreverse : ∀ l x, |fN N l x - f l x| ≤ Gamma * eps l / (N : ℝ) := by
    intro l x
    rw [abs_sub_comm]
    exact hpert N hN l x
  have hmain := perturbed_diffusion_comparison_of_affine
    (B := eps) (delta := fun l => Gamma * eps l) (K := fun l => eps l * M)
    (qZero := 1024 * q) (qSlope := 256)
    hNreal hT hR (by positivity) (by norm_num) heps
    (fun l => mul_nonneg hGamma (heps l)) (fun l => mul_nonneg (heps l) hM)
    (hfN N hN) hf (hbound N hN) hupper hreverse hLip
    hfNX hfX hfZ huint hurc hHorizon hXeq hZeq hKMT hWaff ht
  have hKsum : channelClockLip (fun l => ‖v l‖) (fun l => eps l * M) =
      M * channelClockLip (fun l => ‖v l‖) eps := by
    unfold channelClockLip
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hDelta : channelClockLip (fun l => ‖v l‖) (fun l => Gamma * eps l) =
      Gamma * channelClockLip (fun l => ‖v l‖) eps := by
    unfold channelClockLip
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hKsum, hDelta] at hmain
  have hexponent : (1 + (256 : ℝ)) *
      (M * channelClockLip (fun l => ‖v l‖) eps) * T =
      257 * M * channelClockLip (fun l => ‖v l‖) eps * T := by ring
  rw [hexponent] at hmain
  convert hmain using 1; ring


end Ripple.Kurtz.StrongApprox
end

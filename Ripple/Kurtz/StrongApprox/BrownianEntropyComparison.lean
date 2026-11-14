-- Ripple/Kurtz/StrongApprox/BrownianEntropyComparison.lean
import Ripple.Kurtz.StrongApprox.BrownianEntropyModulus
import Ripple.Kurtz.StrongApprox.ClockModulusGronwall
import Ripple.Kurtz.StrongApprox.DiffusionClockComparison

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal BigOperators

variable {ι : Type*} [Fintype ι]
variable {d : ℕ}

/-- Use a nontrivial entropy parameter in the pathwise comparison.  Replacing
`a` by `max a 2` costs no probability and only a fixed factor in the final
logarithmic budget. -/
def comparisonEntropyTail (a : ℝ) : ℝ := max a 2

/-- Affine modulus fed to `DiffusionClockComparison` after applying its entropy-envelope lemma. -/
def comparisonAffineModulus (q h : ℝ) : ℝ := 1024 * q + 256 * h

/-- Extra fixed factor needed to replace `max a 2` by `a` in the final budget. -/
def comparisonTailFactor : ℝ := 1 + 2 / Real.log 2

/-- The explicit comparison constant resulting from `C = 256` and the
fully affine Gronwall route. -/
def brownianEntropyComparisonGamma
    (S Ksum T D : ℝ) : ℝ :=
  let fac := 1 + (1 + Real.log D) / Real.log 2
  S * (1 + 1024 * fac) * comparisonTailFactor *
    Real.exp (257 * Ksum * T)

private theorem entropyBound_le_q5228_shape
    {H N a h : ℝ} (hN : 2 ≤ N) (ha : 0 ≤ a)
    (hh : h ∈ Icc (0 : ℝ) H) :
    brownianEntropyBound H (comparisonEntropyTail a) h ≤
      512 * Real.sqrt
        (h * (Real.log (H / h) + comparisonEntropyTail a)) +
      512 * (Real.log N + comparisonEntropyTail a) := by
  have hlogN : (1 / 2 : ℝ) < Real.log N := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN
    linarith [Real.log_two_gt_d9]
  have htail0 : 0 ≤ comparisonEntropyTail a := by
    unfold comparisonEntropyTail
    positivity
  have hadd : 1 + comparisonEntropyTail a ≤
      2 * (Real.log N + comparisonEntropyTail a) := by
    nlinarith
  have hsqrt := Real.sqrt_nonneg
    (h * (Real.log (H / h) + comparisonEntropyTail a))
  unfold brownianEntropyBound brownianEntropyConstant brownianEntropyCore
  split_ifs with hz
  · nlinarith [hsqrt]
  · nlinarith [hsqrt]

private theorem comparisonAffineModulus_mono {q : ℝ} :
    Monotone (comparisonAffineModulus q) := by
  intro x y hxy
  unfold comparisonAffineModulus
  linarith

/-- Pathwise adapter from the `BrownianEntropyModulus` modulus to `DiffusionClockComparison`.

The affine function is monotone, so this avoids needing monotonicity of the
raw entropy expression near the coarse endpoint. -/
theorem timeChange_diffusion_comparison_of_entropy
    {U : Set (Fin d → ℝ)}
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {B K : ι → ℝ} {Y W : ι → ℝ → ℝ}
    {N T D R a : ℝ}
    {X Z : ℝ → Fin d → ℝ} {xZero : Fin d → ℝ}
    (hNtwo : 2 ≤ N) (hT : 0 ≤ T) (hD : 1 ≤ D)
    (hR : 0 ≤ R) (ha : 0 ≤ a)
    (hB : ∀ l, 0 ≤ B l) (hK : ∀ l, 0 ≤ K l)
    (hBT : ∀ l, B l * T ≤ D)
    (hbeta0 : ∀ l y, y ∈ U → 0 ≤ beta l y)
    (hbetaB : ∀ l y, y ∈ U → beta l y ≤ B l)
    (hbetaLip : ∀ l y z, y ∈ U → z ∈ U →
      |beta l y - beta l z| ≤ K l * ‖y - z‖)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    (hZU : ∀ s ∈ Icc (0 : ℝ) T, Z s ∈ U)
    (hbetaX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hbetaZ : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (Z s)) volume 0 t)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    (hurc : ∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt (fun s => ‖X s - Z s‖) (Ioi t) t)
    (hXeq : ∀ t ∈ Icc (0 : ℝ) T,
      X t = xZero + ∑ l,
        (Y l (scaledTcClock N beta X l t) / N) • v l)
    (hZeq : ∀ t ∈ Icc (0 : ℝ) T,
      Z t = xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s)) +
        ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l)
    (hKMT : ∀ l u, u ∈ Icc (0 : ℝ) (N * D) →
      |Y l u - u - W l u| ≤ R)
    (hWcontinuous : ∀ l, Continuous (W l))
    (hWentropy : ∀ l u, u ∈ Icc (0 : ℝ) (N * D) →
      ∀ w, w ∈ Icc (0 : ℝ) (N * D) →
        |W l u - W l w| ≤
          brownianEntropyBound (N * D) (comparisonEntropyTail a) |u - w|)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖X t - Z t‖ ≤
      brownianEntropyComparisonGamma
          (channelWeight (fun l => ‖v l‖))
          (channelClockLip (fun l => ‖v l‖) K) T D *
        (R + Real.log N + a) / N := by
  let tail := comparisonEntropyTail a
  let p : ℝ := R + Real.log N + tail
  let q : ℝ := p + 1 + Real.log D
  let omega : ℝ → ℝ := comparisonAffineModulus q
  let fac : ℝ := 1 + (1 + Real.log D) / Real.log 2
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) hNtwo
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hH : 0 ≤ N * D := (mul_pos hN hDpos).le
  have htail0 : 0 ≤ tail := by
    dsimp [tail, comparisonEntropyTail]
    positivity
  have htailTwo : 2 ≤ tail := by
    dsimp [tail, comparisonEntropyTail]
    exact le_max_right _ _
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlogN : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) hNtwo
  have hp0 : 0 ≤ p := by
    dsimp [p]
    linarith [Real.log_two_gt_d9]
  have hqOne : 1 ≤ q := by
    dsimp [q]
    linarith
  have hqH : Real.log (N * D) + tail ≤ q := by
    rw [Real.log_mul hN.ne' hDpos.ne']
    dsimp [q, p]
    linarith
  have hqN : Real.log N + tail ≤ q := by
    dsimp [q, p]
    linarith
  have homega0 : 0 ≤ 1024 * q := by positivity
  have homegaSlope : 0 ≤ (256 : ℝ) := by norm_num
  have hHorizon : ∀ l, N * (B l * T) ≤ N * D := fun l =>
    mul_le_mul_of_nonneg_left (hBT l) hN.le
  have hWmod : ∀ l u w,
      u ∈ Icc (0 : ℝ) (N * D) →
      w ∈ Icc (0 : ℝ) (N * D) →
      |W l u - W l w| ≤ omega |u - w| := by
    intro l u w hu hw
    have hgap : |u - w| ∈ Icc (0 : ℝ) (N * D) := by
      constructor
      · exact abs_nonneg _
      · rw [abs_le]
        constructor <;> linarith [hu.1, hu.2, hw.1, hw.2]
    have hraw := hWentropy l u hu w hw
    have hshape := entropyBound_le_q5228_shape hNtwo ha hgap
    have haff := brownian_modulus_shape_le_affine
      (H := N * D) (N := N) (C := 512) (tail := tail)
      (q := q) (h := |u - w|)
      (mul_pos hN hDpos) hN (by norm_num) htail0 hqOne hqH hqN
      hgap.1 hgap.2
    dsimp [omega, comparisonAffineModulus]
    exact hraw.trans (hshape.trans (haff.trans (le_of_eq (by ring))))
  have hmain := timeChange_diffusion_comparison_of_affine
    (N := N) (T := T) (H := N * D) (R := R)
    (qZero := 1024 * q) (qSlope := 256)
    (omega := omega)
    hN hT hH hR homega0 homegaSlope
    hB hK hbeta0 hbetaB hbetaLip hXU hZU hbetaX hbetaZ
    huint hurc hHorizon hXeq hZeq hKMT hWcontinuous
    comparisonAffineModulus_mono hWmod
    (fun h _ => le_rfl) ht
  have hfac0 : 0 ≤ fac := by
    dsimp [fac]
    positivity
  have hqle : q ≤ fac * p := by
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpLog : Real.log 2 ≤ p := by
      dsimp [p]
      linarith
    dsimp [q, fac]
    calc
      p + 1 + Real.log D ≤
          p + ((1 + Real.log D) / Real.log 2) * p := by
        have h1 : 1 + Real.log D ≤ ((1 + Real.log D) / Real.log 2) * p := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlogTwo]
          exact mul_le_mul_of_nonneg_left hpLog (by linarith)
        linarith
      _ = (1 + (1 + Real.log D) / Real.log 2) * p := by ring
  have htailBudget : p ≤ comparisonTailFactor *
      (R + Real.log N + a) := by
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbase : Real.log 2 ≤ R + Real.log N + a := by
      linarith
    have htailLe : tail ≤ a + 2 := by
      dsimp [tail, comparisonEntropyTail]
      exact max_le (by linarith) (by linarith)
    dsimp [p, comparisonTailFactor]
    have htwo : 2 ≤ (2 / Real.log 2) *
        (R + Real.log N + a) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlogTwo]
      nlinarith
    nlinarith
  have hfront : R + 1024 * q ≤
      (1 + 1024 * fac) * comparisonTailFactor *
        (R + Real.log N + a) := by
    have hRle : R ≤ p := by
      dsimp [p]
      linarith [Real.log_two_gt_d9]
    have hpNonneg : 0 ≤ p := hp0
    calc
      R + 1024 * q ≤ p + 1024 * (fac * p) :=
        add_le_add hRle (mul_le_mul_of_nonneg_left hqle (by norm_num))
      _ = (1 + 1024 * fac) * p := by ring
      _ ≤ (1 + 1024 * fac) *
          (comparisonTailFactor * (R + Real.log N + a)) := by
        gcongr
      _ = (1 + 1024 * fac) * comparisonTailFactor *
          (R + Real.log N + a) := by ring
  have hexp :
      Real.exp (((1 + (256 : ℝ)) *
        channelClockLip (fun l => ‖v l‖) K) * t) ≤
      Real.exp (257 * channelClockLip (fun l => ‖v l‖) K * T) := by
    apply Real.exp_le_exp.mpr
    have hKsum := channelClockLip_nonneg (fun l => norm_nonneg (v l)) hK
    nlinarith [ht.2]
  unfold brownianEntropyComparisonGamma
  dsimp [fac]
  calc
    ‖X t - Z t‖ ≤
        channelWeight (fun l => ‖v l‖) * (R + 1024 * q) / N *
          Real.exp (((1 + (256 : ℝ)) *
            channelClockLip (fun l => ‖v l‖) K) * t) := hmain
    _ ≤ channelWeight (fun l => ‖v l‖) *
          ((1 + 1024 * fac) * comparisonTailFactor *
            (R + Real.log N + a)) / N *
          Real.exp (257 * channelClockLip (fun l => ‖v l‖) K * T) := by
      have hS : 0 ≤ channelWeight (fun l => ‖v l‖) :=
        channelWeight_nonneg (fun l => norm_nonneg (v l))
      have hF : 0 ≤ (1 + 1024 * fac) * comparisonTailFactor *
          (R + Real.log N + a) :=
        (by linarith : 0 ≤ R + 1024 * q).trans hfront
      exact mul_le_mul
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfront hS) hN.le)
        hexp (Real.exp_nonneg _) (div_nonneg (mul_nonneg hS hF) hN.le)
    _ = channelWeight (fun l => ‖v l‖) *
          (1 + 1024 * fac) * comparisonTailFactor *
          Real.exp (257 * channelClockLip (fun l => ‖v l‖) K * T) *
          (R + Real.log N + a) / N := by ring

/-! ## Original-law union with an external KMT failure -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Modulus failure for one channel, using the nontrivial tail parameter. -/
def channelBrownianModulusFailure
    (W : ι → ℝ → Ω → ℝ) (H a : ℝ) (l : ι) : Set Ω :=
  brownianEntropyFailure (W l) H (comparisonEntropyTail a)

/-- Some channel violates its Brownian modulus. -/
def anyChannelBrownianModulusFailure
    (W : ι → ℝ → Ω → ℝ) (H a : ℝ) : Set Ω :=
  ⋃ l : ι, channelBrownianModulusFailure W H a l

/-- Per-channel tail is actually `exp (-a)` after shifting to `max a 2`. -/
theorem law_channelBrownianModulusFailure_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ι → ℝ → Ω → ℝ} {H a : ℝ}
    (hH : 1 ≤ H) (ha : 0 ≤ a)
    (hW : ∀ l, DyadicBrownianOn P (W l) H)
    (l : ι) :
    P (channelBrownianModulusFailure W H a l) ≤
      ENNReal.ofReal (Real.exp (-a)) := by
  unfold channelBrownianModulusFailure
  refine (law_brownianEntropyFailure_le_of_two_le
    (lt_of_lt_of_le zero_lt_one hH)
    (le_max_right a 2) (hW l)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact Real.exp_le_exp.mpr (neg_le_neg (le_max_left a 2))

/-- Finite union over the active channels. -/
theorem law_anyChannelBrownianModulusFailure_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ι → ℝ → Ω → ℝ} {H a : ℝ}
    (hH : 1 ≤ H) (ha : 0 ≤ a)
    (hW : ∀ l, DyadicBrownianOn P (W l) H) :
    P (anyChannelBrownianModulusFailure W H a) ≤
      Fintype.card ι * ENNReal.ofReal (Real.exp (-a)) := by
  calc
    P (anyChannelBrownianModulusFailure W H a) ≤
        ∑ l : ι, P (channelBrownianModulusFailure W H a l) := by
      exact measure_iUnion_fintype_le (μ := P) _
    _ ≤ ∑ _l : ι, ENNReal.ofReal (Real.exp (-a)) :=
      Finset.sum_le_sum fun l _ =>
        law_channelBrownianModulusFailure_le hH ha hW l
    _ = Fintype.card ι * ENNReal.ofReal (Real.exp (-a)) := by simp

/-- Named total exceptional set: external KMT failure plus Brownian modulus
failure in at least one channel. -/
def diffusionComparisonFailure
    (kmtFailure : Set Ω)
    (W : ι → ℝ → Ω → ℝ) (H a : ℝ) : Set Ω :=
  kmtFailure ∪ anyChannelBrownianModulusFailure W H a

/-- Original-law failure accounting.  `epsilonKMT` is supplied by the KMT row;
the Brownian contribution is `exp (-a)` per channel. -/
theorem law_diffusionComparisonFailure_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ι → ℝ → Ω → ℝ} {H a : ℝ}
    (kmtFailure : Set Ω) (epsilonKMT : ℝ≥0∞)
    (hKMT : P kmtFailure ≤ epsilonKMT)
    (hH : 1 ≤ H) (ha : 0 ≤ a)
    (hW : ∀ l, DyadicBrownianOn P (W l) H) :
    P (diffusionComparisonFailure kmtFailure W H a) ≤
      epsilonKMT +
        Fintype.card ι * ENNReal.ofReal (Real.exp (-a)) := by
  exact (measure_union_le _ _).trans
    (add_le_add hKMT
      (law_anyChannelBrownianModulusFailure_le hH ha hW))

/-- On the complement of the named failure set, expose the channelwise modulus
needed by `timeChange_diffusion_comparison_of_entropy`. -/
theorem channel_entropy_bound_of_not_failure
    {W : ι → ℝ → Ω → ℝ} {H a : ℝ}
    {kmtFailure : Set Ω} {omega : Ω}
    (hgood : omega ∉ diffusionComparisonFailure kmtFailure W H a) :
    ∀ l u, u ∈ Icc (0 : ℝ) H →
      ∀ w, w ∈ Icc (0 : ℝ) H →
      |W l u omega - W l w omega| ≤
        brownianEntropyBound H (comparisonEntropyTail a) |u - w| := by
  intro l u hu w hw
  have hnot : omega ∉ channelBrownianModulusFailure W H a l := by
    intro hbad
    apply hgood
    exact Or.inr (Set.mem_iUnion.mpr ⟨l, hbad⟩)
  unfold channelBrownianModulusFailure brownianEntropyFailure at hnot
  by_contra hfail
  apply hnot
  exact ⟨u, hu, w, hw, lt_of_not_ge hfail⟩

/-!
THEOREM LIST
* `comparisonEntropyTail`, `comparisonAffineModulus`
* `brownianEntropyComparisonGamma`
* `timeChange_diffusion_comparison_of_entropy`
* `channelBrownianModulusFailure`
* `law_channelBrownianModulusFailure_le`
* `law_anyChannelBrownianModulusFailure_le`
* `diffusionComparisonFailure`
* `law_diffusionComparisonFailure_le`
* `channel_entropy_bound_of_not_failure`

CLOSES
* Conversion of the `BrownianEntropyModulus` modulus to a monotone affine modulus.
* Direct consumption by `DiffusionClockComparison`'s `timeChange_diffusion_comparison_of_affine`.
* Pointwise-in-time form of
  `sup_{t ≤ T} ‖X(t)-Z(t)‖ ≤ Γ_T (R + log N + a) / N`.
* Original-law union with an externally supplied KMT failure set.
* Brownian failure probability `exp (-a)` per channel in the comparison row.

UNFINISHED
* The final model-specific invocation must supply the already-required
  `DiffusionClockComparison` path equations, clock bounds, Lipschitz data, and KMT good-event implication.
  They are intentionally not duplicated as a new stochastic-process structure.
END
-/

end Ripple.Kurtz.StrongApprox

end

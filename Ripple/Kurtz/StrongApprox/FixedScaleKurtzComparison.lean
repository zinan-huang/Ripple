import Ripple.Kurtz.StrongApprox.KurtzTheoremThreeThreeCommon

/-!
# Kurtz Theorem 3.3(a) at a fixed population size

The comparison of Kurtz 1978, Theorem 3.3(a), at one population size `N`.
No family of solution paths indexed by all `N` is assumed.

The deterministic model premises are (3.1), (3.2) and (3.19) at `N`,
together with the limiting-rate bounds `0 ≤ f ≤ eps`. These bounds
follow from the all-`N` model hypotheses by `rate_limit_nonneg` and
`rate_limit_le`, but cannot be inferred from (3.2) at a single `N`.

The stochastic drivers and their KMT and entropy inputs are hypotheses here,
as are the chain and diffusion equations and the path integrability and
continuity of their solutions.
-/

noncomputable section
namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

/-- Explicit code coordinate: sum of KMT errors and common Brownian entropy. -/
def fixedScaleKurtzCode
    {Ω ι : Type*} [Fintype ι]
    (Xi : ι → Ω → ℝ) (W : ι → ℝ → Ω → ℝ)
    (ω : Ω) : ℝ × ℝ :=
  (∑ l, Xi l ω, dyadicEntropyCommonReal W ω)

/-- A fixed, non-random transformation of the two code coordinates. -/
def fixedScaleKurtzFunctional
    (S D Gamma E M T : ℝ) (code : ℝ × ℝ) : ℝ :=
  dyadicCoverBeta S code.1 code.2 D Gamma E M T

/-- This formula contains no population size: the sole random input is
the coded pair (sum of KMT coefficients, common entropy level). -/
def fixedScaleKurtzBeta
    {Ω ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (eps : ι → ℝ)
    (Gamma M T : ℝ) (Xi : ι → Ω → ℝ)
    (W : ι → ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  fixedScaleKurtzFunctional
    (channelWeight (fun l => ‖v l‖))
    (1 + ∑ l, eps l * T) Gamma
    (channelClockLip (fun l => ‖v l‖) eps) M T
    (fixedScaleKurtzCode Xi W ω)

theorem measurable_fixedScaleKurtzCode
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {Xi : ι → Ω → ℝ} {W : ι → ℝ → Ω → ℝ}
    (hXi : ∀ l, Measurable (Xi l))
    (hW : ∀ l t, Measurable (W l t)) :
    Measurable (fixedScaleKurtzCode Xi W) := by
  classical
  exact (Finset.measurable_sum _ fun l _ => hXi l).prodMk
    (measurable_dyadicEntropyCommonReal hW)

theorem measurable_fixedScaleKurtzFunctional
    (S D Gamma E M T : ℝ) :
    Measurable (fixedScaleKurtzFunctional S D Gamma E M T) := by
  unfold fixedScaleKurtzFunctional dyadicCoverBeta
  fun_prop

theorem fixedScaleKurtzBeta_eq_comp
    {Ω ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (eps : ι → ℝ)
    (Gamma M T : ℝ) (Xi : ι → Ω → ℝ)
    (W : ι → ℝ → Ω → ℝ) :
    fixedScaleKurtzBeta v eps Gamma M T Xi W =
      fixedScaleKurtzFunctional
        (channelWeight (fun l => ‖v l‖))
        (1 + ∑ l, eps l * T) Gamma
        (channelClockLip (fun l => ‖v l‖) eps) M T ∘
          fixedScaleKurtzCode Xi W := by
  rfl

/-- The single-scale path hypotheses: only N is mentioned, never an
arbitrary configuration or a universal family of solution paths. -/
def FixedScaleKurtzPaths
    {Ω ι : Type*} [Fintype ι] {d : ℕ}
    (N : ℕ) (f fN : ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (T : ℝ)
    (Y W : ι → ℝ → Ω → ℝ)
    (X Z : Ω → ℝ → Fin d → ℝ)
    (x0 : Ω → Fin d → ℝ) (ω : Ω) : Prop :=
  (∀ l t, t ∈ Icc (0 : ℝ) T →
    IntervalIntegrable (fun s => fN l (X ω s)) volume 0 t) ∧
  (∀ l t, t ∈ Icc (0 : ℝ) T →
    IntervalIntegrable (fun s => f l (X ω s)) volume 0 t) ∧
  (∀ l t, t ∈ Icc (0 : ℝ) T →
    IntervalIntegrable (fun s => f l (Z ω s)) volume 0 t) ∧
  IntegrableOn (fun s => ‖X ω s - Z ω s‖) (Icc (0 : ℝ) T) ∧
  (∀ t ∈ Ico (0 : ℝ) T,
    ContinuousWithinAt (fun s => ‖X ω s - Z ω s‖) (Ioi t) t) ∧
  (∀ t ∈ Icc (0 : ℝ) T,
    X ω t = x0 ω + ∑ l,
      (Y l (scaledTcClock (N : ℝ) fN (X ω) l t) ω /
        (N : ℝ)) • v l) ∧
  (∀ t ∈ Icc (0 : ℝ) T,
    Z ω t = x0 ω +
      (∫ s in (0 : ℝ)..t, tcDrift f v (Z ω s)) + ∑ l,
      (W l (scaledTcClock (N : ℝ) f (Z ω) l t) ω /
        (N : ℝ)) • v l)

/-- A fixed-N version of the deterministic estimate from the existing
all-N lemma. The auxiliary g is *only a family of deterministic rates*:
nothing concerning other N's sample paths is assumed.

The explicitly carried 0 ≤ f ≤ eps bounds have producer: the
all-N rate-model assumptions via rate_limit_nonneg/rate_limit_le.
-/
theorem fixedScale_perturbed_comparison
    {ι : Type*} [Fintype ι] {d : ℕ}
    {N : ℕ} {f fN : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {eps : ι → ℝ}
    {Y W : ι → ℝ → ℝ} {X Z : ℝ → Fin d → ℝ}
    {x0 : Fin d → ℝ} {Gamma M T H R q : ℝ}
    (hN : 2 ≤ N) (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (heps : ∀ l, 0 ≤ eps l)
    (hf0 : ∀ l x, 0 ≤ f l x)
    (hfB : ∀ l x, f l x ≤ eps l)
    (hfN0 : ∀ l x, 0 ≤ fN l x)
    (h31 : ∀ l x, fN l x ≤ eps l)
    (h32 : ∀ l x, |f l x - fN l x| ≤ Gamma * eps l / (N : ℝ))
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hfNX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => fN l (X s)) volume 0 t)
    (hfX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => f l (X s)) volume 0 t)
    (hfZ : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => f l (Z s)) volume 0 t)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    (hurc : ∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt (fun s => ‖X s - Z s‖) (Ioi t) t)
    (hHorizon : ∀ l, (N : ℝ) * (eps l * T) ≤ H)
    (hXeq : ∀ t ∈ Icc (0 : ℝ) T,
      X t = x0 + ∑ l,
        (Y l (scaledTcClock (N : ℝ) fN X l t) / (N : ℝ)) • v l)
    (hZeq : ∀ t ∈ Icc (0 : ℝ) T,
      Z t = x0 + (∫ s in (0 : ℝ)..t, tcDrift f v (Z s)) +
        ∑ l, (W l (scaledTcClock (N : ℝ) f Z l t) / (N : ℝ)) • v l)
    (hKMT : ∀ l u, u ∈ Icc (0 : ℝ) H → |Y l u - u - W l u| ≤ R)
    (hWaff : ∀ l u w, u ∈ Icc (0 : ℝ) H →
      w ∈ Icc (0 : ℝ) H →
      |W l u - W l w| ≤ 1024 * q + 256 * |u - w|)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖X t - Z t‖ ≤
      Real.exp (257 * M * channelClockLip (fun l => ‖v l‖) eps * T) *
      (channelWeight (fun l => ‖v l‖) * R +
        1024 * channelWeight (fun l => ‖v l‖) * q +
        257 * Gamma * channelClockLip (fun l => ‖v l‖) eps * T) /
        (N : ℝ) := by
  classical
  let g : ℕ → ι → (Fin d → ℝ) → ℝ :=
    fun n => if n = N then fN else f
  have hg : g N = fN := by simp [g]
  have hg0 : ∀ n : ℕ, 2 ≤ n → ∀ l x, 0 ≤ g n l x := by
    intro n _ l x
    by_cases hn : n = N
    · simpa [g, hn] using hfN0 l x
    · simpa [g, hn] using hf0 l x
  have hgB : ∀ n : ℕ, 2 ≤ n → ∀ l x, g n l x ≤ eps l := by
    intro n _ l x
    by_cases hn : n = N
    · simpa [g, hn] using h31 l x
    · simpa [g, hn] using hfB l x
  have hgErr : ∀ n : ℕ, 2 ≤ n → ∀ l x,
      |f l x - g n l x| ≤ Gamma * eps l / (n : ℝ) := by
    intro n _ l x
    by_cases hn : n = N
    · subst n
      simpa [g] using h32 l x
    · simp only [g, if_neg hn, sub_self, abs_zero]
      exact div_nonneg (mul_nonneg hGamma (heps l)) (Nat.cast_nonneg _)
  exact perturbed_diffusion_comparison
    (f := f) (fN := g) (v := v) (eps := eps)
    (Y := Y) (W := W) (X := X) (Z := Z) (xZero := x0)
    hN hGamma hM hT hR hq heps hf0 hg0 hgB hgErr h319
    (by simpa [g] using hfNX) hfX hfZ huint hurc hHorizon
    (by simpa [g] using hXeq) hZeq hKMT hWaff ht

/-- Fixed-N version of Theorem 3.3(a) on an arbitrary probability
space. The coefficient is specified exactly, not merely existentially.
The conclusion is pointwise for every t on one conull set, hence also
controls the supremum on [0,T]. -/
theorem finiteChannelKurtz_at
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ)
    (f fN : ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (eps : ι → ℝ)
    (Gamma M T : ℝ)
    (Y W : ι → ℝ → Ω → ℝ) (Xi : ι → Ω → ℝ)
    (X Z : Ω → ℝ → Fin d → ℝ)
    (x0 : Ω → Fin d → ℝ)
    (hN : 2 ≤ N) (heps : ∀ l, 0 ≤ eps l)
    (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hf0 : ∀ l x, 0 ≤ f l x)
    (hfB : ∀ l x, f l x ≤ eps l)
    (hfN0 : ∀ l x, 0 ≤ fN l x)
    (h31 : ∀ l x, fN l x ≤ eps l)
    (h32 : ∀ l x, |f l x - fN l x| ≤ Gamma * eps l / (N : ℝ))
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hW : ∀ l j, DyadicBrownianOn P (W l) ((2 : ℝ) ^ (j : ℕ)))
    (hXiMeas : ∀ l, Measurable (Xi l))
    (hXi0 : ∀ l ω, 0 ≤ Xi l ω)
    (hXiExp : ∀ l, HasPositiveExpMoment P (Xi l))
    (hKMT : ∀ᵐ ω ∂P, ∀ l u, 0 ≤ u →
      |Y l u ω - u - W l u ω| ≤ Xi l ω * Real.log (max 2 u))
    (hPaths : ∀ᵐ ω ∂P,
      FixedScaleKurtzPaths N f fN v T Y W X Z x0 ω) :
    let betaN := fixedScaleKurtzBeta v eps Gamma M T Xi W
    Measurable betaN ∧
      (∀ ω, 0 ≤ betaN ω) ∧
      HasPositiveExpMoment P betaN ∧
      (∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
        ‖X ω t - Z ω t‖ ≤
          betaN ω * Real.log (N : ℝ) / (N : ℝ)) := by
  classical
  dsimp
  let S := channelWeight (fun l => ‖v l‖)
  let E := channelClockLip (fun l => ‖v l‖) eps
  let D := 1 + ∑ l, eps l * T
  let K := fun ω => ∑ l, Xi l ω
  let A := dyadicEntropyCommonReal W
  let betaN := fun ω => dyadicCoverBeta S (K ω) (A ω) D Gamma E M T
  have hS : 0 ≤ S := channelWeight_nonneg (fun l => norm_nonneg (v l))
  have hE : 0 ≤ E := channelClockLip_nonneg (fun l => norm_nonneg (v l)) heps
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun l _ => mul_nonneg (heps l) hT)
  have hclockD : ∀ l, eps l * T ≤ D := by
    intro l
    have hle := Finset.single_le_sum
      (fun k (_ : k ∈ Finset.univ) => mul_nonneg (heps k) hT)
      (Finset.mem_univ l)
    dsimp [D]
    linarith
  have hKmeas : Measurable K :=
    Finset.measurable_sum _ fun l _ => hXiMeas l
  have hKn : ∀ ω, 0 ≤ K ω :=
    fun ω => Finset.sum_nonneg fun l _ => hXi0 l ω
  have hAmeas : Measurable A :=
    measurable_dyadicEntropyCommonReal
      fun l => (hW l 0).eval_measurable
  have hAn : ∀ ω, 0 ≤ A ω := dyadicEntropyCommonReal_nonneg W
  have hKm : HasPositiveExpMoment P K :=
    positiveExpMoment_sum hXiMeas hXi0 hXiExp
  have hAm : HasPositiveExpMoment P A :=
    ⟨1 / 2, by norm_num,
      (integral_exp_dyadicEntropyCommonReal_le hW
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).1⟩
  have hbetaEq :
      fixedScaleKurtzBeta v eps Gamma M T Xi W = betaN := by
    rfl
  rw [hbetaEq]
  refine ⟨measurable_dyadicCoverBeta hKmeas hAmeas S D Gamma E M T,
    (fun ω => dyadicCoverBeta_nonneg hS (hKn ω) (hAn ω)
      hD hGamma hE hT),
    positiveExpMoment_dyadicCoverBeta hKmeas hAmeas hKn hAn
      hKm hAm hS hD hGamma hE hT, ?_⟩
  filter_upwards
    [hKMT, hPaths, brownianEntropyBound_of_commonLevel_ae hW]
    with ω hcoupling hpaths hentropy
  intro t ht
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨j, hjlo, hjhi⟩ := exists_dyadic_cover_nat hN hD
  have hadm := dyadicCover_affineBudget_admissible
    hNr hD (hAn ω) hjlo
  have hHtwo : (2 : ℝ) ≤ (2 : ℝ) ^ j := by
    have hND : (N : ℝ) ≤ (N : ℝ) * D := by
      nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
    linarith
  have hHpos : (0 : ℝ) < (2 : ℝ) ^ j :=
    pow_pos (by norm_num) j
  have hR : 0 ≤ K ω * Real.log ((2 : ℝ) ^ j) :=
    mul_nonneg (hKn ω) (Real.log_nonneg (by linarith))
  have hq : 0 ≤ dyadicCoverAffineBudget ((2 : ℝ) ^ j) (A ω) j := by
    linarith [hadm.2.1]
  have hXiK : ∀ l, Xi l ω ≤ K ω := fun l =>
    Finset.single_le_sum
      (fun k (_ : k ∈ Finset.univ) => hXi0 k ω)
      (Finset.mem_univ l)
  have hcouplingH : ∀ l u,
      u ∈ Icc (0 : ℝ) ((2 : ℝ) ^ j) →
      |Y l u ω - u - W l u ω| ≤
        K ω * Real.log ((2 : ℝ) ^ j) := by
    intro l u hu
    have hmax : max (2 : ℝ) u ≤ (2 : ℝ) ^ j :=
      max_le hHtwo hu.2
    have hlog : Real.log (max (2 : ℝ) u) ≤
        Real.log ((2 : ℝ) ^ j) :=
      Real.log_le_log
        (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) hmax
    exact (hcoupling l u hu.1).trans
      ((mul_le_mul_of_nonneg_left hlog (hXi0 l ω)).trans
        (mul_le_mul_of_nonneg_right (hXiK l)
          (Real.log_nonneg (by linarith))))
  have hWaff : ∀ l u w,
      u ∈ Icc (0 : ℝ) ((2 : ℝ) ^ j) →
      w ∈ Icc (0 : ℝ) ((2 : ℝ) ^ j) →
      |W l u ω - W l w ω| ≤
        1024 * dyadicCoverAffineBudget ((2 : ℝ) ^ j) (A ω) j +
          256 * |u - w| := by
    intro l u w hu hw
    have habs : |u - w| ∈ Icc (0 : ℝ) ((2 : ℝ) ^ j) :=
      ⟨abs_nonneg _,
        abs_sub_le_iff.mpr
          ⟨by linarith [hu.1, hu.2, hw.1, hw.2],
           by linarith [hu.1, hu.2, hw.1, hw.2]⟩⟩
    have hmod := hentropy.2.2.2 l j u hu w hw
    have hparam :
        2 + A ω + dyadicEntropyPenalty j =
          dyadicCoverEntropy (A ω) j := by
      dsimp [dyadicEntropyPenalty, dyadicCoverEntropy]
      push_cast
      ring
    rw [hparam] at hmod
    exact hmod.trans
      (brownianEntropyBound_le_cover_affine hHpos hNr
        hadm.1 hadm.2.1 hadm.2.2.1 hadm.2.2.2 habs)
  obtain ⟨hfNX, hfX, hfZ, huint, hurc, hXeq, hZeq⟩ := hpaths
  have hmain := fixedScale_perturbed_comparison
    (f := f) (fN := fN) (v := v) (eps := eps)
    (Y := fun l u => Y l u ω) (W := fun l u => W l u ω)
    (X := X ω) (Z := Z ω) (x0 := x0 ω)
    hN hGamma hM hT hR hq heps hf0 hfB hfN0 h31 h32 h319
    hfNX hfX hfZ huint hurc
    (fun l =>
      (mul_le_mul_of_nonneg_left (hclockD l)
        (Nat.cast_nonneg N)).trans hjlo)
    hXeq hZeq hcouplingH hWaff ht
  exact dyadicCover_comparison_le_beta hNr hD
    (hAn ω) (hKn ω) hS hGamma hE hT hjlo hjhi hmain

/-- Identical code laws give identical beta laws.
No independence between channels is needed; the hypothesis concerns their
joint *sufficient-statistic* code, not just the separate marginal laws. -/
theorem fixedScaleKurtzBeta_law_of_code_law
    {Ω₁ Ω₂ ι : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [Fintype ι]
    {d : ℕ}
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (v : ι → Fin d → ℝ) (eps : ι → ℝ)
    (Gamma M T : ℝ)
    (Xi₁ : ι → Ω₁ → ℝ) (W₁ : ι → ℝ → Ω₁ → ℝ)
    (Xi₂ : ι → Ω₂ → ℝ) (W₂ : ι → ℝ → Ω₂ → ℝ)
    (hXi₁ : ∀ l, Measurable (Xi₁ l))
    (hXi₂ : ∀ l, Measurable (Xi₂ l))
    (hW₁ : ∀ l t, Measurable (W₁ l t))
    (hW₂ : ∀ l t, Measurable (W₂ l t))
    (hCode : Measure.map (fixedScaleKurtzCode Xi₁ W₁) P₁ =
      Measure.map (fixedScaleKurtzCode Xi₂ W₂) P₂) :
    Measure.map (fixedScaleKurtzBeta v eps Gamma M T Xi₁ W₁) P₁ =
      Measure.map (fixedScaleKurtzBeta v eps Gamma M T Xi₂ W₂) P₂ := by
  let S := channelWeight (fun l => ‖v l‖)
  let D := 1 + ∑ l, eps l * T
  let E := channelClockLip (fun l => ‖v l‖) eps
  let F := fixedScaleKurtzFunctional S D Gamma E M T
  have hF : Measurable F :=
    measurable_fixedScaleKurtzFunctional S D Gamma E M T
  have hC₁ : Measurable (fixedScaleKurtzCode Xi₁ W₁) :=
    measurable_fixedScaleKurtzCode hXi₁ hW₁
  have hC₂ : Measurable (fixedScaleKurtzCode Xi₂ W₂) :=
    measurable_fixedScaleKurtzCode hXi₂ hW₂
  change Measure.map (F ∘ fixedScaleKurtzCode Xi₁ W₁) P₁ =
    Measure.map (F ∘ fixedScaleKurtzCode Xi₂ W₂) P₂
  rw [← Measure.map_map hF hC₁, ← Measure.map_map hF hC₂, hCode]

end Ripple.Kurtz.StrongApprox
end

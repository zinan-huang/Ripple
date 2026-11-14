import Ripple.Kurtz.StrongApprox.SectionFourUTailKurtz
import Ripple.Stochastic.StrongSDEGlobal

/-!
# Kurtz's diffusion as a strong solution on the channel space

For the Kurtz rates `f_l` with `0 ≤ f_l ≤ ε_l`, the Lipschitz condition (3.19), and the
square-root condition `|sqrt f_l x - sqrt f_l y| ≤ Lg_l ‖x - y‖`, the finite-channel SDE

`Z t = x₀ + Σ_l (M_l t / N) v_l + ∫₀ᵗ F (Z s) ds`,  `M_l = ∫ sqrt (N f_l (Z)) dW_l`,

with drift `F = tcDrift f v`, has for every `N ≥ 2` a solution on the channel space
`channelKMTSpace (Fin m)` driven by the channel Brownian motions `W_l` and adapted to the
augmented channel filtration. The solution has continuous paths for every sample and solves
the SDE on every horizon `T`, almost surely, in the form `KurtzSDEPathsNN` used by the
Section 4 estimates.

The construction applies the global strong-solution theorem
`StrongSDEGlobal.exists_all_time_solution` with the state space `Fin d → ℝ`, the bounded
Lipschitz diffusion coefficients `g_l = sqrt ∘ f_l` and the bounded Lipschitz drift
`tcDrift f v`. Its all-time equation restricts to the window `[0,T]`
(`StrongSDEGlobal.globalEquation_on_integer`, `StrongSDEGlobal.equation_restrict`). The window
integral `windowIto` is the continuous Itô integral `continuousItoOfFun`
(`windowIto_eq_continuousItoOfFun`), and the scaling `N^{-1/2}` turns into `M_l / N` by scalar
linearity (`kurtzSDEPathsNN_of_continuousIto_rates`).

`sectionFour_U_tail_kurtz_strong` is the `U_N` tail for these solutions: its premises are the
model conditions on the rates, the square-root condition, and the fluid-limit equation; no SDE
premise remains.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox

open Ripple.Stochastic Ripple.Stochastic.ContinuousItoLinear
open Ripple.Stochastic.FilteredItoIntegralCLM
open SectionFourAssembly

/-! ## The window integral is the continuous Itô integral -/

section Window

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} [IsFilteredPreBrownian B F μ]

/-- The total window integral of the strong-solution construction and the continuous Itô
integral of a function are the same operator: both read the continuous representative of the
predictable `L²` class stopped at the horizon, and both are `0` outside that class. -/
theorem windowIto_eq_continuousItoOfFun (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t)) :
    StrongSDEConcreteMaps.windowIto (μ := μ) F T B hB hBmeas =
      continuousItoOfFun μ F T hB hBmeas := by
  funext H t ω
  by_cases hm : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)
  · rw [continuousItoOfFun_of_memLp T hB hBmeas hm]
    simp only [StrongSDEConcreteMaps.windowIto, dif_pos hm]
    rfl
  · unfold continuousItoOfFun
    rw [dif_neg hm]
    simp only [StrongSDEConcreteMaps.windowIto, dif_neg hm]

end Window

/-! ## The coefficients -/

section Coefficients

variable {m d : ℕ} {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
  {M : ℝ}

/-- The square-root condition makes each diffusion coefficient `sqrt ∘ f_l` Lipschitz. -/
theorem lipschitzWith_sqrt_rate (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖) (l : Fin m) :
    LipschitzWith (Lg l) (fun x => Real.sqrt (f l x)) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, dist_eq_norm]
    exact hLg l x y

/-- The diffusion coefficients are bounded by `sqrt ε_l`. -/
theorem abs_sqrt_rate_le (hfB : ∀ l x, f l x ≤ eps l) (l : Fin m) (x : Fin d → ℝ) :
    |Real.sqrt (f l x)| ≤ Real.sqrt (eps l) := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (hfB l x)

/-- (3.19) makes the drift Lipschitz with constant `M Σ_l ‖v_l‖ ε_l`. -/
theorem lipschitzWith_tcDrift (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) :
    LipschitzWith (kurtzDriftLip v eps M).toNNReal (tcDrift f v) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.coe_toNNReal _ (kurtzDriftLip_nonneg heps hM), dist_eq_norm, dist_eq_norm]
    exact norm_tcDrift_sub_le h319 x y

/-- The drift is bounded by `Σ_l ε_l ‖v_l‖`. -/
theorem norm_tcDrift_le (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (x : Fin d → ℝ) : ‖tcDrift f v x‖ ≤ ∑ l, eps l * ‖v l‖ := by
  unfold tcDrift
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf0 l x)]
  exact mul_le_mul_of_nonneg_right (hfB l x) (norm_nonneg _)

end Coefficients

/-! ## The strong solution on the channel space -/

section Channel

attribute [local instance] channelBrownian_isFilteredPreBrownian_augmented

variable {m d : ℕ} {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
  {M : ℝ}

/-- **Kurtz's SDE has a strong solution for every `N ≥ 2`.** On the channel space, with the
channel Brownian motions and the augmented channel filtration, there is a process `Z` adapted
to that filtration, with continuous paths for every sample and finite second path moments on
every compact window, which solves the SDE `KurtzSDEPathsNN` with the noise integrals
`channelRateIntegral T N f Z = ∫ sqrt (N f_l (Z)) dW_l` on every horizon `T`, almost surely. -/
theorem exists_kurtz_strong_solution (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ,
      (∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t)) ∧
      (∀ ω, Continuous fun t => Z t ω) ∧
      (∀ T : ℝ≥0, Integrable (fun ω => ⨆ t : StrongSDEConcreteMaps.Window T,
        ‖Z t.val ω‖ ^ 2) (channelKMTMeasure (Fin m))) ∧
      ∀ T : ℝ≥0, ∀ᵐ ω ∂channelKMTMeasure (Fin m),
        KMTTransfer.KurtzSDEPathsNN N f v T Z (channelRateIntegral T N f Z) (fun _ => x0) ω := by
  have hf := continuous_rate_of_lip heps hM h319
  have hLip := lipschitzWith_sqrt_rate Lg hLg
  have hK := abs_sqrt_rate_le hfB
  have hb := lipschitzWith_tcDrift (v := v) heps hM h319
  have hC : 0 ≤ ∑ l, eps l * ‖v l‖ :=
    Finset.sum_nonneg fun l _ => mul_nonneg (heps l) (norm_nonneg _)
  have hbC := norm_tcDrift_le (v := v) hf0 hfB
  have hN1 : 1 ≤ N := by omega
  obtain ⟨Z, hZa, hZc, hZm, hZE⟩ := StrongSDEGlobal.exists_all_time_solution
    (μ := channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration channelBrownian
    channelBrownian_continuous measurable_channelBrownian augmentedChannelBrownianFiltration_null
    v (fun l x => Real.sqrt (f l x)) Lg hLip (fun l => Real.sqrt (eps l)) hK
    (tcDrift f v) (kurtzDriftLip v eps M).toNNReal hb (∑ l, eps l * ‖v l‖) hC hbC x0 N hN1
  refine ⟨Z, fun t => (hZa t).measurable, hZc, hZm, fun T => ?_⟩
  have hn := StrongSDEGlobal.globalEquation_on_integer (μ := channelKMTMeasure (Fin m))
    augmentedChannelBrownianFiltration channelBrownian
    channelBrownian_continuous measurable_channelBrownian augmentedChannelBrownianFiltration_null
    v (fun l x => Real.sqrt (f l x)) Lg hLip (fun l => Real.sqrt (eps l)) hK
    (tcDrift f v) (kurtzDriftLip v eps M).toNNReal hb (∑ l, eps l * ‖v l‖) hC hbC x0 N Z hZa
    (ae_of_all _ hZc) hZE (ConsistentHorizonProcess.horizon T)
  have hT := StrongSDEGlobal.equation_restrict (μ := channelKMTMeasure (Fin m))
    augmentedChannelBrownianFiltration channelBrownian
    channelBrownian_continuous measurable_channelBrownian augmentedChannelBrownianFiltration_null
    v (fun l x => Real.sqrt (f l x)) Lg hLip (fun l => Real.sqrt (eps l)) hK
    (tcDrift f v) (kurtzDriftLip v eps M).toNNReal hb (∑ l, eps l * ‖v l‖) hC hbC x0
    (ConsistentHorizonProcess.le_horizon T) N Z hZa hZc hn
  unfold StrongSDEGlobal.Equation at hT
  simp only [windowIto_eq_continuousItoOfFun] at hT
  exact kurtzSDEPathsNN_of_continuousIto_rates channelBrownian_continuous
    measurable_channelBrownian augmentedChannelBrownianFiltration_null (by omega) hf hfB
    (fun t => (hZa t).measurable) (ae_of_all _ hZc) hT

/-- One strong solution `Z_N` for every `N ≥ 2`, on the same channel space, with the same
Brownian drivers. For `N < 2` the process is `0`, so adaptation and continuity hold for all
`N`. -/
theorem exists_kurtz_strong_solution_family (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) :
    ∃ Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ,
      (∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t)) ∧
      (∀ N ω, Continuous fun t => Z N t ω) ∧
      (∀ N, 2 ≤ N → ∀ T : ℝ≥0, Integrable (fun ω => ⨆ t : StrongSDEConcreteMaps.Window T,
        ‖Z N t.val ω‖ ^ 2) (channelKMTMeasure (Fin m))) ∧
      ∀ N, 2 ≤ N → ∀ T : ℝ≥0, ∀ᵐ ω ∂channelKMTMeasure (Fin m),
        KMTTransfer.KurtzSDEPathsNN N f v T (Z N) (channelRateIntegral T N f (Z N))
          (fun _ => x0) ω := by
  classical
  have hex := fun N (hN : 2 ≤ N) =>
    exists_kurtz_strong_solution (v := v) heps hM hf0 hfB h319 Lg hLg x0 hN
  let Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ := fun N =>
    if hN : 2 ≤ N then Classical.choose (hex N hN) else fun _ _ => 0
  have hZ : ∀ N (hN : 2 ≤ N), Z N = Classical.choose (hex N hN) := fun N hN => dif_pos hN
  have hZ0 : ∀ N, ¬ 2 ≤ N → Z N = fun _ _ => 0 := fun N hN => dif_neg hN
  refine ⟨Z, ?_, ?_, ?_, ?_⟩
  · intro N t
    by_cases hN : 2 ≤ N
    · rw [hZ N hN]
      exact (Classical.choose_spec (hex N hN)).1 t
    · rw [hZ0 N hN]
      exact measurable_const
  · intro N ω
    by_cases hN : 2 ≤ N
    · rw [hZ N hN]
      exact (Classical.choose_spec (hex N hN)).2.1 ω
    · rw [hZ0 N hN]
      exact continuous_const
  · intro N hN T
    rw [hZ N hN]
    exact (Classical.choose_spec (hex N hN)).2.2.1 T
  · intro N hN T
    rw [hZ N hN]
    exact (Classical.choose_spec (hex N hN)).2.2.2 T

/-- **The `U_N` tail for Kurtz's strong solutions.** There are strong solutions `Z_N`, `N ≥ 2`,
of Kurtz's SDE on the channel space (adapted, continuous, solving the SDE on every horizon) such
that for every horizon `T`, every `Q ≥ T Σ_l ‖v_l‖² ε_l` with `Q > 0`, and every fluid limit `X`
from `x0`, `P (r < U_N) ≤ a_U exp (-b_U r²)` for all `N ≥ 2` and `r ≥ 0`, with
`a_U = 2 max (1, d)` and `b_U = 1 / (2 e^{2 L T} Q)`, `L = M Σ_l ‖v_l‖ ε_l`. The premises are
the model conditions on the rates and the square-root condition; the SDE is constructed. -/
theorem sectionFour_U_tail_kurtz_strong (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) :
    ∃ Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ,
      (∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t)) ∧
      (∀ N ω, Continuous fun t => Z N t ω) ∧
      (∀ N, 2 ≤ N → ∀ T : ℝ≥0, ∀ᵐ ω ∂channelKMTMeasure (Fin m),
        KMTTransfer.KurtzSDEPathsNN N f v T (Z N) (channelRateIntegral T N f (Z N))
          (fun _ => x0) ω) ∧
      ∀ (T : ℝ≥0) (Q : ℝ), sectionFourQZero v eps T ≤ Q → 0 < Q →
        ∀ X : ℝ≥0 → Fin d → ℝ, Continuous X →
        (∀ t ≤ T, X t = x0 + ∫ s in (0 : ℝ)..(t : ℝ), tcDrift f v (X s.toNNReal)) →
        ∀ N, 2 ≤ N → ∀ r : ℝ, 0 ≤ r →
          channelKMTMeasure (Fin m) {ω | r < sectionFourRemainderU N X (Z N) T ω} ≤
            ENNReal.ofReal (sectionFourAU d *
              Real.exp (-sectionFourBU (Real.exp (kurtzDriftLip v eps M * T)) Q * r ^ 2)) := by
  obtain ⟨Z, hZa, hZc, -, hSDE⟩ :=
    exists_kurtz_strong_solution_family (v := v) heps hM hf0 hfB h319 Lg hLg x0
  refine ⟨Z, hZa, hZc, hSDE, ?_⟩
  intro T Q hQ hQpos X hX hXeq
  exact sectionFour_U_tail_kurtz heps hM hf0 hfB h319 hQ hQpos hX hXeq hZa
    (fun N hN => hSDE N hN T)

end Channel

end Ripple.Kurtz.StrongApprox

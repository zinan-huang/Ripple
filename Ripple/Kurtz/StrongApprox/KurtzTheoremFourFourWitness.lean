import Ripple.Kurtz.StrongApprox.KurtzKnightTimeChange

/-!
# A model satisfying the hypotheses of Kurtz's Theorem 4.4

The state is one-dimensional (`Fin 1 → ℝ`), with two channels: direction `+1` at rate
`f₊ x = 2 + sin x` and direction `-1` at rate `f₋ x = 2`. Then `1 ≤ f ≤ ε` with `ε = (3, 2)`,
the rates are `1`-Lipschitz, so (3.19) holds with `M = 1`, and the square roots are
`1`-Lipschitz because `f ≥ 1`. The population rates are `f_N = f`, so (3.2) holds with
`Γ = 0`. The drift is `F x = sin x`, with derivative `F' x h = cos x · h`, so `‖F'‖ ≤ 1` and
`F'` is `1`-Lipschitz.

`kurtz_theorem_four_four_witness` is `kurtz_theorem_four_four_channel` applied to this model:
the hypotheses of the theorem are jointly satisfiable by a model with a state-dependent rate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox

/-- The rates `f₊ x = 2 + sin x`, `f₋ x = 2`. -/
def witnessRate : Fin 2 → (Fin 1 → ℝ) → ℝ := ![fun x => 2 + Real.sin (x 0), fun _ => 2]

/-- The jump directions `+1`, `-1`. -/
def witnessDir : Fin 2 → Fin 1 → ℝ := ![fun _ => 1, fun _ => -1]

/-- The rate bounds `ε = (3, 2)`. -/
def witnessEps : Fin 2 → ℝ := ![3, 2]

/-- The square-root Lipschitz constants. -/
def witnessLg : Fin 2 → ℝ≥0 := fun _ => 1

/-- The derivative `h ↦ cos (x 0) · h 0` of the drift `x ↦ sin (x 0)`. -/
def witnessDeriv (x : Fin 1 → ℝ) : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
  (Real.cos (x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight
    (fun _ : Fin 1 => (1 : ℝ))

theorem abs_apply_zero_le (x : Fin 1 → ℝ) : |x 0| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]
  exact norm_le_pi_norm x 0

theorem witnessEps_nonneg (l : Fin 2) : 0 ≤ witnessEps l := by
  fin_cases l
  · show (0 : ℝ) ≤ 3
    norm_num
  · show (0 : ℝ) ≤ 2
    norm_num

theorem one_le_witnessRate (l : Fin 2) (x : Fin 1 → ℝ) : 1 ≤ witnessRate l x := by
  fin_cases l
  · show (1 : ℝ) ≤ 2 + Real.sin (x 0)
    linarith [Real.neg_one_le_sin (x 0)]
  · show (1 : ℝ) ≤ 2
    norm_num

theorem witnessRate_nonneg (l : Fin 2) (x : Fin 1 → ℝ) : 0 ≤ witnessRate l x :=
  zero_le_one.trans (one_le_witnessRate l x)

theorem witnessRate_le (l : Fin 2) (x : Fin 1 → ℝ) : witnessRate l x ≤ witnessEps l := by
  fin_cases l
  · show 2 + Real.sin (x 0) ≤ 3
    linarith [Real.sin_le_one (x 0)]
  · show (2 : ℝ) ≤ 2
    exact le_rfl

theorem witnessRate_measurable (l : Fin 2) : Measurable (witnessRate l) := by
  fin_cases l
  · show Measurable fun x : Fin 1 → ℝ => 2 + Real.sin (x 0)
    exact measurable_const.add (Real.measurable_sin.comp (measurable_pi_apply 0))
  · show Measurable fun _ : Fin 1 → ℝ => (2 : ℝ)
    exact measurable_const

/-- (3.19) with `M = 1`. -/
theorem witnessRate_lip (l : Fin 2) (x y : Fin 1 → ℝ) :
    |witnessRate l x - witnessRate l y| ≤ witnessEps l * 1 * ‖x - y‖ := by
  have hxy : |x 0 - y 0| ≤ ‖x - y‖ := abs_apply_zero_le (x - y)
  fin_cases l
  · show |2 + Real.sin (x 0) - (2 + Real.sin (y 0))| ≤ 3 * 1 * ‖x - y‖
    rw [show 2 + Real.sin (x 0) - (2 + Real.sin (y 0)) = Real.sin (x 0) - Real.sin (y 0) by
      ring]
    have := Real.abs_sin_sub_sin_le (x 0) (y 0)
    linarith [norm_nonneg (x - y)]
  · show |(2 : ℝ) - 2| ≤ 2 * 1 * ‖x - y‖
    rw [sub_self, abs_zero]
    positivity

theorem abs_sqrt_sub_sqrt_le_of_one_le {u w : ℝ} (hu : 1 ≤ u) (hw : 1 ≤ w) :
    |Real.sqrt u - Real.sqrt w| ≤ |u - w| := by
  have hsu := Real.sq_sqrt (zero_le_one.trans hu)
  have hsw := Real.sq_sqrt (zero_le_one.trans hw)
  have h1 : 1 ≤ Real.sqrt u := Real.one_le_sqrt.2 hu
  have h2 : 0 ≤ Real.sqrt w := Real.sqrt_nonneg w
  have key : |u - w| = |Real.sqrt u - Real.sqrt w| * (Real.sqrt u + Real.sqrt w) := by
    rw [← abs_of_nonneg (by linarith : 0 ≤ Real.sqrt u + Real.sqrt w), ← abs_mul]
    congr 1
    linear_combination (-1 : ℝ) * hsu + hsw
  rw [key]
  exact le_mul_of_one_le_right (abs_nonneg _) (by linarith)

/-- The square-root condition with `Lg = 1`. -/
theorem witnessRate_sqrt_lip (l : Fin 2) (x y : Fin 1 → ℝ) :
    |Real.sqrt (witnessRate l x) - Real.sqrt (witnessRate l y)| ≤ witnessLg l * ‖x - y‖ := by
  have hxy : |x 0 - y 0| ≤ ‖x - y‖ := abs_apply_zero_le (x - y)
  have hs := abs_sqrt_sub_sqrt_le_of_one_le (one_le_witnessRate l x) (one_le_witnessRate l y)
  have hL : ((witnessLg l : ℝ≥0) : ℝ) = 1 := rfl
  rw [hL, one_mul]
  refine hs.trans ?_
  fin_cases l
  · show |2 + Real.sin (x 0) - (2 + Real.sin (y 0))| ≤ ‖x - y‖
    rw [show 2 + Real.sin (x 0) - (2 + Real.sin (y 0)) = Real.sin (x 0) - Real.sin (y 0) by
      ring]
    exact (Real.abs_sin_sub_sin_le (x 0) (y 0)).trans hxy
  · show |(2 : ℝ) - 2| ≤ ‖x - y‖
    rw [sub_self, abs_zero]
    exact norm_nonneg _

theorem witness_tcDrift (x : Fin 1 → ℝ) :
    tcDrift witnessRate witnessDir x = Real.sin (x 0) • (fun _ : Fin 1 => (1 : ℝ)) := by
  funext i
  show (∑ l, witnessRate l x • witnessDir l) i = Real.sin (x 0) * 1
  rw [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  show (2 + Real.sin (x 0)) • (1 : ℝ) + (2 : ℝ) • (-1 : ℝ) = Real.sin (x 0) * 1
  simp only [smul_eq_mul]
  ring

theorem witnessDeriv_hasFDerivAt (x : Fin 1 → ℝ) :
    HasFDerivAt (tcDrift witnessRate witnessDir) (witnessDeriv x) x := by
  have h := ((Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 1 => ℝ) 0 x)).smul_const
      (fun _ : Fin 1 => (1 : ℝ))
  have hfun : tcDrift witnessRate witnessDir =
      fun y => (Real.sin ∘ fun f : Fin 1 → ℝ => f 0) y • (fun _ : Fin 1 => (1 : ℝ)) :=
    funext witness_tcDrift
  rw [hfun]
  exact h

theorem witnessDeriv_apply (x h : Fin 1 → ℝ) :
    witnessDeriv x h = (Real.cos (x 0) * h 0) • (fun _ : Fin 1 => (1 : ℝ)) := by
  simp [witnessDeriv]

theorem norm_smul_ones (r : ℝ) : ‖r • (fun _ : Fin 1 => (1 : ℝ))‖ = |r| := by
  rw [norm_smul, pi_norm_const, norm_one, mul_one, Real.norm_eq_abs]

theorem witnessDeriv_norm_le (x : Fin 1 → ℝ) : ‖witnessDeriv x‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => ?_
  rw [witnessDeriv_apply, norm_smul_ones, abs_mul]
  exact mul_le_mul (Real.abs_cos_le_one _) (abs_apply_zero_le h) (abs_nonneg _) zero_le_one

theorem witnessDeriv_lip (x y : Fin 1 → ℝ) :
    ‖witnessDeriv y - witnessDeriv x‖ ≤ 1 * ‖y - x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [ContinuousLinearMap.sub_apply, witnessDeriv_apply, witnessDeriv_apply, ← sub_smul,
    ← sub_mul, norm_smul_ones, abs_mul, one_mul]
  exact mul_le_mul ((Real.abs_cos_sub_cos_le _ _).trans (abs_apply_zero_le (y - x)))
    (abs_apply_zero_le h) (abs_nonneg _) (norm_nonneg _)

theorem witnessRateFamily_nonneg :
    ∀ N : ℕ, 2 ≤ N → ∀ l x, 0 ≤ (fun _ : ℕ => witnessRate) N l x :=
  fun _ _ l x => witnessRate_nonneg l x

theorem witnessRateFamily_le :
    ∀ N : ℕ, 2 ≤ N → ∀ l x, (fun _ : ℕ => witnessRate) N l x ≤ witnessEps l :=
  fun _ _ l x => witnessRate_le l x

theorem witnessRateFamily_measurable :
    ∀ N : ℕ, 2 ≤ N → ∀ l, Measurable ((fun _ : ℕ => witnessRate) N l) :=
  fun _ _ l => witnessRate_measurable l

/-- (3.2) with `Γ = 0`. -/
theorem witnessRateFamily_close :
    ∀ N : ℕ, 2 ≤ N → ∀ l x,
      |witnessRate l x - (fun _ : ℕ => witnessRate) N l x| ≤ 0 * witnessEps l / (N : ℝ) := by
  intro N _ l x
  simp

/-- **Kurtz's Theorem 4.4 for the witness model.** The conclusion of
`kurtz_theorem_four_four_channel` for the two-channel model with rates `2 + sin x` and `2`:
its hypotheses are jointly satisfiable by a model with a state-dependent rate. -/
theorem kurtz_theorem_four_four_witness (x0 : Fin 1 → ℝ) :
    ∃ Z : ℕ → ℝ≥0 → channelKMTSpace (Fin 2) → Fin 1 → ℝ,
      (∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t)) ∧
      (∀ N ω, Continuous fun t => Z N t ω) ∧
      (∀ N, 2 ≤ N → ∀ T : ℝ≥0, ∀ᵐ ω ∂channelKMTMeasure (Fin 2),
        KMTTransfer.KurtzSDEPathsNN N witnessRate witnessDir T (Z N)
          (channelRateIntegral T N witnessRate (Z N)) (fun _ => x0) ω) ∧
      ∃ (β : ℕ → Fin 2 → ℝ≥0 → channelKMTSpace (Fin 2) × channelKMTSpace (Fin 2) → ℝ)
        (hβ : ∀ N l t, Measurable (β N l t)),
        (∀ N, 2 ≤ N → ∀ l,
          IsPreBrownian (β N l) ((channelKMTMeasure (Fin 2)).prod (channelKMTMeasure (Fin 2)))) ∧
        (∀ N, 2 ≤ N → iIndepFun (fun (l : Fin 2) p => fun t => β N l t p)
          ((channelKMTMeasure (Fin 2)).prod (channelKMTMeasure (Fin 2)))) ∧
        (∀ N, 2 ≤ N → ∀ T : ℝ≥0,
          ∀ᵐ p ∂(channelKMTMeasure (Fin 2)).prod (channelKMTMeasure (Fin 2)),
            KMTTransfer.KurtzKnightPathsNN N witnessRate T β (fun t p => Z N t p.1)
              (fun l t p => channelRateIntegral T N witnessRate (Z N) l t p.1) p) ∧
        ∀ T : ℝ≥0, ∃ (gamma : ℕ → (channelKMTSpace (Fin 2) × channelKMTSpace (Fin 2)) ×
            (ℕ × Fin 2 → KMTTransfer.KMTPoissonCode) → ℝ) (eta C : ℝ),
          0 < eta ∧ (∀ N, 2 ≤ N → Measurable (gamma N)) ∧
          (∀ N, 2 ≤ N → ∀ z, 0 ≤ gamma N z) ∧
          (∀ N, 2 ≤ N →
            Integrable (fun z => Real.exp (eta * gamma N z)) (KMTTransfer.kmtFamilyMeasure
              ((channelKMTMeasure (Fin 2)).prod (channelKMTMeasure (Fin 2))) β hβ) ∧
            ∫ z, Real.exp (eta * gamma N z) ∂KMTTransfer.kmtFamilyMeasure
              ((channelKMTMeasure (Fin 2)).prod (channelKMTMeasure (Fin 2))) β hβ ≤ C) ∧
          ∀ᵐ z ∂KMTTransfer.kmtFamilyMeasure
              ((channelKMTMeasure (Fin 2)).prod (channelKMTMeasure (Fin 2))) β hβ,
            ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
              ‖Real.sqrt N • (KMTTransfer.transferredChainFamily witnessDir
                  (fun _ => witnessRate) witnessEps witnessRateFamily_nonneg witnessRateFamily_le
                  witnessRateFamily_measurable (fun _ _ => x0) N z t -
                  kurtzFluidLimit witnessRate witnessDir x0 t.toNNReal) -
                sectionFourVAll witnessDeriv witnessRate witnessDir x0 z.1.1 t‖ ≤
                gamma N z * Real.log (N : ℝ) / Real.sqrt N :=
  kurtz_theorem_four_four_channel (v := witnessDir) (f := witnessRate) (eps := witnessEps)
    (M := 1) (F' := witnessDeriv) (L1 := 1) (L2 := 1) (fN := fun _ => witnessRate) (Gamma := 0)
    witnessEps_nonneg zero_le_one witnessRate_nonneg witnessRate_le witnessRate_lip le_rfl
    witnessRateFamily_nonneg witnessRateFamily_le witnessRateFamily_measurable
    witnessRateFamily_close witnessLg witnessRate_sqrt_lip witnessDeriv_hasFDerivAt
    witnessDeriv_norm_le zero_le_one witnessDeriv_lip x0

end Ripple.Kurtz.StrongApprox

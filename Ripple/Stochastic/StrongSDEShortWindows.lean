import Ripple.Stochastic.StrongSDEConcreteMaps

/-!
# Explicit short windows and shifted filtered Brownian drivers

A concrete positive window removes the numerical local
smallness premise. Brownian increments and the prescribed filtration are
shifted together on the same probability space. These ingredients do not
themselves identify stochastic integrals across consecutive windows.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Stochastic.StrongSDEShortWindows
open StrongSDEConcreteMaps

/-- A deterministic window depending only on the two Lipschitz bounds. -/
def shortWindow (Lb S : ℝ≥0) : ℝ≥0 :=
  1 / (16 * (1 + Lb ^ 2 + S ^ 2))

theorem shortWindow_pos (Lb S : ℝ≥0) : 0 < shortWindow Lb S := by
  unfold shortWindow
  positivity

theorem shortWindow_coe (Lb S : ℝ≥0) :
    (shortWindow Lb S : ℝ) =
      1 / (16 * (1 + (Lb : ℝ) ^ 2 + (S : ℝ) ^ 2)) := by
  simp only [shortWindow, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add,
    NNReal.coe_pow, NNReal.coe_one, NNReal.coe_ofNat]

/-- The chosen interval has a contraction budget at most `65/128`. -/
theorem shortWindow_budget (Lb S : ℝ≥0) :
    2 * (shortWindow Lb S : ℝ) ^ 2 * (Lb : ℝ) ^ 2 +
      8 * (shortWindow Lb S : ℝ) * (S : ℝ) ^ 2 ≤ 65 / 128 := by
  let h : ℝ := shortWindow Lb S
  have hh : 0 ≤ h := (shortWindow Lb S).coe_nonneg
  have hden : 0 < 16 * (1 + (Lb : ℝ) ^ 2 + (S : ℝ) ^ 2) := by positivity
  have hid : h * (16 * (1 + (Lb : ℝ) ^ 2 + (S : ℝ) ^ 2)) = 1 := by
    dsimp [h]
    rw [shortWindow_coe]
    exact one_div_mul_cancel hden.ne'
  have hb : 0 ≤ h * (Lb : ℝ) ^ 2 := mul_nonneg hh (sq_nonneg _)
  have hs : 0 ≤ h * (S : ℝ) ^ 2 := mul_nonneg hh (sq_nonneg _)
  have hhsmall : h ≤ 1 / 16 := by nlinarith
  have hbsmall : h * (Lb : ℝ) ^ 2 ≤ 1 / 16 := by nlinarith
  have hssmall : h * (S : ℝ) ^ 2 ≤ 1 / 16 := by nlinarith
  have hprod : h * (h * (Lb : ℝ) ^ 2) ≤ (1 / 16 : ℝ) * (1 / 16) :=
    mul_le_mul hhsmall hbsmall hb (by norm_num)
  change 2 * h ^ 2 * (Lb : ℝ) ^ 2 + 8 * h * (S : ℝ) ^ 2 ≤ 65 / 128
  nlinarith

theorem shortWindow_small (Lb S : ℝ≥0) :
    2 * (shortWindow Lb S : ℝ) ^ 2 * (Lb : ℝ) ^ 2 +
      8 * (shortWindow Lb S : ℝ) * (S : ℝ) ^ 2 < 1 :=
  (shortWindow_budget Lb S).trans_lt (by norm_num)

/-- A final partial window satisfies the same strict estimate. -/
theorem small_of_le_shortWindow {T Lb S : ℝ≥0} (hT : T ≤ shortWindow Lb S) :
    2 * (T : ℝ) ^ 2 * (Lb : ℝ) ^ 2 + 8 * (T : ℝ) * (S : ℝ) ^ 2 < 1 := by
  have ht : (T : ℝ) ≤ shortWindow Lb S := by exact_mod_cast hT
  have hsq := pow_le_pow_left₀ T.coe_nonneg ht 2
  have hbudget :
      2 * (T : ℝ) ^ 2 * (Lb : ℝ) ^ 2 + 8 * (T : ℝ) * (S : ℝ) ^ 2 ≤
        2 * (shortWindow Lb S : ℝ) ^ 2 * (Lb : ℝ) ^ 2 +
          8 * (shortWindow Lb S : ℝ) * (S : ℝ) ^ 2 := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (by norm_num)) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht (by norm_num)) (sq_nonneg _)
  exact hbudget.trans_lt (shortWindow_small Lb S)

/-- The channel Lipschitz bound uses the actual directions in the SDE. -/
def channelSize {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (ell : ι → E) (L : ι → ℝ≥0) : ℝ≥0 := ∑ i, ‖ell i‖₊ * L i

theorem channelSize_coe {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (ell : ι → E) (L : ι → ℝ≥0) :
    (channelSize ell L : ℝ) = ∑ i, ‖ell i‖ * (L i : ℝ) := by
  simp [channelSize]

/-- The local fixed-point theorem now has no numerical smallness premise. -/
theorem exists_unique_picard_on_shortWindow {Ω E ι : Type*}
    [mΩ : MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : Filtration ℝ≥0 mΩ)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (ell : ι → E) (g : ι → E → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : E → E) (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C) (x₀ : E)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃! X : State (E := E) (μ := μ) F (shortWindow Lb (channelSize ell L)),
      StrongSDE.picardStep (initial F (shortWindow Lb (channelSize ell L)) x₀)
        (drift F (shortWindow Lb (channelSize ell L)) hnull b hb C hC hbC)
        (noise F (shortWindow Lb (channelSize ell L)) B hB hBmeas hnull ell g
          (fun i => (hLip i).continuous) K hK N) X = X := by
  apply exists_unique_concrete_picard F (shortWindow Lb (channelSize ell L))
    B hB hBmeas hnull ell g L hLip K hK b Lb hb C hC hbC x₀ N hN
  simpa only [channelSize_coe] using shortWindow_small Lb (channelSize ell L)

section Shift
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- Elapsed-time filtration at a deterministic starting time. -/
def shiftedFiltration (F : Filtration ℝ≥0 mΩ) (a : ℝ≥0) : Filtration ℝ≥0 mΩ where
  seq t := F (a + t)
  mono' s t hst := F.mono (add_le_add le_rfl hst)
  le' t := F.le (a + t)

/-- The driving Brownian increments on a window beginning at `a`. -/
def shiftedDriver (B : ℝ≥0 → Ω → ℝ) (a t : ℝ≥0) (ω : Ω) : ℝ :=
  B (a + t) ω - B a ω

@[simp] theorem shiftedDriver_zero (B : ℝ≥0 → Ω → ℝ) (a : ℝ≥0) (ω : Ω) :
    shiftedDriver B a 0 ω = 0 := by simp [shiftedDriver]

theorem shiftedFiltration_null (F : Filtration ℝ≥0 mΩ)
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (a t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet A) (hz : μ A = 0) :
    MeasurableSet[shiftedFiltration F a t] A := hnull (a + t) A hA hz

theorem shiftedDriver_continuous (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (a : ℝ≥0) (ω : Ω) :
    Continuous (fun t => shiftedDriver B a t ω) :=
  ((hB ω).comp (continuous_const.add continuous_id)).sub continuous_const

theorem shiftedDriver_measurable (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ t, Measurable (B t)) (a t : ℝ≥0) :
    Measurable (shiftedDriver B a t) := (hB (a + t)).sub (hB a)

/-- Filtered Brownian structure is preserved by shifting driver and
filtration together, without changing the probability measure. -/
theorem shiftedDriver_isFilteredPreBrownian {B : ℝ≥0 → Ω → ℝ}
    {F : Filtration ℝ≥0 mΩ} [hB : IsFilteredPreBrownian B F μ] (a : ℝ≥0) :
    IsFilteredPreBrownian (shiftedDriver B a) (shiftedFiltration F a) μ where
  toIsPreBrownian := IsPreBrownian.shift a
  stronglyAdapted t := (hB.stronglyAdapted (a + t)).sub
    ((hB.stronglyAdapted a).mono (F.mono (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ t))))
  indep s t hst := by
    have heq : shiftedDriver B a t - shiftedDriver B a s = B (a + t) - B (a + s) := by
      funext ω
      simp only [Pi.sub_apply, shiftedDriver]
      ring
    rw [heq]
    exact hB.indep (a + s) (a + t) (add_le_add le_rfl hst)

/-- Joint vector increment independence is preserved as well; separate
scalar increment independence is not substituted for this premise. -/
theorem shifted_vectorIncrement_indep {ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (hind : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap
      (fun ω i => B i t ω - B i s ω) inferInstance) (F s) μ)
    (a s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun ω i => shiftedDriver (B i) a t ω - shiftedDriver (B i) a s ω) inferInstance)
      (shiftedFiltration F a s) μ := by
  have heq : (fun ω i => shiftedDriver (B i) a t ω - shiftedDriver (B i) a s ω) =
      fun ω i => B i (a + t) ω - B i (a + s) ω := by
    funext ω i
    simp only [shiftedDriver]
    ring
  rw [heq]
  exact hind (a + s) (a + t) (add_le_add le_rfl hst)

end Shift
end Ripple.Stochastic.StrongSDEShortWindows

import Ripple.Kurtz.StrongApprox.WienerIntegralPathBridge
import Ripple.Kurtz.StrongApprox.SectionFourGaussianLaw

/-!
# Two-time covariance of the actual deterministic channel integrals

Different coefficients and observation times are allowed in the two factors.
Off-diagonal terms vanish by independence of the product-coordinate Brownian
paths and measurability of the continuous integration-by-parts functional.
The diagonal terms use the common-horizon Wiener integral bridge.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox.ChannelWienerCovariance

variable {m : ℕ}

/-- The integration-by-parts integral driven by an actual channel Brownian path. -/
def channelJ (a : ℝ → ℝ) (l : Fin m) (t : ℝ≥0)
    (ω : channelKMTSpace (Fin m)) : ℝ :=
  Analysis.BVIntegrationByParts.J a (fun s => channelBrownian l s.toNNReal ω) t

/-- Square integrability comes from the Wiener/pathwise identification. -/
theorem memLp_channelJ {T t : ℝ≥0} (ht : t ≤ T)
    {a : ℝ → ℝ} {K : ℝ≥0} (hc : Continuous a)
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (l : Fin m) :
    MemLp (channelJ a l t) 2 (channelKMTMeasure (Fin m)) := by
  letI := channelBrownian_isPreBrownian l
  exact WienerIntegralPathBridge.memLp_J ht hc ha
    (Filter.Eventually.of_forall (channelBrownian_continuous l))

/-- Two different channels remain independent after applying different
continuous path functionals at different times. -/
theorem channelJ_indepFun {T t u : ℝ≥0} (ht : t ≤ T) (hu : u ≤ T)
    {a b : ℝ → ℝ} {Ka Kb : ℝ≥0}
    (ha : LipschitzOnWith Ka a (Icc 0 (T : ℝ)))
    (hb : LipschitzOnWith Kb b (Icc 0 (T : ℝ)))
    {l k : Fin m} (hlk : l ≠ k) :
    IndepFun (channelJ a l t) (channelJ b k u) (channelKMTMeasure (Fin m)) := by
  let ta : Icc (0 : ℝ) (T : ℝ) := ⟨t, t.coe_nonneg, by exact_mod_cast ht⟩
  let ub : Icc (0 : ℝ) (T : ℝ) := ⟨u, u.coe_nonneg, by exact_mod_cast hu⟩
  let Fa : C(Icc (0 : ℝ) (T : ℝ), ℝ) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ ta).comp (JPathCLM T ha)
  let Fb : C(Icc (0 : ℝ) (T : ℝ), ℝ) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ ub).comp (JPathCLM T hb)
  have hind := ((brownianPath_independent (m := m) T).indepFun hlk).comp
    Fa.continuous.measurable Fb.continuous.measurable
  have hea : Fa ∘ brownianPath T l = channelJ a l t := by
    funext ω
    exact JPathCLM_brownianPath T ha l ω ta
  have heb : Fb ∘ brownianPath T k = channelJ b k u := by
    funext ω
    exact JPathCLM_brownianPath T hb k ω ub
  rw [hea, heb] at hind
  exact hind

/-- The same-channel two-time covariance, with two arbitrary deterministic coefficients. -/
theorem covariance_channelJ_same {T t u : ℝ≥0} (ht : t ≤ T) (hu : u ≤ T)
    {a b : ℝ → ℝ} {Ka Kb : ℝ≥0} (hca : Continuous a) (hcb : Continuous b)
    (ha : LipschitzOnWith Ka a (Icc 0 (T : ℝ)))
    (hb : LipschitzOnWith Kb b (Icc 0 (T : ℝ))) (l : Fin m) :
    cov[channelJ a l t, channelJ b l u; channelKMTMeasure (Fin m)] =
      ∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)), a s * b s := by
  letI := channelBrownian_isPreBrownian l
  exact WienerIntegralPathBridge.covariance_J ht hu hca hcb ha hb
    (Filter.Eventually.of_forall (channelBrownian_continuous l))

/-- The cross-channel covariance is derived from the product construction. -/
theorem covariance_channelJ_distinct {T t u : ℝ≥0} (ht : t ≤ T) (hu : u ≤ T)
    {a b : ℝ → ℝ} {Ka Kb : ℝ≥0} (hca : Continuous a) (hcb : Continuous b)
    (ha : LipschitzOnWith Ka a (Icc 0 (T : ℝ)))
    (hb : LipschitzOnWith Kb b (Icc 0 (T : ℝ)))
    {l k : Fin m} (hlk : l ≠ k) :
    cov[channelJ a l t, channelJ b k u; channelKMTMeasure (Fin m)] = 0 :=
  (channelJ_indepFun ht hu ha hb hlk).covariance_eq_zero
    (memLp_channelJ ht hca ha l) (memLp_channelJ hu hcb hb k)

/-- Two-time covariance of finite sums of actual channel integrals.
Only matching channel indices survive, even when the coefficient arrays differ. -/
theorem covariance_sum_channelJ {T t u : ℝ≥0} (ht : t ≤ T) (hu : u ≤ T)
    {a b : Fin m → ℝ → ℝ} {Ka Kb : Fin m → ℝ≥0}
    (hca : ∀ l, Continuous (a l)) (hcb : ∀ l, Continuous (b l))
    (ha : ∀ l, LipschitzOnWith (Ka l) (a l) (Icc 0 (T : ℝ)))
    (hb : ∀ l, LipschitzOnWith (Kb l) (b l) (Icc 0 (T : ℝ))) :
    cov[fun ω => ∑ l, channelJ (a l) l t ω,
      fun ω => ∑ l, channelJ (b l) l u ω; channelKMTMeasure (Fin m)] =
      ∑ l, ∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)), a l s * b l s := by
  classical
  rw [covariance_fun_sum_fun_sum
    (fun l => memLp_channelJ ht (hca l) (ha l) l)
    (fun l => memLp_channelJ hu (hcb l) (hb l) l)]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_eq_single l]
  · exact covariance_channelJ_same ht hu (hca l) (hcb l) (ha l) (hb l) l
  · intro k _ hkl
    exact covariance_channelJ_distinct ht hu (hca l) (hcb k) (ha l) (hb k) hkl.symm
  · simp

/-- Scalar weights, for example pairings with fixed channel jump vectors,
can be taken outside the two-time covariance integrals. -/
theorem covariance_weighted_sum_channelJ {T t u : ℝ≥0} (ht : t ≤ T) (hu : u ≤ T)
    {a b : Fin m → ℝ → ℝ} {Ka Kb : Fin m → ℝ≥0}
    (hca : ∀ l, Continuous (a l)) (hcb : ∀ l, Continuous (b l))
    (ha : ∀ l, LipschitzOnWith (Ka l) (a l) (Icc 0 (T : ℝ)))
    (hb : ∀ l, LipschitzOnWith (Kb l) (b l) (Icc 0 (T : ℝ)))
    (c d : Fin m → ℝ) :
    cov[fun ω => ∑ l, c l * channelJ (a l) l t ω,
      fun ω => ∑ l, d l * channelJ (b l) l u ω; channelKMTMeasure (Fin m)] =
      ∑ l, c l * d l *
        (∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)), a l s * b l s) := by
  classical
  rw [covariance_fun_sum_fun_sum
    (fun l => (memLp_channelJ ht (hca l) (ha l) l).const_mul (c l))
    (fun l => (memLp_channelJ hu (hcb l) (hb l) l).const_mul (d l))]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_eq_single l]
  · rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_channelJ_same ht hu (hca l) (hcb l) (ha l) (hb l) l]
    ring
  · intro k _ hkl
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_channelJ_distinct ht hu (hca l) (hcb k) (ha l) (hb k) hkl.symm]
    simp
  · simp

end Ripple.Kurtz.StrongApprox.ChannelWienerCovariance

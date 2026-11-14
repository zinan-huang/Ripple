-- Ripple/Kurtz/StrongApprox/KMTCoefficientAdapter.lean
import Ripple.Kurtz.StrongApprox.KurtzLemmaThreeOne

/-!
# Real coefficient for the all-time KMT estimate

The coefficient is the real value of the normalized error supremum
`allTimeKMTXi` of the all-time coupling, which dominates the variable `K` of
Kurtz 1978, Lemma 3.1 (p. 230).  The path estimate
`|Y(t) - t - W(t)| ≤ Ξ log (max 2 t)` is asserted on the locus where `Ξ` is
finite, which has full measure; `Ξ` is measurable and has an exponential
moment.  This is the KMT input `|Y_l - B_l| ≤ K_l log t` of Theorem 3.3(a).
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open AllTimeKMT AllTimeKurtzMoment

/-- Real coefficient obtained from the normalized all-time error supremum. -/
def kmtCoefficient (ω : AllTimeKMTSpace) : ℝ := (allTimeKMTXi ω).toReal

theorem measurable_kmtCoefficient : Measurable kmtCoefficient :=
  measurable_allTimeKMTXi.ennreal_toReal

theorem kmtCoefficient_nonneg (ω : AllTimeKMTSpace) : 0 ≤ kmtCoefficient ω :=
  ENNReal.toReal_nonneg

/-- The normalized real-time supremum controls every nonnegative time. -/
theorem kmtCoefficient_bound (ω : AllTimeKMTSpace)
    (hXi : allTimeKMTXi ω ≠ ⊤) {t : ℝ} (ht : 0 ≤ t) :
    |(allTimeKMTPoisson t ω : ℝ) - t - allTimeKMTBrownian t ω| ≤
      kmtCoefficient ω * Real.log (max 2 t) := by
  have hratio : ENNReal.ofReal (allTimeKMTRatio t ω) ≤ allTimeKMTXi ω := by
    rw [allTimeKMTXi_eq_real_sup]
    exact le_iSup (fun s : {s : ℝ // 0 ≤ s} =>
      ENNReal.ofReal (allTimeKMTRatio s.1 ω)) ⟨t, ht⟩
  have hreal : allTimeKMTRatio t ω ≤ kmtCoefficient ω :=
    (ENNReal.ofReal_le_iff_le_toReal hXi).mp hratio
  have hlog : 0 < Real.log (max 2 t) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  exact (div_le_iff₀ hlog).mp hreal

theorem kmtCoefficient_bound_ae :
    ∀ᵐ ω ∂allTimeKMTMeasure, ∀ t : ℝ, 0 ≤ t →
      |(allTimeKMTPoisson t ω : ℝ) - t - allTimeKMTBrownian t ω| ≤
        kmtCoefficient ω * Real.log (max 2 t) := by
  filter_upwards [allTimeKMTXi_ae_ne_top] with ω hXi
  exact fun t ht => kmtCoefficient_bound ω hXi ht

/-- Every exponent strictly between zero and the existing tail rate works. -/
theorem integrable_exp_kmtCoefficient {θ : ℝ} (hθpos : 0 < θ)
    (hθrate : θ < allTimeKurtzGamma) :
    Integrable (fun ω => Real.exp (θ * kmtCoefficient ω)) allTimeKMTMeasure :=
  (integral_exp_allTimeKMTXi_le hθpos hθrate).1

theorem kmtCoefficient_exponentialMoment :
    ∃ θ : ℝ, 0 < θ ∧
      Integrable (fun ω => Real.exp (θ * kmtCoefficient ω)) allTimeKMTMeasure := by
  refine ⟨allTimeKurtzGamma / 2, half_pos allTimeKurtzGamma_pos, ?_⟩
  exact integrable_exp_kmtCoefficient (half_pos allTimeKurtzGamma_pos)
    (half_lt_self allTimeKurtzGamma_pos)

end Ripple.Kurtz.StrongApprox


end

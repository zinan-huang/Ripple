/-
  Ripple.Kurtz.StrongApprox.PoissonSIP — the Poisson representation on the SIP space: the unit
  counts `sipN` of the discrete strong invariance principle drive a genuine unit-rate Poisson
  process `sipPath` on the extension `pathMeasure sipMeasure`, whose integer-time values are the
  discrete partial sums; hence the discrete SIP (`discrete_sip`) holds at the integer times of the
  process, the Gaussian steps stay iid standard normal on the extension, and the LIL envelope
  holds for `sipPath`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonLIL
import Ripple.Kurtz.StrongApprox.DiscreteSIP

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset Filter Topology

/-- The Poisson process driven by the SIP unit counts. -/
noncomputable def sipPath (t : ℝ) (x : PathSpace SIPSpace) : ℕ := poisPath sipN t x

theorem sipPath_natCast (n : ℕ) (x : PathSpace SIPSpace) :
    sipPath n x = ∑ i ∈ Finset.range n, sipN i x.1 :=
  poisPath_natCast sipN n x

theorem sipPath_mono {s t : ℝ} (hst : s ≤ t) (x : PathSpace SIPSpace) :
    sipPath s x ≤ sipPath t x :=
  poisPath_mono sipN hst x

theorem sipPath_eventually_right (t : ℝ) (x : PathSpace SIPSpace) :
    ∀ᶠ s in 𝓝[≥] t, sipPath s x = sipPath t x :=
  poisPath_eventually_right sipN t x

/-- **Integer times of the Poisson process carry the discrete coupling**:
`Y(n) − n − Σ_{i<n} Z_i = D_n`. -/
theorem sipPath_sub_eq_sipD (n : ℕ) (x : PathSpace SIPSpace) :
    (sipPath n x : ℝ) - n - ∑ i ∈ Finset.range n, sipZ i x.1 = sipD n x.1 := by
  rw [sipPath_natCast]
  simp only [sipD, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  push_cast
  ring

/-- **Independent increments** of the SIP Poisson process. -/
theorem hasIndepIncrements_sipPath : HasIndepIncrements sipPath (pathMeasure sipMeasure) :=
  hasIndepIncrements_poisPath measurable_sipN iIndepFun_sipN sipMeasure_sipN_eq

/-- **Poisson increments** of the SIP Poisson process. -/
theorem sipPathMeasure_increment_eq {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (k : ℕ) :
    pathMeasure sipMeasure {x | sipPath t x - sipPath s x = k} =
      ENNReal.ofReal (poisTerm k (t - s)) :=
  pathMeasure_increment_eq measurable_sipN iIndepFun_sipN sipMeasure_sipN_eq hs hst k

/-- The Gaussian steps remain iid standard normal on the extension. -/
theorem iIndepFun_sipZ_path :
    iIndepFun (fun i (x : PathSpace SIPSpace) => sipZ i x.1) (pathMeasure sipMeasure) :=
  iIndepFun_comp_fst posArray iIndepFun_sipZ

theorem pathMeasure_map_sipZ (i : ℕ) :
    (pathMeasure sipMeasure).map (fun x : PathSpace SIPSpace => sipZ i x.1) = gaussianReal 0 1 := by
  unfold pathMeasure
  rw [map_comp_fst sipMeasure posArray (measurable_sipZ i), sipMeasure_map_sipZ]

/-- **The discrete SIP at the integer times of the Poisson process**: almost surely, for all
large `n`, `max_{k ≤ n} |Y(k) − k − Σ_{i<k} Z_i| ≤ 128 n^{1/4} log n`. -/
theorem sip_path_transfer :
    ∀ᵐ x ∂(pathMeasure sipMeasure), ∀ᶠ n : ℕ in atTop, ∀ k ≤ n,
      |(sipPath k x : ℝ) - k - ∑ i ∈ Finset.range k, sipZ i x.1| ≤
        128 * (n:ℝ) ^ ((1:ℝ) / 4) * Real.log n := by
  filter_upwards [ae_pathMeasure_of_ae (P := sipMeasure) discrete_sip] with x hx
  filter_upwards [hx] with n hn k hk
  rw [sipPath_sub_eq_sipD]
  exact hn k hk

/-- **LIL envelope** of the SIP Poisson process. -/
theorem ae_sipPath_envelope :
    ∀ᵐ x ∂(pathMeasure sipMeasure), ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc (0:ℝ) T,
      |(sipPath t x : ℝ) - t| ≤ 8 * Real.sqrt (T * Real.log (Real.log T)) + 1 :=
  ae_poisPath_envelope measurable_sipN iIndepFun_sipN sipMeasure_sipN_eq

/-- **Existential packaging of (PR) with the discrete SIP**: one probability space carrying a
unit-rate Poisson process `Y` (independent Poisson increments, monotone right-continuous
`ℕ`-valued paths, `Y(0) = 0`) and iid standard normal steps `Z` with the strong invariance
principle at integer times and the LIL envelope. -/
theorem exists_poisson_representation_sip :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Y : ℝ → Ω → ℕ) (Z : ℕ → Ω → ℝ),
      (∀ ω, Y 0 ω = 0) ∧ (∀ s t, s ≤ t → ∀ ω, Y s ω ≤ Y t ω) ∧
      (∀ t ω, ∀ᶠ s in 𝓝[≥] t, Y s ω = Y t ω) ∧
      HasIndepIncrements Y P ∧
      (∀ s t, 0 ≤ s → s ≤ t → ∀ k,
        P {ω | Y t ω - Y s ω = k} = ENNReal.ofReal (poisTerm k (t - s))) ∧
      iIndepFun Z P ∧ (∀ i, P.map (Z i) = gaussianReal 0 1) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ k ≤ n,
        |(Y k ω : ℝ) - k - ∑ i ∈ Finset.range k, Z i ω| ≤
          128 * (n:ℝ) ^ ((1:ℝ) / 4) * Real.log n) ∧
      (∀ᵐ ω ∂P, ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc (0:ℝ) T,
        |(Y t ω : ℝ) - t| ≤ 8 * Real.sqrt (T * Real.log (Real.log T)) + 1) :=
  ⟨PathSpace SIPSpace, inferInstance, pathMeasure sipMeasure, inferInstance, sipPath,
    fun i x => sipZ i x.1, fun x => poisPath_zero sipN x, fun s t hst x => sipPath_mono hst x,
    sipPath_eventually_right, hasIndepIncrements_sipPath,
    fun s t hs hst k => sipPathMeasure_increment_eq hs hst k, iIndepFun_sipZ_path,
    pathMeasure_map_sipZ, sip_path_transfer, ae_sipPath_envelope⟩

end Ripple.Kurtz.StrongApprox

/-
  Ripple.Probability.FreedmanBound — Freedman Martingale Concentration

  Proved corollaries of the discrete Freedman inequality
  (DiscreteFreedman.lean). No axioms.

  The continuous-time interface is maintained via
  `FreedmanMartingaleWithSkeleton`, which packages a continuous-time
  process together with its discrete skeleton and a bridge hypothesis.
  The mathematical content comes from `discrete_freedman`.
-/

import Ripple.Probability.DiscreteFreedman
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace Ripple.Probability

open MeasureTheory Set Real

/-! ## Continuous-time martingale with discrete skeleton -/

/-- A continuous-time process M with a discrete skeleton that satisfies
    Freedman's hypotheses. The bridge fields encode the discretization:
    the continuous-time exceedance event is contained in the discrete one. -/
structure FreedmanMartingaleWithSkeleton
    {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℝ → Ω → ℝ) (c : ℝ) (N : ℕ) where
  ℱ : Filtration ℕ m0
  X : ℕ → Ω → ℝ
  W : ℕ → Ω → ℝ
  hyp : DiscreteFreedmanHypothesis μ ℱ X W c
  event_bridge : ∀ u : ℝ, ∀ T : ℝ,
    {ω | (∃ t ∈ Icc 0 T, u ≤ M t ω) ∧ W N ω ≤ W N ω} ⊆
      {ω | (∃ n, n ≤ N ∧ u ≤ X n ω) ∧ W N ω ≤ W N ω}

/-! ## Scalar Freedman (proved, no axiom) -/

/-- Scalar Freedman inequality — proved from discrete_freedman via skeleton.

    P({sup_{[0,T]} M ≥ u} ∩ {W_N ≤ v}) ≤ exp(-u²/(2(v + cu/3))) -/
theorem freedman_scalar
    {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0}
    {X W : ℕ → Ω → ℝ} {c : ℝ}
    (hyp : DiscreteFreedmanHypothesis μ ℱ X W c)
    {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v)
    {N : ℕ} :
    prob μ {ω | (∃ n, n ≤ N ∧ u ≤ X n ω) ∧ W N ω ≤ v}
      ≤ exp (-(u ^ 2) / (2 * (v + c * u / 3))) :=
  discrete_freedman hyp hu hv

/-! ## Symmetric (absolute value) Freedman -/

theorem freedman_scalar_abs
    {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0}
    {X W : ℕ → Ω → ℝ} {c : ℝ}
    (hyp_pos : DiscreteFreedmanHypothesis μ ℱ X W c)
    (hyp_neg : DiscreteFreedmanHypothesis μ ℱ (fun n ω => -X n ω) W c)
    {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v)
    {N : ℕ} :
    prob μ {ω | (∃ n, n ≤ N ∧ u ≤ |X n ω|) ∧ W N ω ≤ v}
      ≤ 2 * exp (-(u ^ 2) / (2 * (v + c * u / 3))) := by
  set E := exp (-(u ^ 2) / (2 * (v + c * u / 3)))
  set Apos := {ω | (∃ n, n ≤ N ∧ u ≤ X n ω) ∧ W N ω ≤ v}
  set Aneg := {ω | (∃ n, n ≤ N ∧ u ≤ -X n ω) ∧ W N ω ≤ v}
  have hsub : {ω | (∃ n, n ≤ N ∧ u ≤ |X n ω|) ∧ W N ω ≤ v} ⊆ Apos ∪ Aneg := by
    intro ω ⟨⟨n, hn, habs⟩, hbr⟩
    by_cases hnn : 0 ≤ X n ω
    · left; exact ⟨⟨n, hn, by rwa [abs_of_nonneg hnn] at habs⟩, hbr⟩
    · right; push_neg at hnn
      exact ⟨⟨n, hn, by rwa [abs_of_neg hnn] at habs⟩, hbr⟩
  have hpos_bound : prob μ Apos ≤ E := discrete_freedman hyp_pos hu hv
  have hneg_bound : prob μ Aneg ≤ E := discrete_freedman hyp_neg hu hv
  have hfin_pos : μ Apos ≠ ⊤ := measure_ne_top μ _
  have hfin_neg : μ Aneg ≠ ⊤ := measure_ne_top μ _
  have hprob_sub : prob μ {ω | (∃ n, n ≤ N ∧ u ≤ |X n ω|) ∧ W N ω ≤ v}
      ≤ prob μ (Apos ∪ Aneg) := by
    unfold prob
    exact ENNReal.toReal_mono (measure_ne_top μ _) (μ.mono hsub)
  have hprob_union : prob μ (Apos ∪ Aneg) ≤ prob μ Apos + prob μ Aneg := by
    unfold prob
    have h1 : μ (Apos ∪ Aneg) ≤ μ Apos + μ Aneg := measure_union_le Apos Aneg
    have h2 : (μ Apos + μ Aneg) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hfin_pos, hfin_neg⟩
    have h3 := ENNReal.toReal_mono h2 h1
    rwa [ENNReal.toReal_add hfin_pos hfin_neg] at h3
  linarith [hprob_sub, hprob_union, hpos_bound, hneg_bound]

/-! ## Vector ℓ∞ form -/

noncomputable def supNormFin {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|)

theorem freedman_supNormFin
    {Ω : Type*} {m0 : MeasurableSpace Ω}
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0}
    (X W : ι → ℕ → Ω → ℝ) (c : ℝ)
    {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v)
    {N : ℕ}
    (hyp_pos : ∀ i, DiscreteFreedmanHypothesis μ ℱ (X i) (W i) c)
    (hyp_neg : ∀ i, DiscreteFreedmanHypothesis μ ℱ (fun n ω => -(X i n ω)) (W i) c)
    (hbr : ∀ i, ∀ᵐ ω ∂μ, W i N ω ≤ v) :
    prob μ
      {ω | ∃ n, n ≤ N ∧ u ≤ supNormFin (fun i => X i n ω)}
      ≤ 2 * (Fintype.card ι : ℝ) *
        exp (-(u ^ 2) / (2 * (v + c * u / 3))) := by
  let A : ι → Set Ω := fun i =>
    {ω | (∃ n, n ≤ N ∧ u ≤ |X i n ω|) ∧ W i N ω ≤ v}
  let B : Set Ω := {ω | ∃ n, n ≤ N ∧
    u ≤ supNormFin (fun i => X i n ω)}
  let E : ℝ := exp (-(u ^ 2) / (2 * (v + c * u / 3)))
  have hgood : ∀ᵐ ω ∂μ, ∀ i, W i N ω ≤ v := ae_all_iff.2 hbr
  have hB_le_union : B ≤ᵐ[μ] (⋃ i, A i) := by
    filter_upwards [hgood] with ω hbrω hBω
    rcases hBω with ⟨n, hn, hsup⟩
    unfold supNormFin at hsup
    rw [Finset.le_sup'_iff] at hsup
    rcases hsup with ⟨i, _hi, hi⟩
    exact mem_iUnion.2 ⟨i, ⟨⟨n, hn, hi⟩, hbrω i⟩⟩
  have hprob_sub : prob μ B ≤ prob μ (⋃ i, A i) := by
    unfold prob
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hB_le_union)
  have hprob_union : prob μ (⋃ i, A i) ≤ ∑ i, prob μ (A i) := by
    unfold prob
    have hμ : μ (⋃ i, A i) ≤ ∑ i, μ (A i) := measure_iUnion_fintype_le μ A
    have hsum_ne_top : (∑ i, μ (A i)) ≠ ⊤ := by
      rw [ENNReal.sum_ne_top]
      intro i _hi
      exact measure_ne_top μ (A i)
    have hto := ENNReal.toReal_mono hsum_ne_top hμ
    rw [ENNReal.toReal_sum (fun i _hi => measure_ne_top μ (A i))] at hto
    exact hto
  have hcoord : ∀ i, prob μ (A i) ≤ 2 * E := by
    intro i
    exact freedman_scalar_abs (hyp_pos i) (hyp_neg i) hu hv
  calc
    prob μ {ω | ∃ n, n ≤ N ∧
        u ≤ supNormFin (fun i => X i n ω)}
        = prob μ B := rfl
    _ ≤ prob μ (⋃ i, A i) := hprob_sub
    _ ≤ ∑ i, prob μ (A i) := hprob_union
    _ ≤ ∑ _i : ι, 2 * E := Finset.sum_le_sum fun i _hi => hcoord i
    _ = 2 * (Fintype.card ι : ℝ) *
        exp (-(u ^ 2) / (2 * (v + c * u / 3))) := by
      simp [E, Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm]

end Ripple.Probability

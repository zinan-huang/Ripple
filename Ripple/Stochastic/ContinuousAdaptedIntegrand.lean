/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The strict-past grid argument is adapted from their predictable-process work.
-/
import Ripple.Stochastic.FilteredItoIntegralCLM
import Ripple.Stochastic.BoundedPredictableApproximation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Continuous adapted integrands in the prescribed predictable product space

A strict-past deterministic grid proves predictable
measurability directly. Boundedness on a finite horizon supplies actual L²
membership. The final maximal estimate uses the bounded predictable exponential
producer; the preceding construction uses the installed filtered integral only.

The strict-grid argument follows the Apache-2.0 StochLean contributors' proofs
in `Probability/Process/Measurability/PredictableGrid.lean`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.ContinuousAdaptedIntegrand
open FilteredItoIntegralL2 FilteredItoIntegralCLM FilteredItoIntegralProcess
open BoundedStochasticExponential

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

/-- At a grid endpoint use the preceding cell, as required by `(s,t]`. -/
def leftGrid (δ t : ℝ≥0) : ℝ≥0 :=
  δ * ((Nat.ceil (t / δ) - 1 : ℕ) : ℝ≥0)

@[simp] theorem leftGrid_zero (δ : ℝ≥0) : leftGrid δ 0 = 0 := by
  simp [leftGrid]

theorem leftGrid_mem_cell {δ t : ℝ≥0} (hδ : 0 < δ) (ht : 0 < t) :
    t ∈ Ioc (leftGrid δ t) (leftGrid δ t + δ) := by
  have hn : 0 < Nat.ceil (t / δ) := Nat.ceil_pos.mpr (div_pos ht hδ)
  have hs : Nat.ceil (t / δ) - 1 + 1 = Nat.ceil (t / δ) := Nat.sub_add_cancel hn
  have hlo : ((Nat.ceil (t / δ) - 1 : ℕ) : ℝ≥0) < t / δ :=
    Nat.lt_ceil.mp (Nat.sub_lt hn (by decide))
  have hhi := Nat.le_ceil (t / δ)
  constructor
  · simpa only [leftGrid, mul_comm δ] using (lt_div_iff₀ hδ).mp hlo
  · have h := (div_le_iff₀ hδ).mp hhi
    have heq : (Nat.ceil (t / δ) : ℝ≥0) =
        ((Nat.ceil (t / δ) - 1 : ℕ) : ℝ≥0) + 1 := by exact_mod_cast hs.symm
    simpa only [heq, add_mul, one_mul, leftGrid, mul_comm δ] using h

theorem leftGrid_eq_of_mem_cell {δ t : ℝ≥0} (hδ : 0 < δ) (k : ℕ)
    (ht : t ∈ Ioc (δ * k) (δ * (k + 1))) : leftGrid δ t = δ * k := by
  have hceil : Nat.ceil (t / δ) = k + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).mpr
    constructor
    · simpa only [Nat.add_sub_cancel, Nat.succ_sub_one] using
        (lt_div_iff₀ hδ).mpr (by simpa only [mul_comm δ] using ht.1)
    · exact (div_le_iff₀ hδ).mpr
        (by simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ, mul_comm δ] using ht.2)
  simp only [leftGrid, hceil, Nat.add_sub_cancel]

theorem leftGrid_le {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ≥0) : leftGrid δ t ≤ t := by
  by_cases ht : t = 0
  · simp [ht]
  · exact (leftGrid_mem_cell hδ (pos_iff_ne_zero.mpr ht)).1.le

theorem le_leftGrid_add {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ≥0) :
    t ≤ leftGrid δ t + δ := by
  by_cases ht : t = 0
  · simp [ht]
  · exact (leftGrid_mem_cell hδ (pos_iff_ne_zero.mpr ht)).2

theorem tendsto_leftGrid (t : ℝ≥0) :
    Tendsto (fun n : ℕ => leftGrid (1 / ((n : ℝ≥0) + 1)) t) atTop (𝓝 t) := by
  have hδ : ∀ n : ℕ, 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) := fun n => by positivity
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ≥0) / ((n : ℝ≥0) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlo : Tendsto (fun n : ℕ => t - 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 t) := by
    simpa only [tsub_zero] using tendsto_const_nhds.sub hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n => tsub_le_iff_right.mpr (le_leftGrid_add (hδ n) t))
    (fun n => leftGrid_le (hδ n) t)

/-- A sampled adapted process is predictable, by an explicit countable union
of predictable rectangles. No progressive-to-predictable premise is used. -/
theorem measurable_sample {H : ℝ≥0 → Ω → ℝ}
    (ha : ∀ t, Measurable[F t] (H t)) {δ : ℝ≥0} (hδ : 0 < δ) :
    Measurable[F.predictable] (fun z : ℝ≥0 × Ω => H (leftGrid δ z.1) z.2) := by
  intro s hs
  have heq : (fun z : ℝ≥0 × Ω => H (leftGrid δ z.1) z.2) ⁻¹' s =
      ({0} ×ˢ ((H 0) ⁻¹' s)) ∪
        ⋃ k : ℕ, Ioc (δ * k) (δ * (k + 1)) ×ˢ ((H (δ * k)) ⁻¹' s) := by
    ext ⟨t, ω⟩
    constructor
    · intro h
      by_cases ht : t = 0
      · left
        simpa only [ht, mem_prod, mem_singleton_iff, leftGrid_zero, mem_preimage,
          true_and] using h
      · right
        let k := Nat.ceil (t / δ) - 1
        apply mem_iUnion.mpr ⟨k, ?_⟩
        have hcell := leftGrid_mem_cell hδ (pos_iff_ne_zero.mpr ht)
        refine ⟨?_, h⟩
        simpa only [leftGrid, k, mul_add, mul_one] using hcell
    · rintro (h | h)
      · rcases h with ⟨ht, hω⟩
        have ht' : t = 0 := ht
        change H (leftGrid δ t) ω ∈ s
        simpa only [ht', leftGrid_zero, mem_preimage] using hω
      · obtain ⟨k, hk, hω⟩ := mem_iUnion.mp h
        change H (leftGrid δ t) ω ∈ s
        simpa only [leftGrid_eq_of_mem_cell hδ k hk, mem_preimage] using hω
  rw [heq]
  exact (measurableSet_predictable_singleton_bot_prod (𝓕 := F) (ha 0 hs)).union
    (MeasurableSet.iUnion (fun k =>
      measurableSet_predictable_Ioc_prod (𝓕 := F) _ _ (ha _ hs)))

/-- One common deterministic sampling scheme works for every channel. -/
theorem sample_tendsto {E : Type*} [TopologicalSpace E] {H : ℝ≥0 → Ω → E}
    (hc : ∀ ω, Continuous (fun t => H t ω)) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n : ℕ => H (leftGrid (1 / ((n : ℝ≥0) + 1)) t) ω)
      atTop (𝓝 (H t ω)) :=
  ((hc ω).tendsto t).comp (tendsto_leftGrid t)

/-- All coefficients and all Brownian channels use this same clipped grid. -/
def samplePartition (δ T : ℝ≥0) (i : ℕ) : ℝ≥0 := min (δ * i) T

def sampleCells (δ T : ℝ≥0) : ℕ := Nat.ceil (T / δ)

theorem samplePartition_mono (δ T : ℝ≥0) : Monotone (samplePartition δ T) := by
  intro i j hij
  exact min_le_min_right T (mul_le_mul_left' (by exact_mod_cast hij) δ)

@[simp] theorem samplePartition_zero (δ T : ℝ≥0) : samplePartition δ T 0 = 0 := by
  simp [samplePartition]

theorem samplePartition_end {δ : ℝ≥0} (hδ : 0 < δ) (T : ℝ≥0) :
    samplePartition δ T (sampleCells δ T) = T := by
  apply min_eq_right
  simpa only [sampleCells, mul_comm] using (div_le_iff₀ hδ).mp (Nat.le_ceil (T / δ))

/-- A bounded adapted finite simple process on the common clipped grid. -/
def sampleSP (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) (δ : ℝ≥0) : TBoundedSP (𝓖 := F) T hBmeas :=
  ∑ i ∈ Finset.range (sampleCells δ T),
    BoundedPredictableApproximation.stepSP hBmeas
      (a := samplePartition δ T i) (b := samplePartition δ T (i + 1))
      (samplePartition_mono δ T (Nat.le_succ i)) (min_le_right _ _)
      (ha _) (hb _)

theorem sampleSP_formula (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) (δ t : ℝ≥0) (ω : Ω) :
    ⇑(sampleSP T hBmeas H ha K hb δ).val t ω =
      ∑ i ∈ Finset.range (sampleCells δ T),
        (Ioc (samplePartition δ T i) (samplePartition δ T (i + 1))).indicator
          (fun _ => H (samplePartition δ T i) ω) t := by
  classical
  have hcell : ∀ i,
      ⇑(BoundedPredictableApproximation.stepSP hBmeas
        (a := samplePartition δ T i) (b := samplePartition δ T (i + 1))
        (samplePartition_mono δ T (Nat.le_succ i)) (min_le_right _ _)
        (ha _) (hb _)).val t ω =
      (Ioc (samplePartition δ T i) (samplePartition δ T (i + 1))).indicator
        (fun _ => H (samplePartition δ T i) ω) t := by
    intro i
    rw [SimpleProcess.apply_eq]
    simp [BoundedPredictableApproximation.stepSP, Finsupp.sum_single_index]
  let V := fun i => BoundedPredictableApproximation.stepSP hBmeas
    (a := samplePartition δ T i) (b := samplePartition δ T (i + 1))
    (samplePartition_mono δ T (Nat.le_succ i)) (min_le_right _ _)
    (ha _) (hb _)
  have hsum : ∀ n : ℕ, ⇑(∑ i ∈ Finset.range n, V i).val t ω =
      ∑ i ∈ Finset.range n,
        (Ioc (samplePartition δ T i) (samplePartition δ T (i + 1))).indicator
          (fun _ => H (samplePartition δ T i) ω) t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ, Submodule.coe_add,
        SimpleProcess.coe_add, Pi.add_apply, ih]
      exact congrArg (fun x : ℝ =>
        (∑ i ∈ Finset.range n,
          (Ioc (samplePartition δ T i) (samplePartition δ T (i + 1))).indicator
            (fun _ => H (samplePartition δ T i) ω) t) + x) (hcell n)
  exact hsum (sampleCells δ T)

/-- Clipping the grid at `T` does not change which positive grid cell
contains a time at or before `T`. -/
theorem mem_sample_cell {δ T t : ℝ≥0} (ht : t ≤ T) (i : ℕ) :
    t ∈ Ioc (samplePartition δ T i) (samplePartition δ T (i + 1)) ↔
      t ∈ Ioc (δ * i) (δ * (i + 1)) := by
  simp only [samplePartition, mem_Ioc, min_lt_iff, le_min_iff,
    not_lt.mpr ht, or_false, ht, and_true, Nat.cast_add, Nat.cast_one]

/-- On `(0,T]` the finite simple process equals the strict-past sample. -/
theorem sampleSP_apply (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) {δ t : ℝ≥0}
    (hδ : 0 < δ) (ht : 0 < t) (htT : t ≤ T) (ω : Ω) :
    ⇑(sampleSP T hBmeas H ha K hb δ).val t ω = H (leftGrid δ t) ω := by
  classical
  let k := Nat.ceil (t / δ) - 1
  have hn : 0 < Nat.ceil (t / δ) := Nat.ceil_pos.mpr (div_pos ht hδ)
  have hk : k < sampleCells δ T :=
    (Nat.sub_lt hn (by decide)).trans_le
      (Nat.ceil_mono (div_le_div_of_nonneg_right htT ((zero_le : (0 : ℝ≥0) ≤ δ))))
  have hkt : t ∈ Ioc (δ * k) (δ * (k + 1)) := by
    simpa only [leftGrid, k, mul_add, mul_one] using leftGrid_mem_cell hδ ht
  have hpart : samplePartition δ T k = leftGrid δ t := by
    rw [samplePartition, min_eq_left (hkt.1.le.trans htT)]
    rfl
  rw [sampleSP_formula]
  rw [Finset.sum_eq_single k]
  · rw [Set.indicator_of_mem ((mem_sample_cell htT k).mpr hkt), hpart]
  · intro i hi hik
    apply Set.indicator_of_notMem
    intro hmem
    have hiCell := (mem_sample_cell htT i).mp hmem
    have heq : δ * i = δ * k := by
      rw [← leftGrid_eq_of_mem_cell hδ i hiCell, ← leftGrid_eq_of_mem_cell hδ k hkt]
    exact hik (by exact_mod_cast (mul_left_cancel₀ hδ.ne' heq))
  · intro hknot
    exact (hknot (Finset.mem_range.mpr hk)).elim

/-- Uniform boundedness of the finite approximants, including zero and the
region after the horizon. -/
theorem sampleSP_bound (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t)) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ t ω, |H t ω| ≤ K) {δ : ℝ≥0}
    (hδ : 0 < δ) (t : ℝ≥0) (ω : Ω) :
    |⇑(sampleSP T hBmeas H ha K hb δ).val t ω| ≤ K := by
  by_cases ht : t = 0
  · subst ht
    rw [sampleSP_formula]
    have hz : ∀ i ∈ Finset.range (sampleCells δ T),
        (Ioc (samplePartition δ T i) (samplePartition δ T (i + 1))).indicator
          (fun _ => H (samplePartition δ T i) ω) (0 : ℝ≥0) = 0 :=
      fun i _ => Set.indicator_of_notMem (fun h => (not_lt.mpr zero_le) h.1) _
    rw [Finset.sum_eq_zero hz, abs_zero]
    exact hK
  · by_cases htT : t ≤ T
    · rw [sampleSP_apply T hBmeas H ha K hb hδ (pos_iff_ne_zero.mpr ht) htT]
      exact hb _ _
    · rw [sampleSP_formula]
      have hzero : ∀ i ∈ Finset.range (sampleCells δ T),
          (Ioc (samplePartition δ T i) (samplePartition δ T (i + 1))).indicator
            (fun _ => H (samplePartition δ T i) ω) t = 0 := by
        intro i hi
        apply Set.indicator_of_notMem
        intro hmem
        exact htT (hmem.2.trans (min_le_right _ _))
      rw [Finset.sum_eq_zero hzero, abs_zero]
      exact hK

/-- The finite Brownian increment sum uses exactly the same cells as the
simple process, so its Itô integral is already the installed one. -/
theorem sampleSP_simpleSum (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) (δ t : ℝ≥0) (ω : Ω) :
    simpleSum B (samplePartition δ T) (fun i ω => H (samplePartition δ T i) ω)
      (sampleCells δ T) t ω =
      itoSimpleProcess hBmeas (sampleSP T hBmeas H ha K hb δ).val t ω := by
  let V := fun i => BoundedPredictableApproximation.stepSP hBmeas
    (a := samplePartition δ T i) (b := samplePartition δ T (i + 1))
    (samplePartition_mono δ T (Nat.le_succ i)) (min_le_right _ _)
    (ha _) (hb _)
  have hsum : ∀ n : ℕ,
      itoSimpleProcess hBmeas (∑ i ∈ Finset.range n, V i).val t ω =
        simpleSum B (samplePartition δ T) (fun i ω => H (samplePartition δ T i) ω) n t ω := by
    intro n
    induction n with
    | zero => simp [simpleSum, itoSimpleProcess, SimpleProcess.integral]
    | succ n ih =>
      rw [Finset.sum_range_succ, Submodule.coe_add, itoSimpleProcess_add]
      simp only [Pi.add_apply]
      rw [show itoSimpleProcess hBmeas (V n).val t ω =
          H (samplePartition δ T n) ω *
            (B (min (samplePartition δ T (n + 1)) t) ω -
              B (min (samplePartition δ T n) t) ω) from
        BoundedPredictableApproximation.itoSimpleProcess_stepSP hBmeas
          (samplePartition_mono δ T (Nat.le_succ n)) (min_le_right _ _) (ha _) (hb _) t ω]
      rw [ih]
      simp [simpleSum, Finset.sum_range_succ]
  exact (hsum (sampleCells δ T)).symm

/-- Squaring a simple sample introduces no cross terms, since the grid
cells are disjoint. -/
theorem sampleSP_sq_formula (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) {δ t : ℝ≥0}
    (hδ : 0 < δ) (ht : 0 < t) (htT : t ≤ T) (ω : Ω) :
    (⇑(sampleSP T hBmeas H ha K hb δ).val t ω) ^ 2 =
      ∑ i ∈ Finset.range (sampleCells δ T),
        (Ioc (samplePartition δ T i) (samplePartition δ T (i + 1))).indicator
          (fun _ => (H (samplePartition δ T i) ω) ^ 2) t := by
  classical
  let k := Nat.ceil (t / δ) - 1
  have hn : 0 < Nat.ceil (t / δ) := Nat.ceil_pos.mpr (div_pos ht hδ)
  have hk : k < sampleCells δ T :=
    (Nat.sub_lt hn (by decide)).trans_le
      (Nat.ceil_mono (div_le_div_of_nonneg_right htT ((zero_le : (0 : ℝ≥0) ≤ δ))))
  have hkt : t ∈ Ioc (δ * k) (δ * (k + 1)) := by
    simpa only [leftGrid, k, mul_add, mul_one] using leftGrid_mem_cell hδ ht
  have hpart : samplePartition δ T k = leftGrid δ t := by
    rw [samplePartition, min_eq_left (hkt.1.le.trans htT)]
    rfl
  rw [sampleSP_apply T hBmeas H ha K hb hδ ht htT]
  rw [Finset.sum_eq_single k]
  · rw [Set.indicator_of_mem ((mem_sample_cell htT k).mpr hkt), hpart]
  · intro i hi hik
    apply Set.indicator_of_notMem
    intro hmem
    have hiCell := (mem_sample_cell htT i).mp hmem
    have heq : δ * i = δ * k := by
      rw [← leftGrid_eq_of_mem_cell hδ i hiCell, ← leftGrid_eq_of_mem_cell hδ k hkt]
    exact hik (by exact_mod_cast (mul_left_cancel₀ hδ.ne' heq))
  · intro hknot
    exact (hknot (Finset.mem_range.mpr hk)).elim

/-- The finite exponential bracket equals the time integral of the square
of the very same finite simple process, on every smaller horizon. -/
theorem sampleSP_bracket (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) {δ : ℝ≥0} (hδ : 0 < δ)
    (u : ℝ≥0) (hu : u ≤ T) (ω : Ω) :
    simpleBracket (samplePartition δ T) (fun i ω => H (samplePartition δ T i) ω)
      (sampleCells δ T) u ω =
      ∫ s in Ioc (0 : ℝ≥0) u, (⇑(sampleSP T hBmeas H ha K hb δ).val s ω) ^ 2 ∂timeMeasure := by
  letI : IsFiniteMeasure (timeMeasure.restrict (Ioc (0 : ℝ≥0) u)) :=
    inferInstanceAs (IsFiniteMeasure (timeMeasure_T u))
  have htoReal : ∀ i : ℕ,
      (timeMeasure (Ioc (0 : ℝ≥0) u ∩
          Ioc (samplePartition δ T i) (samplePartition δ T (i + 1)))).toReal =
        ((min (samplePartition δ T (i + 1)) u : ℝ≥0) : ℝ) -
          ((min (samplePartition δ T i) u : ℝ≥0) : ℝ) := by
    intro i
    have hi := samplePartition_mono δ T (Nat.le_succ i)
    rw [Set.inter_comm, timeMeasure_Ioc_inter, NNReal.coe_zero,
      max_eq_left (samplePartition δ T i).coe_nonneg, NNReal.coe_min, NNReal.coe_min]
    by_cases hit : samplePartition δ T i ≤ u
    · rw [ENNReal.toReal_ofReal (by
          have hle : (samplePartition δ T i : ℝ) ≤
              min (samplePartition δ T (i + 1) : ℝ) u :=
            le_min (by exact_mod_cast hi) (by exact_mod_cast hit)
          linarith), min_eq_left (by exact_mod_cast hit : (samplePartition δ T i : ℝ) ≤ u)]
    · have hlow : (u : ℝ) ≤ samplePartition δ T i := by exact_mod_cast (not_le.mp hit).le
      have hhigh : (u : ℝ) ≤ samplePartition δ T (i + 1) :=
        hlow.trans (by exact_mod_cast hi)
      rw [min_eq_right hhigh, min_eq_right hlow, sub_self,
        ENNReal.ofReal_eq_zero.mpr (by linarith), ENNReal.toReal_zero]
  have hsq : Set.EqOn (fun s => (⇑(sampleSP T hBmeas H ha K hb δ).val s ω) ^ 2)
      (fun s => ∑ i ∈ Finset.range (sampleCells δ T),
        (Ioc (samplePartition δ T i) (samplePartition δ T (i + 1))).indicator
          (fun _ => (H (samplePartition δ T i) ω) ^ 2) s) (Ioc (0 : ℝ≥0) u) := by
    intro s hs
    exact sampleSP_sq_formula T hBmeas H ha K hb hδ hs.1 (hs.2.trans hu) ω
  have hint : ∀ i ∈ Finset.range (sampleCells δ T), Integrable
      (fun s => (Ioc (samplePartition δ T i) (samplePartition δ T (i + 1))).indicator
        (fun _ => (H (samplePartition δ T i) ω) ^ 2) s)
      (timeMeasure.restrict (Ioc (0 : ℝ≥0) u)) :=
    fun i _ => (integrable_const _).indicator measurableSet_Ioc
  rw [setIntegral_congr_fun measurableSet_Ioc hsq, integral_finsetSum _ hint, simpleBracket]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul,
    Measure.real_def, htoReal i, mul_comm]
  simp only [NNReal.coe_min]

/-- Continuous adapted real paths are strongly predictable. -/
theorem stronglyMeasurable_uncurry {H : ℝ≥0 → Ω → ℝ}
    (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) :
    StronglyMeasurable[F.predictable] (Function.uncurry H) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply stronglyMeasurable_of_tendsto atTop
    (fun n : ℕ => (measurable_sample ha
      (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity)).stronglyMeasurable)
  apply tendsto_pi_nhds.mpr
  intro z
  exact sample_tendsto hc z.1 z.2

/-- Predictability is obtained from adaptedness and continuity before L²
membership is constructed from the bound. -/
theorem integrandMemLp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) :
    MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  apply MemLp.of_bound (stronglyMeasurable_uncurry ha hc).aestronglyMeasurable K
  exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z.1 z.2

/-- The actual continuous adapted process in the installed integral domain. -/
def integrandLp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
  (integrandMemLp (μ := μ) T hBmeas H ha hc K hb).toLp (Function.uncurry H)

theorem integrandLp_coe (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) :
    (integrandLp (μ := μ) T hBmeas H ha hc K hb : ℝ≥0 × Ω → ℝ)
      =ᵐ[trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas] Function.uncurry H :=
  (integrandMemLp (μ := μ) T hBmeas H ha hc K hb).coeFn_toLp

theorem integrandLp_bound (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) :
    ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas),
      |integrandLp (μ := μ) T hBmeas H ha hc K hb z| ≤ K := by
  filter_upwards [integrandLp_coe (μ := μ) T hBmeas H ha hc K hb] with z hz
  rw [hz]
  exact hb z.1 z.2

/-- Identifying the L² representative in the ordinary product measure is
essential before using Fubini to identify its pathwise bracket. -/
theorem integrandLp_coe_prod (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) :
    (integrandLp (μ := μ) T hBmeas H ha hc K hb : ℝ≥0 × Ω → ℝ)
      =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry H :=
  ae_of_ae_trim F.predictable_le_prod (integrandLp_coe (μ := μ) T hBmeas H ha hc K hb)

theorem integrandLp_sections (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) :
    ∀ᵐ ω ∂μ, (fun s => integrandLp (μ := μ) T hBmeas H ha hc K hb (s, ω))
      =ᵐ[timeMeasure_T T] (fun s => H s ω) := by
  have hp := integrandLp_coe_prod (μ := μ) T hBmeas H ha hc K hb
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure_T T)).quasiMeasurePreserving.ae hp
  exact Measure.ae_ae_of_ae_prod hs

/-- The bracket in the bounded-predictable estimate is the original input's
time-square integral, rather than an unconnected chosen representative. -/
theorem integrandLp_bracket (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) :
    ∀ᵐ ω ∂μ,
      (∫ s in Ioc (0 : ℝ≥0) T, (integrandLp (μ := μ) T hBmeas H ha hc K hb (s, ω)) ^ 2 ∂timeMeasure) =
        ∫ s in Ioc (0 : ℝ≥0) T, (H s ω) ^ 2 ∂timeMeasure := by
  filter_upwards [integrandLp_sections (μ := μ) T hBmeas H ha hc K hb] with ω hω
  exact integral_congr_ae (hω.mono fun s hs => congrArg (fun x : ℝ => x ^ 2) hs)

/-- Trimming does not alter the energy of the actual integrand. -/
theorem integrandLp_norm_sq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) (K : ℝ)
    (hb : ∀ t ω, |H t ω| ≤ K) :
    ‖integrandLp (μ := μ) T hBmeas H ha hc K hb‖ ^ 2 =
      ∫ z, (H z.1 z.2) ^ 2 ∂((timeMeasure_T T).prod μ) := by
  rw [lp_two_norm_sq]
  have heq : (fun z => (integrandLp (μ := μ) T hBmeas H ha hc K hb z) ^ 2)
      =ᵐ[trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas] fun z => (H z.1 z.2) ^ 2 :=
    (integrandLp_coe (μ := μ) T hBmeas H ha hc K hb).mono fun z hz => congrArg (fun x : ℝ => x ^ 2) hz
  rw [integral_congr_ae heq]
  exact (integral_trim F.predictable_le_prod
    ((stronglyMeasurable_uncurry ha hc).pow 2)).symm

/-- Difference energy is preserved when the original continuous processes
are embedded in the predictable L² domain. -/
theorem integrandLp_sub_norm_sq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H G : ℝ≥0 → Ω → ℝ)
    (haH : ∀ t, Measurable[F t] (H t)) (haG : ∀ t, Measurable[F t] (G t))
    (hcH : ∀ ω, Continuous (fun t => H t ω))
    (hcG : ∀ ω, Continuous (fun t => G t ω)) (KH KG : ℝ)
    (hbH : ∀ t ω, |H t ω| ≤ KH) (hbG : ∀ t ω, |G t ω| ≤ KG) :
    ‖integrandLp (μ := μ) T hBmeas H haH hcH KH hbH -
      integrandLp (μ := μ) T hBmeas G haG hcG KG hbG‖ ^ 2 =
      ∫ z, (H z.1 z.2 - G z.1 z.2) ^ 2 ∂((timeMeasure_T T).prod μ) := by
  rw [lp_two_norm_sq]
  have heq : (fun z => ((integrandLp (μ := μ) T hBmeas H haH hcH KH hbH -
      integrandLp (μ := μ) T hBmeas G haG hcG KG hbG) z) ^ 2)
      =ᵐ[trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas]
        fun z => (H z.1 z.2 - G z.1 z.2) ^ 2 := by
    filter_upwards [Lp.coeFn_sub (integrandLp (μ := μ) T hBmeas H haH hcH KH hbH)
      (integrandLp (μ := μ) T hBmeas G haG hcG KG hbG),
      integrandLp_coe (μ := μ) T hBmeas H haH hcH KH hbH,
      integrandLp_coe (μ := μ) T hBmeas G haG hcG KG hbG] with z hz hH hG
    rw [hz, Pi.sub_apply, hH, hG]
    rfl
  rw [integral_congr_ae heq]
  exact (integral_trim F.predictable_le_prod
    (((stronglyMeasurable_uncurry haH hcH).sub
      (stronglyMeasurable_uncurry haG hcG)).pow 2)).symm

/-- The finite time measure has total real mass equal to the horizon. -/
theorem timeMeasure_T_real_univ (T : ℝ≥0) : (timeMeasure_T T).real Set.univ = T := by
  rw [Measure.real_def, timeMeasure_T, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, timeMeasure_Ioc]
  simp

/-- A pointwise Lipschitz bound by a sample-dependent L² random variable
gives the precise `T L²` coefficient-energy bound used by Picard iteration. -/
theorem integrandLp_sub_norm_sq_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (H G : ℝ≥0 → Ω → ℝ)
    (haH : ∀ t, Measurable[F t] (H t)) (haG : ∀ t, Measurable[F t] (G t))
    (hcH : ∀ ω, Continuous (fun t => H t ω))
    (hcG : ∀ ω, Continuous (fun t => G t ω)) (KH KG : ℝ)
    (hbH : ∀ t ω, |H t ω| ≤ KH) (hbG : ∀ t ω, |G t ω| ≤ KG)
    (R : Ω → ℝ) (hR : MemLp R 2 μ) (L : ℝ)
    (hdiff : ∀ t, t ≤ T → ∀ ω, |H t ω - G t ω| ≤ L * R ω) :
    ‖integrandLp (μ := μ) T hBmeas H haH hcH KH hbH -
      integrandLp (μ := μ) T hBmeas G haG hcG KG hbG‖ ^ 2 ≤
      (T : ℝ) * L ^ 2 * ∫ ω, (R ω) ^ 2 ∂μ := by
  rw [integrandLp_sub_norm_sq]
  have hsm : StronglyMeasurable (fun z : ℝ≥0 × Ω => H z.1 z.2 - G z.1 z.2) :=
    ((stronglyMeasurable_uncurry haH hcH).sub
      (stronglyMeasurable_uncurry haG hcG)).mono F.predictable_le_prod
  have hmem : MemLp (fun z : ℝ≥0 × Ω => H z.1 z.2 - G z.1 z.2) 2
      ((timeMeasure_T T).prod μ) := by
    apply MemLp.of_bound hsm.aestronglyMeasurable (KH + KG)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add (hbH _ _) (hbG _ _))
  have hrhs : Integrable (fun z : ℝ≥0 × Ω => L ^ 2 * (R z.2) ^ 2)
      ((timeMeasure_T T).prod μ) :=
    (hR.integrable_sq.comp_snd (timeMeasure_T T)).const_mul (L ^ 2)
  have hwindow : ∀ᵐ z ∂((timeMeasure_T T).prod μ), z.1 ≤ T := by
    have ht : ∀ᵐ t ∂(timeMeasure_T T), t ≤ T :=
      (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ht.2
    exact (Measure.quasiMeasurePreserving_fst (μ := timeMeasure_T T) (ν := μ)).ae ht
  calc
    (∫ z, (H z.1 z.2 - G z.1 z.2) ^ 2 ∂((timeMeasure_T T).prod μ)) ≤
        ∫ z, L ^ 2 * (R z.2) ^ 2 ∂((timeMeasure_T T).prod μ) := by
      apply integral_mono_ae hmem.integrable_sq hrhs
      filter_upwards [hwindow] with z hz
      have h := mul_self_le_mul_self (abs_nonneg (H z.1 z.2 - G z.1 z.2))
        (hdiff z.1 hz z.2)
      nlinarith [sq_abs (H z.1 z.2 - G z.1 z.2)]
    _ = (T : ℝ) * L ^ 2 * ∫ ω, (R ω) ^ 2 ∂μ := by
      rw [integral_const_mul]
      have heq : (∫ z : ℝ≥0 × Ω, (R z.2) ^ 2 ∂((timeMeasure_T T).prod μ)) =
          (∫ t : ℝ≥0, (1 : ℝ) ∂timeMeasure_T T) * ∫ ω, (R ω) ^ 2 ∂μ := by
        simpa only [one_mul] using integral_prod_mul
          (μ := timeMeasure_T T) (ν := μ) (fun _ : ℝ≥0 => (1 : ℝ)) (fun ω => (R ω) ^ 2)
      rw [heq, integral_const, smul_eq_mul, mul_one, timeMeasure_T_real_univ]
      ring

/-- A continuous bounded coefficient of a continuous adapted state has the
required adapted real sections. This works in particular for `E = Fin d → ℝ`. -/
theorem measurable_comp_sections {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {Z : ℝ≥0 → Ω → E} (ha : ∀ t, Measurable[F t] (Z t))
    {g : E → ℝ} (hg : Continuous g) :
    ∀ t, Measurable[F t] (fun ω => g (Z t ω)) :=
  fun t => hg.measurable.comp (ha t)

theorem continuous_comp_paths {E : Type*} [TopologicalSpace E]
    {Z : ℝ≥0 → Ω → E} (hc : ∀ ω, Continuous (fun t => Z t ω))
    {g : E → ℝ} (hg : Continuous g) :
    ∀ ω, Continuous (fun t => g (Z t ω)) :=
  fun ω => hg.comp (hc ω)

/-- The concrete input class for a bounded continuous coefficient of a state. -/
def coefficientLp {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : ℝ≥0 → Ω → E) (ha : ∀ t, Measurable[F t] (Z t))
    (hc : ∀ ω, Continuous (fun t => Z t ω))
    (g : E → ℝ) (hg : Continuous g) (K : ℝ) (hb : ∀ x, |g x| ≤ K) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
  integrandLp (μ := μ) T hBmeas (fun t ω => g (Z t ω))
    (measurable_comp_sections ha hg) (continuous_comp_paths hc hg) K (fun t ω => hb (Z t ω))

section Exponential
open ContinuousItoElementary AdaptedContinuousSpace
open BoundedPredictableApproximation
variable [IsFilteredPreBrownian B F μ]

/-- The installed bounded-predictable maximal inequality now accepts an
actual continuous adapted bounded input, with its original time-square bracket. -/
theorem bounded_continuous_adapted_exponential_maximal (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ t ω, |H t ω| ≤ K) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q) :
    μ {ω | (∃ t : Icc (0 : ℝ≥0) T,
        r ≤ representative (continuousIto T hB hBmeas
          (integrandLp (μ := μ) T hBmeas H ha hc K hb)) ω t) ∧
      (∫ s in Ioc (0 : ℝ≥0) T, (H s ω) ^ 2 ∂timeMeasure) ≤ q} ≤
        ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q))) := by
  have hmax := bounded_predictable_exponential_maximal T hB hBmeas hnull hK
    (integrandLp (μ := μ) T hBmeas H ha hc K hb) (integrandLp_bound (μ := μ) T hBmeas H ha hc K hb) hr hq
  apply le_trans (measure_mono_ae ?_) hmax
  filter_upwards [integrandLp_bracket (μ := μ) T hBmeas H ha hc K hb] with ω hω
  intro hevent
  exact ⟨hevent.1, by simpa only [hω] using hevent.2⟩

end Exponential
end Ripple.Stochastic.ContinuousAdaptedIntegrand

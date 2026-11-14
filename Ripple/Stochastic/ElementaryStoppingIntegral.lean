import Ripple.Stochastic.FilteredItoIntegralProcess

/-!
# Elementary integration stopped on a finite deterministic grid

The survival coefficients are measurable at the left cell endpoints. For a
stopping time taking values in the grid, the elementary mask integral telescopes
pathwise. Associativity then gives the stopped-integrand identity for every
installed simple process. No regularity of the integrator is used here.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Ripple.Stochastic.ElementaryStoppingIntegral

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}

/-- A single survival cell, with its coefficient observed at the left endpoint. -/
def survivalCell (a b : ℝ≥0) (hab : a ≤ b) (τ : Ω → ℝ≥0)
    (hτ : MeasurableSet[F a] {ω | a < τ ω}) : SimpleProcess ℝ F where
  valueBot := 0
  value := Finsupp.single (a, b) ({ω | a < τ ω}.indicator (fun _ => (1 : ℝ)))
  le_of_mem_support_value := by
    intro p hp
    obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
    exact hab
  measurable_valueBot := measurable_const
  measurable_value' := by
    intro p hp
    obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
    rw [Finsupp.single_eq_same]
    exact measurable_const.indicator hτ
  bounded_valueBot := ⟨0, by simp⟩
  bounded_value := by
    refine ⟨1, fun p hp ω => ?_⟩
    obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
    rw [Finsupp.single_eq_same]
    by_cases h : a < τ ω <;> simp [h]

/-- The strict survival event belongs to the current sigma algebra. -/
theorem measurableSet_survival {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0))) (a : ℝ≥0) :
    MeasurableSet[F a] {ω | a < τ ω} := by
  have h := (hτ.measurableSet_le a).compl
  simpa only [Set.compl_setOf, WithTop.coe_le_coe, not_le] using h

/-- Finite-grid survival mask as a genuine installed simple process. -/
def survivalGrid (q : ℕ → ℝ≥0) (hq : Monotone q) (N : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ i, MeasurableSet[F (q i)] {ω | q i < τ ω}) :
    SimpleProcess ℝ F :=
  ∑ i ∈ Finset.range N, survivalCell (q i) (q (i + 1))
    (hq (Nat.le_succ i)) τ (hτ i)

/-- Prefix sums of adjacent increments telescope, also when the prefix is empty. -/
theorem sum_prefix_increments (f : ℕ → ℝ) {k N : ℕ} (hk : k ≤ N) :
    (∑ i ∈ Finset.range N, if i < k then f (i + 1) - f i else 0) = f k - f 0 := by
  have hsum : (∑ i ∈ Finset.range N, if i < k then f (i + 1) - f i else 0) =
      ∑ i ∈ Finset.range k, (f (i + 1) - f i) := by
    symm
    calc
      (∑ i ∈ Finset.range k, (f (i + 1) - f i)) =
          ∑ i ∈ Finset.range k, if i < k then f (i + 1) - f i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos (Finset.mem_range.mp hi)]
      _ = ∑ i ∈ Finset.range N, if i < k then f (i + 1) - f i else 0 := by
        apply Finset.sum_subset (Finset.range_mono hk)
        intro i hi hik
        simp only [Finset.mem_range] at hik
        rw [if_neg hik]
  have ht : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, (f (i + 1) - f i)) = f n - f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [hsum]
  exact ht k

/-- Pointwise value of a single survival cell. -/
theorem survivalCell_apply (a b : ℝ≥0) (hab : a ≤ b) (τ : Ω → ℝ≥0)
    (hτ : MeasurableSet[F a] {ω | a < τ ω}) (s : ℝ≥0) (ω : Ω) :
    survivalCell a b hab τ hτ s ω =
      if a < τ ω then (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s else 0 := by
  rw [SimpleProcess.apply_eq]
  simp only [survivalCell, Pi.zero_apply, Set.indicator_zero', zero_add]
  rw [Finsupp.sum_single_index (by simp)]
  by_cases h : a < τ ω <;> by_cases hs : s ∈ Set.Ioc a b <;> simp [h, hs]

/-- Adjacent interval indicators are differences of upper-ray cut indicators. -/
theorem cell_indicator_eq_cut_sub (a b s : ℝ≥0) (hab : a ≤ b) :
    (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s =
      (if s ≤ b then 1 else 0) - (if s ≤ a then 1 else 0) := by
  by_cases ha : s ≤ a
  · have hb := ha.trans hab
    simp [ha, hb, Set.mem_Ioc, not_lt_of_ge ha]
  · by_cases hb : s ≤ b <;> simp [ha, hb, Set.mem_Ioc, lt_of_not_ge ha]

/-- The finite simple process is exactly the stochastic-interval indicator,
including its zero value at time zero. -/
theorem survivalGrid_apply (q : ℕ → ℝ≥0) (hq : StrictMono q) (hz : q 0 = 0)
    (N : ℕ) (τ : Ω → ℝ≥0)
    (hτ : ∀ i, MeasurableSet[F (q i)] {ω | q i < τ ω})
    (hgrid : ∀ ω, ∃ k ≤ N, τ ω = q k) (s : ℝ≥0) (ω : Ω) :
    survivalGrid q hq.monotone N τ hτ s ω =
      if 0 < s ∧ s ≤ τ ω then 1 else 0 := by
  have hsum : ∀ n : ℕ, survivalGrid q hq.monotone n τ hτ s ω =
      ∑ i ∈ Finset.range n, if q i < τ ω then
        (Set.Ioc (q i) (q (i + 1))).indicator (fun _ => (1 : ℝ)) s else 0 := by
    intro n
    induction n with
    | zero => simp [survivalGrid, SimpleProcess.coe_zero]
    | succ n ih =>
        rw [survivalGrid, Finset.sum_range_succ, SimpleProcess.coe_add]
        simp only [Pi.add_apply]
        rw [show (∑ i ∈ Finset.range n, survivalCell (q i) (q (i + 1))
          (hq.monotone (Nat.le_succ i)) τ (hτ i)) s ω = _ from ih]
        rw [survivalCell_apply, Finset.sum_range_succ]
  obtain ⟨k, hk, he⟩ := hgrid ω
  rw [hsum N, he]
  simp_rw [hq.lt_iff_lt, cell_indicator_eq_cut_sub _ _ _ (hq.monotone (Nat.le_succ _))]
  rw [sum_prefix_increments (fun i => if s ≤ q i then (1 : ℝ) else 0) hk, hz]
  by_cases hs : s = 0
  · simp [hs]
  · have hp : 0 < s := pos_iff_ne_zero.mpr hs
    by_cases hk' : s ≤ q k <;> simp [hs, hp, hk']

/-- A survival cell contributes exactly one masked increment. -/
theorem integral_survivalCell (a b : ℝ≥0) (hab : a ≤ b) (τ : Ω → ℝ≥0)
    (hτ : MeasurableSet[F a] {ω | a < τ ω}) (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ)
        (survivalCell a b hab τ hτ) X (t : WithTop ℝ≥0) ω =
      if a < τ ω then X (min b t) ω - X (min a t) ω else 0 := by
  simp only [SimpleProcess.integral, survivalCell]
  rw [Finsupp.sum_single_index (by simp)]
  have hstop (s : ℝ≥0) : stoppedProcess X (fun _ => (t : WithTop ℝ≥0)) s ω =
      X (min s t) ω := by
    simp only [stoppedProcess, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [hstop, hstop]
  by_cases h : a < τ ω <;> simp [h]

/-- Expand the integral of the finite survival grid before using the grid-valued stop. -/
theorem integral_survivalGrid_sum (q : ℕ → ℝ≥0) (hq : Monotone q) (N : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ i, MeasurableSet[F (q i)] {ω | q i < τ ω})
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ)
        (survivalGrid q hq N τ hτ) X (t : WithTop ℝ≥0) ω =
      ∑ i ∈ Finset.range N,
        if q i < τ ω then X (min (q (i + 1)) t) ω - X (min (q i) t) ω else 0 := by
  induction N with
  | zero => simp [survivalGrid, SimpleProcess.integral]
  | succ N ih =>
      rw [survivalGrid, Finset.sum_range_succ, SimpleProcess.integral_add_left]
      simp only [Pi.add_apply]
      rw [show SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ)
        (∑ i ∈ Finset.range N, survivalCell (q i) (q (i + 1))
          (hq (Nat.le_succ i)) τ (hτ i)) X (t : WithTop ℝ≥0) ω = _ from ih]
      rw [integral_survivalCell, Finset.sum_range_succ]

/-- The mask integral is the stopped increment of any real-valued process. -/
theorem integral_survivalGrid (q : ℕ → ℝ≥0) (hq : StrictMono q) (hz : q 0 = 0)
    (N : ℕ) (τ : Ω → ℝ≥0)
    (hτ : ∀ i, MeasurableSet[F (q i)] {ω | q i < τ ω})
    (hgrid : ∀ ω, ∃ k ≤ N, τ ω = q k)
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ)
        (survivalGrid q hq.monotone N τ hτ) X (t : WithTop ℝ≥0) ω =
      X (min t (τ ω)) ω - X 0 ω := by
  obtain ⟨k, hk, he⟩ := hgrid ω
  rw [integral_survivalGrid_sum, he]
  simp_rw [hq.lt_iff_lt]
  rw [sum_prefix_increments (fun i => X (min (q i) t) ω) hk, hz]
  simp [min_comm]

/-- Simple-process associativity converts stopping the integral into multiplying
its integrand by the finite-grid survival process. This equality holds for all
samples and times, so it is safe at random times. -/
theorem itoSimpleProcess_stopped_grid
    (B : ℝ≥0 → Ω → ℝ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ F) (q : ℕ → ℝ≥0)
    (hq : StrictMono q) (hz : q 0 = 0) (N : ℕ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hgrid : ∀ ω, ∃ k ≤ N, τ ω = q k) (t : ℝ≥0) (ω : Ω) :
    FilteredItoIntegralProcess.itoSimpleProcess hBmeas
      (SimpleProcess.map₂ (ContinuousLinearMap.mul ℝ ℝ)
        (survivalGrid q hq.monotone N τ (fun i => measurableSet_survival hτ (q i))) V) t ω =
      FilteredItoIntegralProcess.itoSimpleProcess hBmeas V (min t (τ ω)) ω := by
  let S := survivalGrid q hq.monotone N τ (fun i => measurableSet_survival hτ (q i))
  have hassoc := SimpleProcess.integral_assoc
    (B₁ := ContinuousLinearMap.mul ℝ ℝ) (B₂ := ContinuousLinearMap.mul ℝ ℝ)
    (B₃ := ContinuousLinearMap.mul ℝ ℝ) (B₄ := ContinuousLinearMap.mul ℝ ℝ)
    (fun x y z : ℝ => by simp only [ContinuousLinearMap.mul_apply']; ring) S V B
  have he := congrFun (congrFun hassoc (t : WithTop ℝ≥0)) ω
  have htel := integral_survivalGrid q hq hz N τ
    (fun i => measurableSet_survival hτ (q i)) hgrid
    (FilteredItoIntegralProcess.itoSimpleProcess hBmeas V) t ω
  change SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ) S
      (FilteredItoIntegralProcess.itoSimpleProcess hBmeas V) (t : WithTop ℝ≥0) ω = _ at he
  rw [htel, FilteredItoIntegralProcess.itoSimpleProcess_zero_time, Pi.zero_apply,
    sub_zero] at he
  exact he.symm

end Ripple.Stochastic.ElementaryStoppingIntegral

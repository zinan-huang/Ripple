import Ripple.sCRNUniversality.ClockedCTM.Unbounded
import Ripple.sCRNUniversality.Stochastic.ClockOccupation

/-!
Partial layer three of FIX3-SCWB-T41.

This file supplies first-error event infrastructure, the varying-rate clock
cone lemma, the exact scalar error series, conditional probability assembly,
and a finite reachable obstruction to unconditional tick progress.
The rawLaw one-window estimate and no-error progress theorem are not declared.
-/

namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction
open MeasureTheory
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-! ## Measurable first-error events -/

def BadTickAt (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (j : ℕ) : Prop :=
  TickAt C z₀ ω j ∧ ¬ WorkTerminal C (pathState (net C) z₀ ω j)

def FirstErrorAt (C : XCTM Q) (z₀ : State (Sp C))
    (ω : LabelPath C) (j : ℕ) : Prop :=
  BadTickAt C z₀ ω j ∧ ∀ m < j, ¬ BadTickAt C z₀ ω m

/-- The first erroneous tick occurs in the group of four windows indexed by n. -/
def firstErrorStep (C : XCTM Q) (z₀ : State (Sp C))
    (n : ℕ) : Set (LabelPath C) :=
  {ω | ∃ j, FirstErrorAt C z₀ ω j ∧ tickCount C z₀ ω j / 4 = n}

private theorem state_congr_of_prefix
    (C : XCTM Q) (z₀ : State (Sp C)) (ω ω' : LabelPath C) (j : ℕ)
    (h : ∀ k ≤ j, ω k = ω' k) :
    pathState (net C) z₀ ω j = pathState (net C) z₀ ω' j := by
  rw [← prefixToState_eq_pathState (net C) z₀ ω j,
    ← prefixToState_eq_pathState (net C) z₀ ω' j]
  congr 1
  funext k
  exact h k.val (Finset.mem_Iic.mp k.property)

private theorem fired_congr_of_prefix
    (C : XCTM Q) (z₀ : State (Sp C)) (ω ω' : LabelPath C) (j : ℕ)
    (h : ∀ k ≤ j + 1, ω k = ω' k) :
    pathFired (net C) z₀ ω j = pathFired (net C) z₀ ω' j := by
  have hz := state_congr_of_prefix C z₀ ω ω' j
    (fun k hk => h k (hk.trans (Nat.le_succ j)))
  unfold pathFired
  rw [h (j + 1) le_rfl]
  by_cases hT : (net C).Terminal (pathState (net C) z₀ ω' j)
  · have hT' : (net C).Terminal (pathState (net C) z₀ ω j) := hz ▸ hT
    rw [dif_pos hT', dif_pos hT]
  · have hT' : ¬ (net C).Terminal (pathState (net C) z₀ ω j) := hz ▸ hT
    rw [dif_neg hT', dif_neg hT]
    simp only [hz]

private theorem tick_congr_of_prefix
    (C : XCTM Q) (z₀ : State (Sp C)) (ω ω' : LabelPath C) (j : ℕ)
    (h : ∀ k ≤ j + 1, ω k = ω' k) :
    TickAt C z₀ ω j ↔ TickAt C z₀ ω' j := by
  simp only [TickAt, firedTick, fired_congr_of_prefix C z₀ ω ω' j h]

private theorem count_congr_of_prefix
    (C : XCTM Q) (z₀ : State (Sp C)) (ω ω' : LabelPath C) :
    ∀ j, (∀ k ≤ j, ω k = ω' k) →
      tickCount C z₀ ω j = tickCount C z₀ ω' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro h
      have hc := ih (fun k hk => h k (hk.trans (Nat.le_succ j)))
      have ht := tick_congr_of_prefix C z₀ ω ω' j h
      simp only [tickCount, hc]
      split_ifs with h1 h2 <;> first | rfl | (exfalso; tauto)

private theorem measurableSet_of_prefix
    (C : XCTM Q) (n : ℕ) (P : LabelPath C → Prop)
    (h : ∀ ω ω',
      Preorder.frestrictLe n ω = Preorder.frestrictLe n ω' →
        (P ω ↔ P ω')) :
    MeasurableSet {ω | P ω} := by
  classical
  have hf : Measurable (fun ω : LabelPath C => if P ω then (1 : ℕ) else 0) := by
    apply MassAction.measurable_of_frestrictLe (net C) n
    intro ω ω' hω
    simp only [h ω ω' hω]
  have hset : {ω : LabelPath C | P ω} =
      (fun ω : LabelPath C => if P ω then (1 : ℕ) else 0) ⁻¹' {1} := by
    ext ω
    by_cases hω : P ω <;> simp [hω]
  rw [hset]
  exact hf (measurableSet_singleton 1)

theorem measurableSet_badTickAt
    (C : XCTM Q) (z₀ : State (Sp C)) (j : ℕ) :
    MeasurableSet {ω : LabelPath C | BadTickAt C z₀ ω j} := by
  apply measurableSet_of_prefix C (j + 1)
  intro ω ω' heq
  have h : ∀ k ≤ j + 1, ω k = ω' k := by
    intro k hk
    exact congrFun heq ⟨k, Finset.mem_Iic.mpr hk⟩
  have hz := state_congr_of_prefix C z₀ ω ω' j
    (fun k hk => h k (hk.trans (Nat.le_succ j)))
  have ht := tick_congr_of_prefix C z₀ ω ω' j h
  simp only [BadTickAt, hz, ht]

theorem measurable_tickCount
    (C : XCTM Q) (z₀ : State (Sp C)) (j : ℕ) :
    Measurable (fun ω : LabelPath C => tickCount C z₀ ω j) := by
  apply MassAction.measurable_of_frestrictLe (net C) j
  intro ω ω' heq
  apply count_congr_of_prefix C z₀ ω ω' j
  intro k hk
  exact congrFun heq ⟨k, Finset.mem_Iic.mpr hk⟩

theorem measurableSet_firstErrorAt
    (C : XCTM Q) (z₀ : State (Sp C)) (j : ℕ) :
    MeasurableSet {ω : LabelPath C | FirstErrorAt C z₀ ω j} := by
  have hbefore : MeasurableSet
      {ω : LabelPath C | ∀ m < j, ¬ BadTickAt C z₀ ω m} := by
    simp_rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro m
    apply MeasurableSet.iInter
    intro _
    exact (measurableSet_badTickAt C z₀ m).compl
  exact (measurableSet_badTickAt C z₀ j).inter hbefore

theorem measurableSet_firstErrorStep
    (C : XCTM Q) (z₀ : State (Sp C)) (n : ℕ) :
    MeasurableSet (firstErrorStep C z₀ n) := by
  have hset : firstErrorStep C z₀ n =
      ⋃ j, {ω : LabelPath C | FirstErrorAt C z₀ ω j} ∩
        {ω | tickCount C z₀ ω j / 4 = n} := by
    ext ω
    simp [firstErrorStep]
  rw [hset]
  apply MeasurableSet.iUnion
  intro j
  apply (measurableSet_firstErrorAt C z₀ j).inter
  apply measurableSet_of_prefix C j
  intro ω ω' heq
  have hc : tickCount C z₀ ω j = tickCount C z₀ ω' j := by
    apply count_congr_of_prefix C z₀ ω ω' j
    intro k hk
    exact congrFun heq ⟨k, Finset.mem_Iic.mpr hk⟩
  rw [hc]

theorem error_eq_iUnion_firstErrorStep
    (C : XCTM Q) (z₀ : State (Sp C)) :
    {ω : LabelPath C | Error C z₀ ω} = ⋃ n, firstErrorStep C z₀ n := by
  classical
  ext ω
  constructor
  · intro hE
    have hex : ∃ j, BadTickAt C z₀ ω j := hE
    let j := Nat.find hex
    have hj : FirstErrorAt C z₀ ω j :=
      ⟨Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    exact Set.mem_iUnion.mpr ⟨tickCount C z₀ ω j / 4, j, hj, rfl⟩
  · intro hω
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
    obtain ⟨j, hj, _⟩ := hn
    exact ⟨j, hj.1⟩

theorem measurableSet_error (C : XCTM Q) (z₀ : State (Sp C)) :
    MeasurableSet {ω : LabelPath C | Error C z₀ ω} := by
  rw [error_eq_iUnion_firstErrorStep]
  exact MeasurableSet.iUnion (measurableSet_firstErrorStep C z₀)

theorem measurableSet_tickProgress (C : XCTM Q) (z₀ : State (Sp C)) :
    MeasurableSet {ω : LabelPath C | TickProgress C z₀ ω} := by
  have hset : {ω : LabelPath C | TickProgress C z₀ ω} =
      ⋂ k : ℕ, ⋃ j : ℕ, {ω | k ≤ tickCount C z₀ ω j} := by
    ext ω
    simp [TickProgress]
  rw [hset]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro j
  exact measurableSet_le measurable_const (measurable_tickCount C z₀ j)

/-! ## The clock cone with a lower bound on the effective upward rate -/

open Ripple.sCRNUniversality.Stochastic.ClockOccupation

private theorem clock_minimum_principle
    {l : ℕ} {a ρ : ℝ} {u : ℕ → ℝ}
    (hl : 2 ≤ l) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (hleft : 0 ≤ u 0) (hright : 0 ≤ u l)
    (hrec : ∀ m, 1 ≤ m → m + 1 ≤ l →
      0 ≤ (ρ + a + 1) * u m - a * u (m - 1) - u (m + 1)) :
    ∀ m, 1 ≤ m → m + 1 ≤ l → 0 ≤ u m := by
  classical
  by_contra hneg
  push_neg at hneg
  obtain ⟨m₀, hm₀one, hm₀last, hm₀neg⟩ := hneg
  have hne : (Finset.Icc 1 (l - 1)).Nonempty := ⟨1, by simp; omega⟩
  obtain ⟨mmin, hmin_mem, hmin⟩ :=
    (Finset.Icc 1 (l - 1)).exists_min_image u hne
  let v := u mmin
  have hvneg : v < 0 :=
    lt_of_le_of_lt (hmin m₀ (by simp; omega)) hm₀neg
  have hex : ∃ m, 1 ≤ m ∧ m + 1 ≤ l ∧ u m = v :=
    ⟨mmin, by simp at hmin_mem; omega,
      by simp at hmin_mem; omega, rfl⟩
  let m := Nat.find hex
  have hmone : 1 ≤ m := (Nat.find_spec hex).1
  have hmlast : m + 1 ≤ l := (Nat.find_spec hex).2.1
  have hmv : u m = v := (Nat.find_spec hex).2.2
  have hge : ∀ j, 1 ≤ j → j + 1 ≤ l → v ≤ u j :=
    fun j hjone hjlast => hmin j (by simp; omega)
  have hprev : v < u (m - 1) := by
    rcases Nat.eq_or_lt_of_le hmone with heq | hlt
    · rw [← heq, Nat.sub_self]
      exact hvneg.trans_le hleft
    · have hle := hge (m - 1) (by omega) (by omega)
      have hne' : u (m - 1) ≠ v := by
        intro heq
        have hminimal := Nat.find_min hex (show m - 1 < m by omega)
        exact hminimal ⟨by omega, by omega, heq⟩
      exact lt_of_le_of_ne hle (Ne.symm hne')
  have hnext : v ≤ u (m + 1) := by
    rcases Nat.eq_or_lt_of_le hmlast with heq | hlt
    · rw [heq]
      exact hvneg.le.trans hright
    · exact hge (m + 1) (by omega) (by omega)
  have hr := hrec m hmone hmlast
  rw [hmv] at hr
  have hρv : ρ * v ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hρ hvneg.le
  have haprev : a * v < a * u (m - 1) :=
    mul_lt_mul_of_pos_left hprev ha
  nlinarith

/-- Entries in the cone with parameter b produce occupations in that cone
when the actual normalized upward rate a is at least b. -/
theorem clockBalance_inCone_of_lower_ratio
    {a b ρ : ℝ} {w e : ℕ → ℝ}
    (h : ClockBalance 5 a ρ 1 w e)
    (hb : 0 < b) (hba : b ≤ a) (hρ : 0 ≤ ρ)
    (hw : ∀ c, c < 5 → 0 ≤ w c)
    (he : InCone 5 b e) :
    InCone 5 b w := by
  have hz := h 0 (by norm_num)
  have ho := h 1 (by norm_num)
  have ht := h 2 (by norm_num)
  have hh := h 3 (by norm_num)
  have hf := h 4 (by norm_num)
  norm_num [Ripple.sCRNUniversality.Stochastic.ClockOccupation.rate]
    at hz ho ht hh hf
  let u : ℕ → ℝ := fun m =>
    if m = 0 then w 0 else
    if m = 5 then (a - b) * w 4 else w m - b * w (m - 1)
  have huleft : 0 ≤ u 0 := by
    simpa [u] using hw 0 (by norm_num)
  have huright : 0 ≤ u 5 := by
    simpa [u] using
      mul_nonneg (sub_nonneg.mpr hba) (hw 4 (by norm_num))
  have hrec : ∀ m, 1 ≤ m → m + 1 ≤ 5 →
      0 ≤ (ρ + a + 1) * u m - a * u (m - 1) - u (m + 1) := by
    intro m hmone hmlast
    have hmfour : m ≤ 4 := by omega
    interval_cases m <;> norm_num [u]
    · have hid :
          (ρ + a + 1) * (w 1 - b * w 0) - a * w 0 -
              (w 2 - b * w 1) = e 1 - b * e 0 := by
        linear_combination ho - b * hz
      nlinarith [he 0 (by norm_num)]
    · have hid :
          (ρ + a + 1) * (w 2 - b * w 1) - a * (w 1 - b * w 0) -
              (w 3 - b * w 2) = e 2 - b * e 1 := by
        linear_combination ht - b * ho
      nlinarith [he 1 (by norm_num)]
    · have hid :
          (ρ + a + 1) * (w 3 - b * w 2) - a * (w 2 - b * w 1) -
              (w 4 - b * w 3) = e 3 - b * e 2 := by
        linear_combination hh - b * ht
      nlinarith [he 2 (by norm_num)]
    · have hid :
          (ρ + a + 1) * (w 4 - b * w 3) - a * (w 3 - b * w 2) -
              (a - b) * w 4 = e 4 - b * e 3 := by
        linear_combination hf - b * hh
      nlinarith [he 3 (by norm_num)]
  have hu := clock_minimum_principle (by norm_num : 2 ≤ (5 : ℕ))
    (lt_of_lt_of_le hb hba) hρ huleft huright hrec
  intro c hc
  have huc := hu (c + 1) (by omega) (by omega)
  have hcz : c + 1 ≠ 0 := by omega
  have hcf : c + 1 ≠ 5 := by omega
  simp only [u, if_neg hcz, if_neg hcf, Nat.add_sub_cancel] at huc
  exact sub_nonneg.mp huc

/-- The occupation inequality with the uniform lower ratio b. This is
a scalar statement; construction of the rawLaw occupations is separate. -/
theorem clockBalance_tick_le_of_lower_ratio
    {a b ρ : ℝ} {w e : ℕ → ℝ}
    (h : ClockBalance 5 a ρ 1 w e)
    (hb : 0 < b) (hba : b ≤ a) (hρ : 0 ≤ ρ)
    (hw : ∀ c, c < 5 → 0 ≤ w c)
    (he : InCone 5 b e) :
    w 0 * geomWeight b 5 ≤ psum w 5 ∧
      ρ * psum w 5 ≤ psum e 5 := by
  have hcone := clockBalance_inCone_of_lower_ratio h hb hba hρ hw he
  constructor
  · unfold geomWeight psum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    rw [mul_comm]
    exact ClockBalance.pow_mul_le_of_inCone hcone hb.le c
      (Finset.mem_range.mp hc)
  · have htotal := ClockBalance.total h (by norm_num)
    simp only [ClockBalance.u, one_mul] at htotal
    linarith [hw 0 (by norm_num)]

/-! ## The exact scalar error budget -/

theorem log_add_two_le_self {a : ℝ} (ha : 2 ≤ a) :
    Real.log (a + 2) ≤ a := by
  have hap : 0 < a + 2 := by linarith
  have hhalf := Real.log_le_sub_one_of_pos (show 0 < (a + 2) / 2 by positivity)
  have htwo := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  rw [Real.log_div hap.ne' (by norm_num)] at hhalf
  linarith

/-- Every restoration window is conservatively charged with factor 81;
the other three slots are charged with factor one. -/
theorem four_window_charge_le {a s : ℝ} (ha : 2 ≤ a) (hs : s ≤ a) :
    (∑ k ∈ Finset.range 4,
      (if k = 1 then (81 : ℝ) else 1) * 16 *
        (s + Real.log (a + 2)) / a ^ 4) ≤ 2688 / a ^ 3 := by
  have ha0 : 0 < a := by linarith
  have hlog := log_add_two_le_self ha
  have hsum :
      (∑ k ∈ Finset.range 4,
        (if k = 1 then (81 : ℝ) else 1) * 16 *
          (s + Real.log (a + 2)) / a ^ 4) =
        1344 * (s + Real.log (a + 2)) / a ^ 4 := by
    norm_num [Finset.sum_range_succ] <;> ring
  rw [hsum]
  calc
    1344 * (s + Real.log (a + 2)) / a ^ 4
        ≤ 1344 * (2 * a) / a ^ 4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    _ = 2688 / a ^ 3 := by
      field_simp [ha0.ne'] <;> ring

private theorem cubic_budget_step {x : ℝ} (hx : 1 < x) :
    2688 / x ^ 3 ≤ 1344 / (x - 1) ^ 2 - 1344 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have he :
      1344 / (x - 1) ^ 2 - 1344 / x ^ 2 =
        1344 * (2 * x - 1) / ((x - 1) ^ 2 * x ^ 2) := by
    field_simp [hx0.ne', hx1.ne'] <;> ring
  rw [he]
  apply (div_le_div_iff₀ (pow_pos hx0 3)
    (mul_pos (pow_pos hx1 2) (pow_pos hx0 2))).2
  have hlinear : 0 ≤ 3 * x - 2 := by linarith
  have hnonneg : 0 ≤ 1344 * x ^ 2 * (3 * x - 2) := by positivity
  nlinarith only [hnonneg]

theorem cubic_budget_prefix (i₀ N : ℕ) (hi : 1 < (i₀ : ℝ)) :
    (∑ n ∈ Finset.range N, 2688 / ((i₀ : ℝ) + (n : ℝ)) ^ 3) ≤
      errorBound i₀ - 1344 / ((i₀ : ℝ) + (N : ℝ) - 1) ^ 2 := by
  induction N with
  | zero => simp [errorBound]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hx : 1 < (i₀ : ℝ) + (N : ℝ) :=
        lt_of_lt_of_le hi (le_add_of_nonneg_right (Nat.cast_nonneg N))
      have hstep := cubic_budget_step hx
      calc
        (∑ n ∈ Finset.range N, 2688 / ((i₀ : ℝ) + (n : ℝ)) ^ 3) +
            2688 / ((i₀ : ℝ) + (N : ℝ)) ^ 3
            ≤ (errorBound i₀ - 1344 / ((i₀ : ℝ) + (N : ℝ) - 1) ^ 2) +
              (1344 / ((i₀ : ℝ) + (N : ℝ) - 1) ^ 2 -
                1344 / ((i₀ : ℝ) + (N : ℝ)) ^ 2) :=
          add_le_add ih hstep
        _ = errorBound i₀ -
              1344 / ((i₀ : ℝ) + ((N + 1 : ℕ) : ℝ) - 1) ^ 2 := by
          have hnext :
              (i₀ : ℝ) + ((N + 1 : ℕ) : ℝ) - 1 =
                (i₀ : ℝ) + (N : ℝ) := by push_cast; ring
          rw [hnext]
          ring

theorem cubic_budget_sum_range_le (i₀ N : ℕ) (hi : 1 < (i₀ : ℝ)) :
    (∑ n ∈ Finset.range N, 2688 / ((i₀ : ℝ) + (n : ℝ)) ^ 3) ≤
      errorBound i₀ :=
  (cubic_budget_prefix i₀ N hi).trans (sub_le_self _ (by positivity))

theorem cubic_error_series_le (i₀ : ℕ) (hi : 1 < (i₀ : ℝ)) :
    (∑' n : ℕ, ENNReal.ofReal (2688 / ((i₀ : ℝ) + (n : ℝ)) ^ 3)) ≤
      ENNReal.ofReal (errorBound i₀) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  rw [← ENNReal.ofReal_sum_of_nonneg
    (s := Finset.range N)
    (f := fun n : ℕ => 2688 / ((i₀ : ℝ) + (n : ℝ)) ^ 3)
    (by
      intro n hn
      positivity)]
  exact ENNReal.ofReal_le_ofReal (cubic_budget_sum_range_le i₀ N hi)

theorem admissibleAccuracy_gt_one {w : List Bool} {i₀ : ℕ} {δ : ℝ}
    (h : AdmissibleAccuracy w i₀ δ) : 1 < (i₀ : ℝ) := by
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.mpr h.2.1
  have hbase : 1 + 37 / Real.sqrt δ ≤ (i₀ : ℝ) :=
    (le_max_right _ _).trans h.2.2.2
  have hpos : 0 < 37 / Real.sqrt δ := by positivity
  linarith

theorem errorBound_le_accuracy {w : List Bool} {i₀ : ℕ} {δ : ℝ}
    (h : AdmissibleAccuracy w i₀ δ) : errorBound i₀ ≤ δ := by
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.mpr h.2.1
  have hbase : 1 + 37 / Real.sqrt δ ≤ (i₀ : ℝ) :=
    (le_max_right _ _).trans h.2.2.2
  have hx : 0 < (i₀ : ℝ) - 1 := by
    have hi := admissibleAccuracy_gt_one h
    linarith
  have hdiv : 37 / Real.sqrt δ ≤ (i₀ : ℝ) - 1 := by linarith
  have hmul : (37 : ℝ) ≤ ((i₀ : ℝ) - 1) * Real.sqrt δ :=
    (div_le_iff₀ hsqrt).mp hdiv
  have hsq : (37 : ℝ) ^ 2 ≤ (((i₀ : ℝ) - 1) * Real.sqrt δ) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hmul 2
  rw [mul_pow, Real.sq_sqrt h.2.1.le] at hsq
  unfold errorBound
  apply (div_le_iff₀ (pow_pos hx 2)).2
  nlinarith

/-! ## Conditional probability assembly; the stochastic premises are explicit -/

theorem countable_error_budget
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : ℕ → Set Ω) (i₀ : ℕ) (hi : 1 < (i₀ : ℝ))
    (hE : ∀ n, μ (E n) ≤
      ENNReal.ofReal (2688 / ((i₀ : ℝ) + (n : ℝ)) ^ 3)) :
    μ (⋃ n, E n) ≤ ENNReal.ofReal (errorBound i₀) :=
  (measure_iUnion_le E).trans
    ((ENNReal.tsum_le_tsum hE).trans (cubic_error_series_le i₀ hi))

theorem error_measure_le_of_firstErrorStep
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hi : 1 < (i₀ : ℝ))
    (hE : ∀ n,
      jumpLaw C i₀ w (firstErrorStep C (initial C i₀ w) n) ≤
        ENNReal.ofReal (2688 / ((i₀ : ℝ) + (n : ℝ)) ^ 3)) :
    jumpLaw C i₀ w {ω | Error C (initial C i₀ w) ω} ≤
      ENNReal.ofReal (errorBound i₀) := by
  rw [error_eq_iUnion_firstErrorStep]
  exact countable_error_budget (jumpLaw C i₀ w)
    (firstErrorStep C (initial C i₀ w)) i₀ hi hE

theorem ae_noError_simulatesAll_of_progress
    (C : XCTM Q) (i₀ : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (hprogress : ∀ᵐ ω ∂jumpLaw C i₀ w,
      ¬ Error C (initial C i₀ w) ω →
        TickProgress C (initial C i₀ w) ω) :
    ∀ᵐ ω ∂jumpLaw C i₀ w,
      ¬ Error C (initial C i₀ w) ω → SimulatesAll C i₀ w ω := by
  filter_upwards [hprogress] with ω hω hno
  exact simulatesAll_of_noError_progress C i₀ w hs ω hno (hω hno)

/-- This reducer does not assert either stochastic premise. -/
theorem errorClaim_of_estimates
    (C : XCTM Q)
    (herror : ∀ (w : List Bool) (i₀ : ℕ) (δ : ℝ),
      AdmissibleAccuracy w i₀ δ →
        jumpLaw C i₀ w {ω | Error C (initial C i₀ w) ω} ≤
          ENNReal.ofReal (errorBound i₀))
    (hprogress : ∀ (w : List Bool) (i₀ : ℕ) (δ : ℝ),
      AdmissibleAccuracy w i₀ δ →
        ∀ᵐ ω ∂jumpLaw C i₀ w,
          ¬ Error C (initial C i₀ w) ω →
            TickProgress C (initial C i₀ w) ω) :
    ErrorClaim C := by
  intro w i₀ δ hacc
  exact ⟨herror w i₀ δ hacc, errorBound_le_accuracy hacc,
    ae_noError_simulatesAll_of_progress C i₀ w hacc.1
      (hprogress w i₀ δ hacc)⟩

theorem tm_failure_measure_le_error_measure
    {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) (hb : M.blank = false)
    (s i₀ : ℕ) (input : List Bool)
    (hs : 1 ≤ s) (hi : input.length ≤ s)
    (hprogress : ∀ᵐ ω ∂jumpLaw (xctmOf M) i₀ (xencT (xInputTape s input)),
      ¬ Error (xctmOf M) (tmInitial M s i₀ input) ω →
        TickProgress (xctmOf M) (tmInitial M s i₀ input) ω) :
    jumpLaw (xctmOf M) i₀ (xencT (xInputTape s input))
        {ω | ¬ TMSimulatesAll M s i₀ input ω} ≤
      jumpLaw (xctmOf M) i₀ (xencT (xInputTape s input))
        {ω | Error (xctmOf M) (tmInitial M s i₀ input) ω} := by
  apply measure_mono_ae
  filter_upwards [hprogress] with ω hω hfail
  by_contra hno
  exact hfail (tmSimulatesAll_of_noError_progress M hb s i₀ input hs hi ω
    hno (hω hno))

/-- Conditional correctness from the existing ErrorClaim. -/
theorem tm_failure_bound_of_errorClaim
    {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) (hb : M.blank = false)
    (s i₀ : ℕ) (input : List Bool)
    (hs : 1 ≤ s) (hi : input.length ≤ s) {δ : ℝ}
    (hacc : AdmissibleAccuracy (xencT (xInputTape s input)) i₀ δ)
    (hclaim : ErrorClaim (xctmOf M)) :
    jumpLaw (xctmOf M) i₀ (xencT (xInputTape s input))
        {ω | ¬ TMSimulatesAll M s i₀ input ω} ≤
      ENNReal.ofReal (errorBound i₀) := by
  obtain ⟨herr, _, hsim⟩ := hclaim (xencT (xInputTape s input)) i₀ δ hacc
  have hprogress : ∀ᵐ ω ∂jumpLaw (xctmOf M) i₀ (xencT (xInputTape s input)),
      ¬ Error (xctmOf M) (tmInitial M s i₀ input) ω →
        TickProgress (xctmOf M) (tmInitial M s i₀ input) ω := by
    filter_upwards [hsim] with ω hω hno
    exact (hω hno).1
  exact (tm_failure_measure_le_error_measure M hb s i₀ input hs hi hprogress).trans herr

/-! ## A finite obstruction to unconditional almost-sure tick progress -/

namespace TMStarvationWitness

def tm : TM.Machine Unit Bool where
  start := ()
  blank := false
  delta _ _ := none

def machine : XCTM (XCS Unit) := xctmOf tm

def reader : ReadState machine := ⟨.gClear (), rfl⟩

def active : ActiveState machine := .inl reader

def tape : List Bool := xencT (xInputTape 1 [])

def start : State (Sp machine) := initial machine 38 tape

theorem tape_eq : tape = [true, false, true, false] := by
  decide +kernel

theorem start_eq_tmInitial : start = tmInitial tm 1 38 [] := rfl

theorem accuracy_admissible : AdmissibleAccuracy tape 38 1 := by
  rw [tape_eq]
  norm_num [AdmissibleAccuracy]

def execute : State (Sp machine) → List (Rx machine) → State (Sp machine)
  | z, [] => z
  | z, r :: rs => execute ((rxn machine r).fire z) rs

def wordEnabled : State (Sp machine) → List (Rx machine) → Bool
  | _, [] => true
  | z, r :: rs =>
      decide (rate machine r z ≠ 0) &&
        wordEnabled ((rxn machine r).fire z) rs

def downTick : List (Rx machine) :=
  [.down (3 : Fin 4) false, .down (2 : Fin 4) false,
   .down (1 : Fin 4) false, .down (0 : Fin 4) false, .tick false]

/-- Three early ticks leave a second-stage population together with a writer. -/
def trapWord : List (Rx machine) :=
  downTick ++ [.startSecond active, .growSecond active, .restoreT active] ++
  downTick ++ [.startThird active] ++
  downTick ++ [.startRead reader, .chooseRead reader false] ++
  List.replicate 25 (.growSecond active)

def trap : State (Sp machine) := execute start trapWord

def trapSpec : State (Sp machine)
  | .second a => if a = active then 26 else 0
  | .write q false => if q = reader then 1 else 0
  | .mem .md => tval tape
  | .mem .t => 1
  | .mem .td => 59
  | .mem .ds => 27
  | .mem .bs => 1
  | .forward => 1026
  | .backward => 27
  | .clock c => if c = Fin.last 4 then 1 else 0
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem prefix_certificate :
    trapWord.length = 46 ∧ wordEnabled start trapWord = true ∧
      (∀ s : Sp machine, trap s = trapSpec s) := by
  decide +kernel

theorem execute_reachable (z : State (Sp machine)) (rs : List (Rx machine))
    (h : wordEnabled z rs = true) :
    ReachBy machine (fun _ => True) z (execute z rs) := by
  induction rs generalizing z with
  | nil => exact Relation.ReflTransGen.refl
  | cons r rs ih =>
      change (decide (rate machine r z ≠ 0) &&
        wordEnabled ((rxn machine r).fire z) rs) = true at h
      rw [Bool.and_eq_true] at h
      obtain ⟨hr, hrs⟩ := h
      have he : (rxn machine r).enabled z :=
        (enabled_iff machine r z).mpr (of_decide_eq_true hr)
      have hfirst : ReachBy machine (fun _ => True) z ((rxn machine r).fire z) :=
        Relation.ReflTransGen.tail Relation.ReflTransGen.refl
          ⟨r, True.intro, he, rfl⟩
      exact hfirst.trans (ih _ hrs)

theorem trap_reachable : ReachBy machine (fun _ => True) start trap :=
  execute_reachable start trapWord prefix_certificate.2.1

def beforeSecondTick : State (Sp machine) :=
  execute start
    (downTick ++ [.startSecond active, .growSecond active, .restoreT active] ++
      [.down (3 : Fin 4) false, .down (2 : Fin 4) false,
       .down (1 : Fin 4) false, .down (0 : Fin 4) false])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem early_error_certificate :
    rate machine (.tick false) beforeSecondTick = 27 ∧
      rate machine (.growSecond active) beforeSecondTick = 50 := by
  decide +kernel

theorem beforeSecondTick_not_workTerminal :
    ¬ WorkTerminal machine beforeSecondTick := by
  intro hterminal
  have hen : (rxn machine (.growSecond active)).enabled beforeSecondTick := by
    rw [enabled_iff, early_error_certificate.2]
    decide +kernel
  exact hterminal (.growSecond active) rfl hen

def afterRestore : State (Sp machine) :=
  (rxn machine (.restoreD active)).fire trap

def afterCycle : State (Sp machine) :=
  (rxn machine (.readZero reader false)).fire afterRestore

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem forward_growth_cycle_certificate :
    rate machine (.restoreD active) trap = 702 ∧
      rate machine (.readZero reader false) afterRestore = 1 ∧
      (∀ s : Sp machine,
        afterCycle s = trap s + (if s = .forward then 1 else 0) +
          (if s = .mem .k1 then 3 else 0)) := by
  decide +kernel

theorem starvation_bound_strict :
    (53 * 27 ^ 4 : ℚ) / (78 * 1025 ^ 3) < 1 ∧
      (53 * 27 ^ 4 : ℚ) / (78 * 1025 ^ 3) < 1 / 1000 := by
  decide +kernel

end TMStarvationWitness

end Ripple.sCRNUniversality.ClockedCTM.Unbounded

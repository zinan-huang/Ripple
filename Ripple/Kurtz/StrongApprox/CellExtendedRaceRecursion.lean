-- Ripple/Kurtz/StrongApprox/CellExtendedRaceRecursion.lean
import Ripple.Kurtz.StrongApprox.CellExtendedRandomTime
import Ripple.Kurtz.StrongApprox.PositiveRaceKernel

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellExtendedRaceRecursion

open MeasureTheory ProbabilityTheory Set Filter Topology Preorder
open scoped ENNReal NNReal BigOperators
open ExponentialRace
open CellRandomTimeEvaluation CellStoppingLineFreshness
open CellStoppingLineResiduals CellStoppingLineAdapters
open CellExtendedStoppingLine CellExtendedRandomTime

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def extendedResidualWaitE
    (σ : ExtendedCellLine ι) (c : CellFamily ι) (l : ι) : ℝ≥0∞ :=
  residualWaitE (finitePart σ) c l

@[fun_prop]
theorem measurable_extendedResidualWaitE
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (l : ι) :
    Measurable fun c => extendedResidualWaitE σ c l := by
  exact measurable_residualWaitE
    (measurable_finitePart hσ.measurable) l

/-- The common physical holding time in a fixed positive-rate race. -/
noncomputable def fixedRaceWaitE
    (σ : ExtendedCellLine ι) (rate : ι → ℝ≥0)
    (c : CellFamily ι) : ℝ≥0∞ :=
  ⨅ l, extendedResidualWaitE σ c l / (rate l : ℝ≥0∞)

@[fun_prop]
theorem measurable_fixedRaceWaitE
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (rate : ι → ℝ≥0) :
    Measurable (fixedRaceWaitE σ rate) := by
  exact Measurable.iInf fun l =>
    (measurable_extendedResidualWaitE hσ l).div_const (rate l : ℝ≥0∞)

/-- Advance every internal clock by its rate times the first race wait. -/
noncomputable def fixedNextInternal
    (σ : ExtendedCellLine ι) (rate : ι → ℝ≥0) :
    ExtendedCellLine ι :=
  fun c l => σ c l + (rate l : ℝ≥0∞) * fixedRaceWaitE σ rate c

theorem measurable_fixedNextInternal
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (rate : ι → ℝ≥0) :
    Measurable (fixedNextInternal σ rate) := by
  apply measurable_pi_lambda
  intro l
  exact ((measurable_pi_apply l).comp hσ.measurable).add
    (measurable_const.mul (measurable_fixedRaceWaitE hσ rate))

theorem extendedLine_le_fixedNextInternal
    (σ : ExtendedCellLine ι) (rate : ι → ℝ≥0) :
    ∀ c l, σ c l ≤ fixedNextInternal σ rate c l := by
  intro c l
  exact le_add_of_nonneg_right zero_le

/-- Deterministic threshold identity for the first future cell arrival. -/
theorem residualWaitE_le_coe_iff_shiftedCount_pos
    (σ : CellFamily ι → ι → ℝ≥0)
    (c : CellFamily ι) (l : ι) (q : ℝ≥0) :
    residualWaitE σ c l ≤ (q : ℝ≥0∞) ↔
      0 < shiftedCount σ c l q := by
  let Y : ℝ≥0 → ℕ := fun s => cellPath s (c l)
  let D : ℝ≥0 → ℕ := fun s => shiftedCount σ c l s
  have hmono : Monotone D := by
    intro s t hst
    unfold D shiftedCount
    exact Nat.sub_le_sub_right
      (Ripple.Kurtz.StrongApprox.cellPath_mono
        (by
          have : (s : ℝ) ≤ t := by exact_mod_cast hst
          linarith) (c l)) _
  have hzero : D 0 = 0 := by
    simp [D, shiftedCount]
  have hYright : ∀ s, ∀ᶠ r in 𝓝[≥] s, Y r = Y s := by
    intro s
    have hcont : Tendsto (fun r : ℝ≥0 => (r : ℝ))
        (𝓝[≥] s) (𝓝[≥] (s : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact NNReal.continuous_coe.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact_mod_cast hr
    exact hcont.eventually
      (Ripple.Kurtz.StrongApprox.cellPath_eventually_right (s : ℝ) (c l))
  have hright : ∀ s, ∀ᶠ r in 𝓝[≥] s, D r = D s := by
    intro s
    filter_upwards [rightConst_shift hYright (σ c l) s] with r hr
    simp only [D, shiftedCount, Y, NNReal.coe_add] at hr ⊢
    rw [hr]
  by_cases hnz : ∃ s, 0 < D s
  · have hchar := firstWait_char hmono hzero hright hnz
    have hfirst :
        (residualWaitE σ c l).toReal =
          firstWait (fun s => (D s : ℝ)) := by
      simpa [D] using cell_residualWait_eq_firstWait σ c l
    have hfirstPos : 0 < firstWait (fun s => (D s : ℝ)) := by
      have := (hchar 0).2 hzero
      simpa using this
    have hfinite : residualWaitE σ c l ≠ ∞ := by
      intro htop
      have hz : (residualWaitE σ c l).toReal = 0 := by simp [htop]
      rw [hfirst] at hz
      linarith
    rw [← ENNReal.toReal_le_toReal hfinite ENNReal.coe_ne_top]
    simp only [ENNReal.coe_toReal, hfirst]
    constructor
    · intro hle
      by_contra hnot
      have hDq : D q = 0 := Nat.eq_zero_of_not_pos hnot
      exact (not_lt_of_ge hle) ((hchar q).2 hDq)
    · intro hpos
      exact le_of_not_gt fun hlt => by
        have hz := (hchar q).1 hlt
        have hDq : D q = shiftedCount σ c l q := rfl
        omega
  · push_neg at hnz
    have htop : residualWaitE σ c l = ∞ := by
      unfold residualWaitE
      apply top_unique
      refine le_iInf fun r => ?_
      split_ifs with hr
      · exfalso
        have h2 := hnz (r : ℝ≥0)
        have h3 : D (r : ℝ≥0) = shiftedCount σ c l r := rfl
        have h4 := hr.2
        omega
      · exact le_rfl
    rw [htop]
    simp [D, hnz]

noncomputable def remainingBudgetE
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) (c : CellFamily ι) : ℝ≥0∞ :=
  ⨅ l,
    ((u l : ℝ≥0∞) - (belowValue σ u c l : ℝ≥0∞)) /
      (rate l : ℝ≥0∞)

@[fun_prop]
theorem measurable_remainingBudgetE
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (rate : ι → ℝ≥0) :
    Measurable[cellPast u] (remainingBudgetE σ u rate) := by
  exact Measurable.iInf fun l =>
    (measurable_const.sub
      (measurable_coe_nnreal_ennreal.comp
        (measurable_belowValue hσ u l))).div_const (rate l : ℝ≥0∞)

noncomputable def raceHorizon
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) (c : CellFamily ι) (l : ι) : ℝ≥0 :=
  (remainingBudgetE σ u rate c * (rate l : ℝ≥0∞)).toNNReal

@[fun_prop]
theorem measurable_raceHorizon
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (rate : ι → ℝ≥0) (l : ι) :
    Measurable[cellPast u] (fun c => raceHorizon σ u rate c l) := by
  exact ENNReal.measurable_toNNReal.comp
    ((measurable_remainingBudgetE hσ u rate).mul_const (rate l : ℝ≥0∞))

theorem remainingBudget_ne_top
    {σ : ExtendedCellLine ι} (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) (hpositive : ∀ l, 0 < rate l)
    (c : CellFamily ι) :
    remainingBudgetE σ u rate c ≠ ∞ := by
  let l0 : ι := Classical.choice inferInstance
  have hterm :
      ((u l0 : ℝ≥0∞) - (belowValue σ u c l0 : ℝ≥0∞)) /
          (rate l0 : ℝ≥0∞) ≠ ∞ :=
    ENNReal.div_ne_top (by finiteness)
      (by exact_mod_cast (hpositive l0).ne')
  exact ne_top_of_le_ne_top hterm
    (iInf_le (fun l =>
      ((u l : ℝ≥0∞) - (belowValue σ u c l : ℝ≥0∞)) /
        (rate l : ℝ≥0∞)) l0)

theorem coe_raceHorizon
    {σ : ExtendedCellLine ι} (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) (hpositive : ∀ l, 0 < rate l)
    (c : CellFamily ι) (l : ι) :
    (raceHorizon σ u rate c l : ℝ≥0∞) =
      remainingBudgetE σ u rate c * (rate l : ℝ≥0∞) := by
  exact ENNReal.coe_toNNReal
    (ENNReal.mul_ne_top (remainingBudget_ne_top u rate hpositive c)
      ENNReal.coe_ne_top)

theorem raceEnd_le
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (rate : ι → ℝ≥0)
    (hpositive : ∀ l, 0 < rate l)
    (c : CellFamily ι) (l : ι) :
    belowValue σ u c l + raceHorizon σ u rate c l ≤ u l := by
  have hbudget := iInf_le
    (fun j =>
      ((u j : ℝ≥0∞) - (belowValue σ u c j : ℝ≥0∞)) /
        (rate j : ℝ≥0∞)) l
  have hmul :
      remainingBudgetE σ u rate c * (rate l : ℝ≥0∞) ≤
        (u l : ℝ≥0∞) - (belowValue σ u c l : ℝ≥0∞) := by
    exact (ENNReal.le_div_iff_mul_le
      (.inl (by exact_mod_cast (hpositive l).ne'))
      (.inl ENNReal.coe_ne_top)).1 hbudget
  have hbase :
      (belowValue σ u c l : ℝ≥0∞) ≤ (u l : ℝ≥0∞) := by
    exact_mod_cast belowValue_le hσ u c l
  have hbaseTop : (belowValue σ u c l : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hadd :
      (belowValue σ u c l : ℝ≥0∞) +
          (raceHorizon σ u rate c l : ℝ≥0∞) ≤
        (u l : ℝ≥0∞) := by
    rw [coe_raceHorizon u rate hpositive]
    exact ((ENNReal.cancel_of_ne hbaseTop).le_tsub_iff_left hbase).1 hmul
  exact_mod_cast hadd

noncomputable def raceIncrementAt
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) (l : ι) (c : CellFamily ι) : ℕ :=
  cellPath (belowValue σ u c l + raceHorizon σ u rate c l) (c l) -
    cellPath (belowValue σ u c l) (c l)

@[fun_prop]
theorem measurable_raceIncrementAt
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (rate : ι → ℝ≥0)
    (hpositive : ∀ l, 0 < rate l) (l : ι) :
    Measurable[cellPast u] (raceIncrementAt σ u rate l) := by
  have hstart := measurable_cellPath_boundedRandomTime u l
    (fun c => belowValue σ u c l)
    (measurable_belowValue hσ u l)
    (fun c => belowValue_le hσ u c l)
  have hend := measurable_cellPath_boundedRandomTime u l
    (fun c => belowValue σ u c l + raceHorizon σ u rate c l)
    ((measurable_belowValue hσ u l).add
      (measurable_raceHorizon hσ u rate l))
    (fun c => raceEnd_le hσ u rate hpositive c l)
  exact hend.sub hstart

def fixedRaceHit
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) : Set (CellFamily ι) :=
  ⋃ l, {c | 0 < raceIncrementAt σ u rate l c}

theorem measurable_fixedRaceHit
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (rate : ι → ℝ≥0)
    (hpositive : ∀ l, 0 < rate l) :
    MeasurableSet[cellPast u] (fixedRaceHit σ u rate) := by
  apply MeasurableSet.iUnion
  intro l
  exact measurable_raceIncrementAt hσ u rate hpositive l
    ((Set.to_countable {m : ℕ | 0 < m}).measurableSet)

private theorem add_rate_mul_le_iff
    {s u w : ℝ≥0∞} {r : ℝ≥0}
    (hs : s ≤ u) (hr : 0 < r) (hu : u ≠ ∞) :
    s + (r : ℝ≥0∞) * w ≤ u ↔
      w ≤ (u - s) / (r : ℝ≥0∞) := by
  have hsTop : s ≠ ∞ := ne_top_of_le_ne_top hu hs
  rw [← (ENNReal.cancel_of_ne hsTop).le_tsub_iff_left hs]
  rw [ENNReal.le_div_iff_mul_le
    (.inl (by exact_mod_cast hr.ne')) (.inl ENNReal.coe_ne_top)]
  simp [mul_comm]

private theorem raceIncrement_eq_shiftedCount
    {σ : ExtendedCellLine ι} {u : ι → ℝ≥0}
    {rate : ι → ℝ≥0} {c : CellFamily ι}
    (hc : c ∈ extendedLineBelow σ u) (l : ι) :
    raceIncrementAt σ u rate l c =
      shiftedCount (finitePart σ) c l (raceHorizon σ u rate c l) := by
  unfold raceIncrementAt shiftedCount
  rw [belowValue_eq_of_mem hc]

/-- The decisive event identity: the next line is below `u` exactly when the
old line is below `u` and one channel arrives before the common remaining
budget. -/
theorem fixedNextInternal_below_eq
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (rate : ι → ℝ≥0) (hpositive : ∀ l, 0 < rate l)
    (u : ι → ℝ≥0) :
    extendedLineBelow (fixedNextInternal σ rate) u =
      extendedLineBelow σ u ∩ fixedRaceHit σ u rate := by
  ext c
  constructor
  · intro hnext
    have hbase : c ∈ extendedLineBelow σ u := by
      intro l
      exact (extendedLine_le_fixedNextInternal σ rate c l).trans (hnext l)
    have hwait :
        fixedRaceWaitE σ rate c ≤ remainingBudgetE σ u rate c := by
      apply le_iInf
      intro l
      have hcoord := hnext l
      have hfinite : σ c l ≠ ∞ :=
        ne_top_of_le_ne_top ENNReal.coe_ne_top (hbase l)
      have hlocal := coe_belowValue_eq_of_mem hbase l
      rw [fixedNextInternal] at hcoord
      rw [hlocal]
      exact (add_rate_mul_le_iff (hbase l) (hpositive l)
        ENNReal.coe_ne_top).1 hcoord
    obtain ⟨l, hlEq⟩ := exists_eq_ciInf_of_finite
      (f := fun j => extendedResidualWaitE σ c j / (rate j : ℝ≥0∞))
    have hl : extendedResidualWaitE σ c l / (rate l : ℝ≥0∞) ≤
        remainingBudgetE σ u rate c := hlEq.le.trans hwait
    have hthreshold :
        extendedResidualWaitE σ c l ≤
          (raceHorizon σ u rate c l : ℝ≥0∞) := by
      rw [coe_raceHorizon u rate hpositive]
      have := (ENNReal.div_le_iff
        (by exact_mod_cast (hpositive l).ne') ENNReal.coe_ne_top).1 hl
      simpa [mul_comm] using this
    have hhit : 0 < raceIncrementAt σ u rate l c := by
      rw [raceIncrement_eq_shiftedCount hbase]
      exact (residualWaitE_le_coe_iff_shiftedCount_pos
        (finitePart σ) c l _).1 hthreshold
    refine ⟨hbase, Set.mem_iUnion.mpr ?_⟩
    exact ⟨l, hhit⟩
  · rintro ⟨hbase, hhit⟩
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hhit
    have hthreshold :
        extendedResidualWaitE σ c l ≤
          (raceHorizon σ u rate c l : ℝ≥0∞) := by
      apply (residualWaitE_le_coe_iff_shiftedCount_pos
        (finitePart σ) c l _).2
      rwa [← raceIncrement_eq_shiftedCount hbase]
    have hterm :
        extendedResidualWaitE σ c l / (rate l : ℝ≥0∞) ≤
          remainingBudgetE σ u rate c := by
      rw [coe_raceHorizon u rate hpositive] at hthreshold
      exact (ENNReal.div_le_iff
        (by exact_mod_cast (hpositive l).ne') ENNReal.coe_ne_top).2
        (by simpa [mul_comm] using hthreshold)
    have hwait : fixedRaceWaitE σ rate c ≤
        remainingBudgetE σ u rate c :=
      (iInf_le (fun j =>
        extendedResidualWaitE σ c j / (rate j : ℝ≥0∞)) l).trans hterm
    intro j
    have hbudget := iInf_le
      (fun q =>
        ((u q : ℝ≥0∞) - (belowValue σ u c q : ℝ≥0∞)) /
          (rate q : ℝ≥0∞)) j
    have hlocal := coe_belowValue_eq_of_mem hbase j
    rw [fixedNextInternal]
    apply (add_rate_mul_le_iff (hbase j) (hpositive j)
      ENNReal.coe_ne_top).2
    exact hwait.trans (by simpa [remainingBudgetE, hlocal] using hbudget)

/-- Fixed positive-rate one-step recursion. -/
theorem fixedNextInternal_isExtendedStoppingLine
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (rate : ι → ℝ≥0) (hpositive : ∀ l, 0 < rate l) :
    ExtendedCellStoppingLine (fixedNextInternal σ rate) := by
  refine ⟨measurable_fixedNextInternal hσ rate, ?_⟩
  intro u
  rw [fixedNextInternal_below_eq hσ rate hpositive u]
  exact (hσ.stopping u).inter
    (measurable_fixedRaceHit hσ u rate hpositive)

/-! ## State-dependent positive rates -/

section StateDependent

variable {S : Type*} [Countable S] [MeasurableSpace S]
variable [MeasurableSingletonClass S]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def stateRaceWaitE
    (σ : ExtendedCellLine ι) (state : CellFamily ι → S)
    (rate : S → ι → ℝ≥0) (c : CellFamily ι) : ℝ≥0∞ :=
  ⨅ l, extendedResidualWaitE σ c l /
    (rate (state c) l : ℝ≥0∞)

noncomputable def stateNextInternal
    (σ : ExtendedCellLine ι) (state : CellFamily ι → S)
    (rate : S → ι → ℝ≥0) : ExtendedCellLine ι :=
  fun c l => σ c l +
    (rate (state c) l : ℝ≥0∞) * stateRaceWaitE σ state rate c

theorem measurable_stateNextInternal
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    {state : CellFamily ι → S}
    (hstate : Measurable state)
    {rate : S → ι → ℝ≥0} (hrate : Measurable rate) :
    Measurable (stateNextInternal σ state rate) := by
  have hwait : Measurable (stateRaceWaitE σ state rate) :=
    Measurable.iInf fun l =>
      (measurable_extendedResidualWaitE hσ l).div
        (measurable_coe_nnreal_ennreal.comp
          ((measurable_pi_apply l).comp (hrate.comp hstate)))
  apply measurable_pi_lambda
  intro l
  exact ((measurable_pi_apply l).comp hσ.measurable).add
    ((measurable_coe_nnreal_ennreal.comp
      ((measurable_pi_apply l).comp (hrate.comp hstate))).mul hwait)

theorem extendedLine_le_stateNextInternal
    (σ : ExtendedCellLine ι) (state : CellFamily ι → S)
    (rate : S → ι → ℝ≥0) :
    ∀ c l, σ c l ≤ stateNextInternal σ state rate c l := by
  intro c l
  exact le_add_of_nonneg_right zero_le

theorem stateNextInternal_eq_fixed
    (σ : ExtendedCellLine ι) (state : CellFamily ι → S)
    (rate : S → ι → ℝ≥0) (c : CellFamily ι) :
    stateNextInternal σ state rate c =
      fixedNextInternal σ (rate (state c)) c := by
  rfl

/-- State-dependent one-step recursion, obtained by a countable union over the
stopped-past state fibres. -/
theorem stateNextInternal_isExtendedStoppingLine
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    {state : CellFamily ι → S}
    (hstate : Measurable[extendedStoppedPast σ hσ] state)
    {rate : S → ι → ℝ≥0} (hrate : Measurable rate)
    (hpositive : ∀ x l, 0 < rate x l) :
    ExtendedCellStoppingLine (stateNextInternal σ state rate) := by
  have hstateAmbient : Measurable state :=
    measurable_extendedStoppedPast_ambient hstate
  refine ⟨measurable_stateNextInternal hσ hstateAmbient hrate, ?_⟩
  intro u
  have heq :
      extendedLineBelow (stateNextInternal σ state rate) u =
        ⋃ x : S,
          {c | state c = x} ∩
            extendedLineBelow (fixedNextInternal σ (rate x)) u := by
    ext c
    constructor
    · intro hc
      apply Set.mem_iUnion.mpr
      exact ⟨state c, rfl, hc⟩
    · intro hc
      obtain ⟨x, hx, hline⟩ := Set.mem_iUnion.mp hc
      have hxc : state c = x := hx
      subst hxc
      exact hline
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  let τx := fixedNextInternal σ (rate x)
  let hτx : ExtendedCellStoppingLine τx :=
    fixedNextInternal_isExtendedStoppingLine hσ (rate x) (hpositive x)
  have hfiberσ :
      MeasurableSet[extendedStoppedPast σ hσ] {c | state c = x} :=
    hstate (measurableSet_singleton x)
  have hfiberτ :
      MeasurableSet[extendedStoppedPast τx hτx] {c | state c = x} :=
    (extendedStoppedPast_mono hσ hτx
      (extendedLine_le_fixedNextInternal σ (rate x))) _ hfiberσ
  exact extendedStoppedPast_inter_below hfiberτ u

/-! ## The observable next record -/

noncomputable def firstPositiveChannel
    (z : ι → ℕ) : ι :=
  if h : ∃ l, 0 < z l then Classical.choose h
  else Classical.choice inferInstance

@[fun_prop]
theorem measurable_firstPositiveChannel :
    Measurable (firstPositiveChannel : (ι → ℕ) → ι) := by
  exact measurable_of_countable _

noncomputable def observableWinner
    (σ τ : ExtendedCellLine ι) (c : CellFamily ι) : ι :=
  firstPositiveChannel (fun l => lineIncrement σ τ l c)

@[fun_prop]
theorem measurable_observableWinner
    {σ τ : ExtendedCellLine ι}
    (hσ : ExtendedCellStoppingLine σ)
    (hτ : ExtendedCellStoppingLine τ)
    (hle : ∀ c l, σ c l ≤ τ c l) :
    Measurable[extendedStoppedPast τ hτ]
      (observableWinner σ τ) := by
  refine @Measurable.comp (CellFamily ι) (ι → ℕ) ι (extendedStoppedPast τ hτ) _ _ _ _
    measurable_firstPositiveChannel ?_
  refine @measurable_pi_lambda _ _ _ (extendedStoppedPast τ hτ) _ _ ?_
  intro l
  exact measurable_lineIncrement hσ hτ hle l

noncomputable def observableHoldingTime
    (σ τ : ExtendedCellLine ι)
    (state : CellFamily ι → S) (rate : S → ι → ℝ≥0)
    (c : CellFamily ι) : ℝ :=
  let l0 : ι := Classical.choice inferInstance
  ((τ c l0 - σ c l0) / (rate (state c) l0 : ℝ≥0∞)).toReal

@[fun_prop]
theorem measurable_observableHoldingTime
    {σ τ : ExtendedCellLine ι}
    (hσ : ExtendedCellStoppingLine σ)
    (hτ : ExtendedCellStoppingLine τ)
    (hle : ∀ c l, σ c l ≤ τ c l)
    {state : CellFamily ι → S}
    (hstate : Measurable[extendedStoppedPast σ hσ] state)
    {rate : S → ι → ℝ≥0} (hrate : Measurable rate) :
    Measurable[extendedStoppedPast τ hτ]
      (observableHoldingTime σ τ state rate) := by
  let l0 : ι := Classical.choice inferInstance
  have hσline : Measurable[extendedStoppedPast τ hτ] σ :=
    Measurable.mono (measurable_extendedLine_stoppedPast hσ)
      (extendedStoppedPast_mono hσ hτ hle) le_rfl
  have hstateτ : Measurable[extendedStoppedPast τ hτ] state :=
    Measurable.mono hstate (extendedStoppedPast_mono hσ hτ hle) le_rfl
  have hrateτ : Measurable[extendedStoppedPast τ hτ]
      (fun c => (rate (state c) l0 : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp
      ((measurable_pi_apply l0).comp (hrate.comp hstateτ))
  exact ENNReal.measurable_toReal.comp
    ((((measurable_pi_apply l0).comp
      (measurable_extendedLine_stoppedPast hτ)).sub
        ((measurable_pi_apply l0).comp hσline)).div hrateτ)

noncomputable def nextRecordValue
    (σ τ : ExtendedCellLine ι)
    (state : CellFamily ι → S) (rate : S → ι → ℝ≥0)
    (step : S → ι → S) (c : CellFamily ι) : ℝ × S :=
  (observableHoldingTime σ τ state rate c,
    step (state c) (observableWinner σ τ c))

@[fun_prop]
theorem measurable_nextRecordValue
    {σ τ : ExtendedCellLine ι}
    (hσ : ExtendedCellStoppingLine σ)
    (hτ : ExtendedCellStoppingLine τ)
    (hle : ∀ c l, σ c l ≤ τ c l)
    {state : CellFamily ι → S}
    (hstate : Measurable[extendedStoppedPast σ hσ] state)
    {rate : S → ι → ℝ≥0} (hrate : Measurable rate)
    {step : S → ι → S}
    (hstep : Measurable (Function.uncurry step)) :
    Measurable[extendedStoppedPast τ hτ]
      (nextRecordValue σ τ state rate step) := by
  have hstateτ : Measurable[extendedStoppedPast τ hτ] state :=
    Measurable.mono hstate (extendedStoppedPast_mono hσ hτ hle) le_rfl
  have hwinner := measurable_observableWinner hσ hτ hle
  have hnextState : Measurable[extendedStoppedPast τ hτ]
      (fun c => step (state c) (observableWinner σ τ c)) :=
    hstep.comp (hstateτ.prodMk hwinner)
  exact (measurable_observableHoldingTime hσ hτ hle hstate hrate).prodMk
    hnextState

noncomputable def extendRecord
    (R : CellFamily ι → ℕ → ℝ × S) (k : ℕ)
    (next : CellFamily ι → ℝ × S)
    (c : CellFamily ι) (j : ℕ) : ℝ × S :=
  if j = k + 1 then next c else R c j

/-- The old record prefix together with the observable next record is
measurable in the next stopped past. -/
theorem measurable_nextRecordPrefix
    {R : CellFamily ι → ℕ → ℝ × S} {k : ℕ}
    {σ τ : ExtendedCellLine ι}
    (hσ : ExtendedCellStoppingLine σ)
    (hτ : ExtendedCellStoppingLine τ)
    (hle : ∀ c l, σ c l ≤ τ c l)
    (hOld : Measurable[extendedStoppedPast σ hσ] (recordPrefix R k))
    {next : CellFamily ι → ℝ × S}
    (hnext : Measurable[extendedStoppedPast τ hτ] next) :
    Measurable[extendedStoppedPast τ hτ]
      (recordPrefix (extendRecord R k next) (k + 1)) := by
  have hOldτ : Measurable[extendedStoppedPast τ hτ] (recordPrefix R k) :=
    Measurable.mono hOld (extendedStoppedPast_mono hσ hτ hle) le_rfl
  refine @measurable_pi_lambda _ _ _ (extendedStoppedPast τ hτ) _ _ ?_
  intro j
  by_cases hj : j.val = k + 1
  · have heq : j = ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
      exact Subtype.ext hj
    subst j
    simpa [recordPrefix, extendRecord] using hnext
  · have hjle : j.val ≤ k := by
      have := Finset.mem_Iic.mp j.property
      omega
    let j0 : Finset.Iic k := ⟨j.val, Finset.mem_Iic.mpr hjle⟩
    have heval := (measurable_pi_apply j0).comp hOldτ
    simpa [recordPrefix, extendRecord, j0, hj] using heval

/-! ## Almost-sure finiteness and the complete one-step receipt -/

lemma clockLaw_all_positive_ae :
    ∀ᵐ e ∂clockLaw ι, ∀ l, 0 < e l := by
  apply ae_all_iff.2
  intro l
  haveI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hmap : (clockLaw ι).map (fun e => e l) = expMeasure 1 := by
    simpa [clockLaw] using
      (MeasureTheory.measurePreserving_eval
        (fun _ : ι => expMeasure 1) l).map_eq
  rw [ae_iff]
  have heq : {e : ι → ℝ | ¬ 0 < e l} =
      (fun e : ι → ℝ => e l) ⁻¹' Set.Iic 0 := by
    ext e
    simp
  rw [heq, ← Measure.map_apply (measurable_pi_apply l) measurableSet_Iic,
    hmap, expMeasure_one_Iic_zero]

/-- Fresh real residuals rule out `∞` extended waits almost surely; `∞` would
be sent to the forbidden atom zero by `toReal`. -/
theorem residualWaitE_finite_ae
    {S0 : Type*} [MeasurableSpace S0]
    {R : CellFamily ι → ℕ → ℝ × S0} {k : ℕ}
    {σ : ExtendedCellLine ι}
    (H : FreshResidualsAt (cellFamilyLaw ι) R
      (extendedStoppingResidual σ) k) :
    ∀ᵐ c ∂cellFamilyLaw ι,
      ∀ l, extendedResidualWaitE σ c l ≠ ∞ := by
  have htarget :
      ∀ᵐ e ∂(cellFamilyLaw ι).map (extendedStoppingResidual σ),
        ∀ l, 0 < e l := by
    rw [H.residual_law]
    exact clockLaw_all_positive_ae
  have hsource := MeasureTheory.ae_of_ae_map
    H.measurable_residual.aemeasurable htarget
  filter_upwards [hsource] with c hc
  intro l htop
  have h' : residualWaitE (finitePart σ) c l = ∞ := htop
  have hz : extendedStoppingResidual σ c l = 0 := by
    simp [extendedStoppingResidual, residualVector,
      CellRandomTimeEvaluation.residualWait, h']
  have hcl := hc l
  rw [hz] at hcl
  exact (lt_irrefl 0) hcl

/-- Finiteness propagates through one positive-rate race. -/
theorem stateNextInternal_finite_ae
    {σ : ExtendedCellLine ι}
    (state : CellFamily ι → S) (rate : S → ι → ℝ≥0)
    (hpositive : ∀ x l, 0 < rate x l)
    (hline : ∀ᵐ c ∂cellFamilyLaw ι, c ∈ extendedLineFinite σ)
    (hresidual : ∀ᵐ c ∂cellFamilyLaw ι,
      ∀ l, extendedResidualWaitE σ c l ≠ ∞) :
    ∀ᵐ c ∂cellFamilyLaw ι,
      c ∈ extendedLineFinite (stateNextInternal σ state rate) := by
  filter_upwards [hline, hresidual] with c hc hres
  have hwait : stateRaceWaitE σ state rate c ≠ ∞ := by
    let l0 : ι := Classical.choice inferInstance
    have hterm :
        extendedResidualWaitE σ c l0 /
            (rate (state c) l0 : ℝ≥0∞) ≠ ∞ :=
      ENNReal.div_ne_top (hres l0)
        (by exact_mod_cast (hpositive (state c) l0).ne')
    exact ne_top_of_le_ne_top hterm
      (iInf_le (fun l => extendedResidualWaitE σ c l /
        (rate (state c) l : ℝ≥0∞)) l0)
  intro l
  apply ENNReal.add_ne_top.2
  refine ⟨hc l, ?_⟩
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top hwait

/-- Complete index-successor step.  It starts only with the current extended
stopping line and measurable record prefix, constructs the next line and next
record, proves their stopped-past properties, and re-establishes freshness. -/
theorem oneStepExtendedRecordRecursion
    {R : CellFamily ι → ℕ → ℝ × S} {k : ℕ}
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (hHistory :
      Measurable[extendedStoppedPast σ hσ] (recordPrefix R k))
    (hfinite : ∀ᵐ c ∂cellFamilyLaw ι, c ∈ extendedLineFinite σ)
    (base : ℕ → ℝ × S)
    {rate : S → ι → ℝ≥0} (hrate : Measurable rate)
    (hpositive : ∀ x l, 0 < rate x l)
    {step : S → ι → S}
    (hstep : Measurable (Function.uncurry step)) :
    let state : CellFamily ι → S := fun c => (R c k).2
    let τ := stateNextInternal σ state rate
    let next := nextRecordValue σ τ state rate step
    let Rnext := extendRecord R k next
    ∃ hτ : ExtendedCellStoppingLine τ,
      Measurable[extendedStoppedPast τ hτ]
          (recordPrefix Rnext (k + 1)) ∧
        (∀ᵐ c ∂cellFamilyLaw ι, c ∈ extendedLineFinite τ) ∧
        FreshResidualsAt (cellFamilyLaw ι) Rnext
          (extendedStoppingResidual τ) (k + 1) := by
  dsimp only
  let state : CellFamily ι → S := fun c => (R c k).2
  have hstate : Measurable[extendedStoppedPast σ hσ] state := by
    have heval := (measurable_pi_apply
      (⟨k, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).comp hHistory
    simpa [state, recordPrefix] using measurable_snd.comp heval
  let τ := stateNextInternal σ state rate
  let hτ : ExtendedCellStoppingLine τ :=
    stateNextInternal_isExtendedStoppingLine hσ hstate hrate hpositive
  have hle : ∀ c l, σ c l ≤ τ c l :=
    extendedLine_le_stateNextInternal σ state rate
  let next := nextRecordValue σ τ state rate step
  have hnext : Measurable[extendedStoppedPast τ hτ] next :=
    measurable_nextRecordValue hσ hτ hle hstate hrate hstep
  let Rnext := extendRecord R k next
  have hnextHistory : Measurable[extendedStoppedPast τ hτ]
      (recordPrefix Rnext (k + 1)) :=
    measurable_nextRecordPrefix hσ hτ hle hHistory hnext
  have hcurrentFresh : FreshResidualsAt (cellFamilyLaw ι) R
      (extendedStoppingResidual σ) k :=
    extendedCellStoppingLine_freshResidualsAt
      hσ hHistory hfinite base
  have hresidual := residualWaitE_finite_ae hcurrentFresh
  have hnextFinite : ∀ᵐ c ∂cellFamilyLaw ι,
      c ∈ extendedLineFinite τ :=
    stateNextInternal_finite_ae state rate hpositive hfinite hresidual
  have hnextFresh : FreshResidualsAt (cellFamilyLaw ι) Rnext
      (extendedStoppingResidual τ) (k + 1) :=
    extendedCellStoppingLine_freshResidualsAt
      hτ hnextHistory hnextFinite base
  exact ⟨hτ, hnextHistory, hnextFinite, hnextFresh⟩

end StateDependent

end Ripple.Kurtz.StrongApprox.CellExtendedRaceRecursion

end

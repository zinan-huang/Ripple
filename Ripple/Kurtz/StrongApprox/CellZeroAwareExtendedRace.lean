-- Ripple/Kurtz/StrongApprox/CellZeroAwareExtendedRace.lean
import Ripple.Kurtz.StrongApprox.CellActiveRaceRecordKernel

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellZeroAwareExtendedRace

open MeasureTheory ProbabilityTheory Set Filter Topology Preorder
open scoped ENNReal NNReal BigOperators Classical
open ExponentialRace
open CellRandomTimeEvaluation CellStoppingLineFreshness
open CellExtendedStoppingLine CellExtendedRandomTime
open CellExtendedRaceRecursion

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- At least one channel has positive rate. -/
def HasActiveRate (rate : ι → ℝ≥0) : Prop :=
  ∃ l, 0 < rate l

/-- A zero rate is masked by `∞`, so it cannot win even on exceptional cell
paths whose encoded residual is zero. -/
noncomputable def activeRaceTermE
    (σ : ExtendedCellLine ι) (rate : ι → ℝ≥0)
    (c : CellFamily ι) (l : ι) : ℝ≥0∞ :=
  if 0 < rate l then
    extendedResidualWaitE σ c l / (rate l : ℝ≥0∞)
  else ∞

/-- Physical wait of the positive-rate sub-race.  The absorbing case is
explicitly zero, matching the canonical record marker. -/
noncomputable def activeRaceWaitE
    (σ : ExtendedCellLine ι) (rate : ι → ℝ≥0)
    (c : CellFamily ι) : ℝ≥0∞ :=
  if HasActiveRate rate then ⨅ l, activeRaceTermE σ rate c l else 0

@[fun_prop]
theorem measurable_activeRaceWaitE
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (rate : ι → ℝ≥0) :
    Measurable (activeRaceWaitE σ rate) := by
  classical
  by_cases hactive : HasActiveRate rate
  · have hfun : activeRaceWaitE σ rate =
        fun c => ⨅ l, activeRaceTermE σ rate c l := by
      funext c
      simp only [activeRaceWaitE, if_pos hactive]
    rw [hfun]
    apply Measurable.iInf
    intro l
    by_cases hl : 0 < rate l
    · simp only [activeRaceTermE, if_pos hl]
      exact (measurable_extendedResidualWaitE hσ l).div_const _
    · simp [activeRaceTermE, hl]
  · have hfun : activeRaceWaitE σ rate = fun _ => 0 := by
      funext c
      simp [activeRaceWaitE, hactive]
    rw [hfun]
    exact measurable_const

/-- Only positive-rate internal coordinates advance. -/
noncomputable def activeNextInternal
    (σ : ExtendedCellLine ι) (rate : ι → ℝ≥0) :
    ExtendedCellLine ι :=
  fun c l => σ c l +
    (rate l : ℝ≥0∞) * activeRaceWaitE σ rate c

theorem measurable_activeNextInternal
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (rate : ι → ℝ≥0) :
    Measurable (activeNextInternal σ rate) := by
  apply measurable_pi_lambda
  intro l
  exact ((measurable_pi_apply l).comp hσ.measurable).add
    (measurable_const.mul (measurable_activeRaceWaitE hσ rate))

theorem extendedLine_le_activeNextInternal
    (σ : ExtendedCellLine ι) (rate : ι → ℝ≥0) :
    ∀ c l, σ c l ≤ activeNextInternal σ rate c l := by
  intro c l
  exact le_add_of_nonneg_right zero_le

theorem activeNextInternal_eq_self_of_no_active
    (σ : ExtendedCellLine ι) (rate : ι → ℝ≥0)
    (hactive : ¬ HasActiveRate rate) :
    activeNextInternal σ rate = σ := by
  classical
  have hz : ∀ l, rate l = 0 := by
    intro l
    exact le_antisymm (not_lt.mp (fun hl => hactive ⟨l, hl⟩)) zero_le
  funext c l
  simp [activeNextInternal, activeRaceWaitE, hactive, hz]

/-! ### The rectangular stopping event -/

noncomputable def activeRemainingTermE
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) (c : CellFamily ι) (l : ι) : ℝ≥0∞ :=
  if 0 < rate l then
    ((u l : ℝ≥0∞) - (belowValue σ u c l : ℝ≥0∞)) /
      (rate l : ℝ≥0∞)
  else ∞

noncomputable def activeRemainingBudgetE
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) (c : CellFamily ι) : ℝ≥0∞ :=
  ⨅ l, activeRemainingTermE σ u rate c l

@[fun_prop]
theorem measurable_activeRemainingBudgetE
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (rate : ι → ℝ≥0) :
    Measurable[cellPast u] (activeRemainingBudgetE σ u rate) := by
  classical
  apply Measurable.iInf
  intro l
  by_cases hl : 0 < rate l
  · simp only [activeRemainingTermE, if_pos hl]
    exact (measurable_const.sub
      (measurable_coe_nnreal_ennreal.comp
        (measurable_belowValue hσ u l))).div_const _
  · simp [activeRemainingTermE, hl]

noncomputable def activeRaceHorizon
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) (c : CellFamily ι) (l : ι) : ℝ≥0 :=
  (activeRemainingBudgetE σ u rate c *
    (rate l : ℝ≥0∞)).toNNReal

@[fun_prop]
theorem measurable_activeRaceHorizon
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (rate : ι → ℝ≥0) (l : ι) :
    Measurable[cellPast u]
      (fun c => activeRaceHorizon σ u rate c l) := by
  exact ENNReal.measurable_toNNReal.comp
    ((measurable_activeRemainingBudgetE hσ u rate).mul_const _)

theorem activeRemainingBudget_ne_top
    {σ : ExtendedCellLine ι} (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) (hactive : HasActiveRate rate)
    (c : CellFamily ι) :
    activeRemainingBudgetE σ u rate c ≠ ∞ := by
  obtain ⟨pivot, hpivot⟩ := hactive
  have hterm :
      activeRemainingTermE σ u rate c pivot ≠ ∞ := by
    simp only [activeRemainingTermE, if_pos hpivot]
    exact ENNReal.div_ne_top (by finiteness)
      (by exact_mod_cast hpivot.ne')
  exact ne_top_of_le_ne_top hterm
    (iInf_le (activeRemainingTermE σ u rate c) pivot)

theorem coe_activeRaceHorizon
    {σ : ExtendedCellLine ι} (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) (hactive : HasActiveRate rate)
    (c : CellFamily ι) (l : ι) :
    (activeRaceHorizon σ u rate c l : ℝ≥0∞) =
      activeRemainingBudgetE σ u rate c *
        (rate l : ℝ≥0∞) := by
  exact ENNReal.coe_toNNReal
    (ENNReal.mul_ne_top
      (activeRemainingBudget_ne_top u rate hactive c)
      ENNReal.coe_ne_top)

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

theorem activeRaceEnd_le
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (rate : ι → ℝ≥0)
    (hactive : HasActiveRate rate)
    (c : CellFamily ι) (l : ι) :
    belowValue σ u c l + activeRaceHorizon σ u rate c l ≤ u l := by
  classical
  by_cases hl : 0 < rate l
  · have hbudget :=
      iInf_le (activeRemainingTermE σ u rate c) l
    simp only [activeRemainingTermE, if_pos hl] at hbudget
    have hmul :
        activeRemainingBudgetE σ u rate c *
            (rate l : ℝ≥0∞) ≤
          (u l : ℝ≥0∞) - (belowValue σ u c l : ℝ≥0∞) := by
      exact (ENNReal.le_div_iff_mul_le
        (.inl (by exact_mod_cast hl.ne'))
        (.inl ENNReal.coe_ne_top)).1 hbudget
    have hbase :
        (belowValue σ u c l : ℝ≥0∞) ≤ (u l : ℝ≥0∞) := by
      exact_mod_cast belowValue_le hσ u c l
    have hadd :
        (belowValue σ u c l : ℝ≥0∞) +
            (activeRaceHorizon σ u rate c l : ℝ≥0∞) ≤
          (u l : ℝ≥0∞) := by
      rw [coe_activeRaceHorizon u rate hactive]
      exact ((ENNReal.cancel_of_ne ENNReal.coe_ne_top).le_tsub_iff_left
        hbase).1 hmul
    exact_mod_cast hadd
  · have hz : rate l = 0 :=
      le_antisymm (not_lt.mp hl) zero_le
    simpa [activeRaceHorizon, hz] using belowValue_le hσ u c l

noncomputable def activeRaceIncrementAt
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) (l : ι) (c : CellFamily ι) : ℕ :=
  cellPath
      (belowValue σ u c l + activeRaceHorizon σ u rate c l) (c l) -
    cellPath (belowValue σ u c l) (c l)

@[fun_prop]
theorem measurable_activeRaceIncrementAt
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (rate : ι → ℝ≥0)
    (hactive : HasActiveRate rate) (l : ι) :
    Measurable[cellPast u] (activeRaceIncrementAt σ u rate l) := by
  have hstart := measurable_cellPath_boundedRandomTime u l
    (fun c => belowValue σ u c l)
    (measurable_belowValue hσ u l)
    (fun c => belowValue_le hσ u c l)
  have hend := measurable_cellPath_boundedRandomTime u l
    (fun c => belowValue σ u c l + activeRaceHorizon σ u rate c l)
    ((measurable_belowValue hσ u l).add
      (measurable_activeRaceHorizon hσ u rate l))
    (fun c => activeRaceEnd_le hσ u rate hactive c l)
  exact hend.sub hstart

abbrev ActiveChannel (rate : ι → ℝ≥0) :=
  {l : ι // 0 < rate l}

def activeRaceHit
    (σ : ExtendedCellLine ι) (u : ι → ℝ≥0)
    (rate : ι → ℝ≥0) : Set (CellFamily ι) :=
  ⋃ l : ActiveChannel rate,
    {c | 0 < activeRaceIncrementAt σ u rate l.1 c}

theorem measurable_activeRaceHit
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (u : ι → ℝ≥0) (rate : ι → ℝ≥0)
    (hactive : HasActiveRate rate) :
    MeasurableSet[cellPast u] (activeRaceHit σ u rate) := by
  apply MeasurableSet.iUnion
  intro l
  exact measurable_activeRaceIncrementAt hσ u rate hactive l.1
    ((Set.to_countable {m : ℕ | 0 < m}).measurableSet)

private theorem activeIncrement_eq_shiftedCount
    {σ : ExtendedCellLine ι} {u : ι → ℝ≥0}
    {rate : ι → ℝ≥0} {c : CellFamily ι}
    (hc : c ∈ extendedLineBelow σ u) (l : ι) :
    activeRaceIncrementAt σ u rate l c =
      shiftedCount (finitePart σ) c l
        (activeRaceHorizon σ u rate c l) := by
  unfold activeRaceIncrementAt shiftedCount
  rw [belowValue_eq_of_mem hc]

/-- Fixed zero-aware successor stopping event. -/
theorem activeNextInternal_below_eq
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (rate : ι → ℝ≥0) (hactive : HasActiveRate rate)
    (u : ι → ℝ≥0) :
    extendedLineBelow (activeNextInternal σ rate) u =
      extendedLineBelow σ u ∩ activeRaceHit σ u rate := by
  classical
  ext c
  constructor
  · intro hnext
    have hbase : c ∈ extendedLineBelow σ u := by
      intro l
      exact (extendedLine_le_activeNextInternal σ rate c l).trans
        (hnext l)
    have hW : (⨅ l, activeRaceTermE σ rate c l) =
        activeRaceWaitE σ rate c := by
      rw [activeRaceWaitE, if_pos hactive]
    have hwait :
        activeRaceWaitE σ rate c ≤
          activeRemainingBudgetE σ u rate c := by
      rw [activeRaceWaitE, if_pos hactive]
      apply le_iInf
      intro l
      by_cases hl : 0 < rate l
      · have hcoord := hnext l
        rw [activeNextInternal] at hcoord
        have hbound :=
          (add_rate_mul_le_iff (hbase l) hl ENNReal.coe_ne_top).1 hcoord
        have hlocal := coe_belowValue_eq_of_mem hbase l
        simpa [activeRemainingTermE, hl, hlocal, hW] using hbound
      · simp [activeRemainingTermE, hl]
    have hwaitFinite : activeRaceWaitE σ rate c ≠ ∞ :=
      ne_top_of_le_ne_top
        (activeRemainingBudget_ne_top u rate hactive c) hwait
    obtain ⟨winner, hwinner⟩ := exists_eq_ciInf_of_finite
      (f := fun l => activeRaceTermE σ rate c l)
    have hwinnerPos : 0 < rate winner := by
      by_contra hnot
      have hterm : activeRaceTermE σ rate c winner = ∞ := by
        simp [activeRaceTermE, hnot]
      have htop : activeRaceWaitE σ rate c = ∞ := by
        rw [activeRaceWaitE, if_pos hactive]
        exact hwinner.symm.trans hterm
      exact hwaitFinite htop
    have hterm :
        extendedResidualWaitE σ c winner /
            (rate winner : ℝ≥0∞) ≤
          activeRemainingBudgetE σ u rate c := by
      have := hwinner.le.trans (hW.le.trans hwait)
      simpa [activeRaceTermE, hwinnerPos,
        activeRaceWaitE, hactive] using this
    have hthreshold :
        extendedResidualWaitE σ c winner ≤
          (activeRaceHorizon σ u rate c winner : ℝ≥0∞) := by
      rw [coe_activeRaceHorizon u rate hactive]
      have hm := (ENNReal.div_le_iff
        (by exact_mod_cast hwinnerPos.ne') ENNReal.coe_ne_top).1 hterm
      simpa [mul_comm] using hm
    have hhit :
        0 < activeRaceIncrementAt σ u rate winner c := by
      rw [activeIncrement_eq_shiftedCount hbase]
      exact (residualWaitE_le_coe_iff_shiftedCount_pos
        (finitePart σ) c winner _).1 hthreshold
    refine ⟨hbase, Set.mem_iUnion.mpr ?_⟩
    exact ⟨⟨winner, hwinnerPos⟩, hhit⟩
  · rintro ⟨hbase, hhit⟩
    obtain ⟨winner, hwinnerHit⟩ := Set.mem_iUnion.mp hhit
    have hthreshold :
        extendedResidualWaitE σ c winner.1 ≤
          (activeRaceHorizon σ u rate c winner.1 : ℝ≥0∞) := by
      apply (residualWaitE_le_coe_iff_shiftedCount_pos
        (finitePart σ) c winner.1 _).2
      rwa [← activeIncrement_eq_shiftedCount hbase]
    have hterm :
        extendedResidualWaitE σ c winner.1 /
            (rate winner.1 : ℝ≥0∞) ≤
          activeRemainingBudgetE σ u rate c := by
      rw [coe_activeRaceHorizon u rate hactive] at hthreshold
      exact (ENNReal.div_le_iff
        (by exact_mod_cast winner.2.ne') ENNReal.coe_ne_top).2
        (by simpa [mul_comm] using hthreshold)
    have hwait :
        activeRaceWaitE σ rate c ≤
          activeRemainingBudgetE σ u rate c := by
      rw [activeRaceWaitE, if_pos hactive]
      exact (iInf_le
        (fun l => activeRaceTermE σ rate c l) winner.1).trans
          (by simpa [activeRaceTermE, winner.2] using hterm)
    intro l
    by_cases hl : 0 < rate l
    · have hbudget :=
        iInf_le (activeRemainingTermE σ u rate c) l
      simp only [activeRemainingTermE, if_pos hl] at hbudget
      rw [activeNextInternal]
      apply (add_rate_mul_le_iff (hbase l) hl ENNReal.coe_ne_top).2
      exact hwait.trans
        (by
          have hlocal := coe_belowValue_eq_of_mem hbase l
          simpa [activeRemainingBudgetE, hlocal] using hbudget)
    · have hz : rate l = 0 := le_antisymm (not_lt.mp hl) zero_le
      simpa [activeNextInternal, hz] using hbase l

/-- Zero-aware fixed-rate stopping-line successor. -/
theorem activeNextInternal_isExtendedStoppingLine
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (rate : ι → ℝ≥0) :
    ExtendedCellStoppingLine (activeNextInternal σ rate) := by
  classical
  refine ⟨measurable_activeNextInternal hσ rate, ?_⟩
  intro u
  by_cases hactive : HasActiveRate rate
  · rw [activeNextInternal_below_eq hσ rate hactive u]
    exact (hσ.stopping u).inter
      (measurable_activeRaceHit hσ u rate hactive)
  · rw [activeNextInternal_eq_self_of_no_active σ rate hactive]
    exact hσ.stopping u

/-! ## State-dependent zero-aware rates -/

section StateDependent

variable {S : Type*} [Countable S] [MeasurableSpace S]
variable [MeasurableSingletonClass S]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def stateActiveRaceWaitE
    (σ : ExtendedCellLine ι) (state : CellFamily ι → S)
    (rate : S → ι → ℝ≥0) (c : CellFamily ι) : ℝ≥0∞ :=
  if HasActiveRate (rate (state c)) then
    ⨅ l, activeRaceTermE σ (rate (state c)) c l
  else 0

noncomputable def stateActiveNextInternal
    (σ : ExtendedCellLine ι) (state : CellFamily ι → S)
    (rate : S → ι → ℝ≥0) : ExtendedCellLine ι :=
  fun c l => σ c l +
    (rate (state c) l : ℝ≥0∞) *
      stateActiveRaceWaitE σ state rate c

theorem stateActiveNextInternal_eq_fixed
    (σ : ExtendedCellLine ι) (state : CellFamily ι → S)
    (rate : S → ι → ℝ≥0) (c : CellFamily ι) :
    stateActiveNextInternal σ state rate c =
      activeNextInternal σ (rate (state c)) c := by
  rfl

@[fun_prop]
theorem measurable_stateActiveRaceWaitE
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    {state : CellFamily ι → S} (hstate : Measurable state)
    {rate : S → ι → ℝ≥0} (hrate : Measurable rate) :
    Measurable (stateActiveRaceWaitE σ state rate) := by
  classical
  have hactive : MeasurableSet
      {c | HasActiveRate (rate (state c))} :=
    hstate ((Set.to_countable
      {x : S | HasActiveRate (rate x)}).measurableSet)
  have hbody : Measurable
      (fun c => ⨅ l, activeRaceTermE σ (rate (state c)) c l) := by
    apply Measurable.iInf
    intro l
    have hcoord : Measurable (fun c => rate (state c) l) :=
      (measurable_pi_apply l).comp (hrate.comp hstate)
    have hpos : MeasurableSet {c | 0 < rate (state c) l} :=
      measurableSet_lt measurable_const hcoord
    exact Measurable.ite hpos
      ((measurable_extendedResidualWaitE hσ l).div
        (measurable_coe_nnreal_ennreal.comp hcoord))
      measurable_const
  exact Measurable.ite hactive hbody measurable_const

theorem measurable_stateActiveNextInternal
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    {state : CellFamily ι → S} (hstate : Measurable state)
    {rate : S → ι → ℝ≥0} (hrate : Measurable rate) :
    Measurable (stateActiveNextInternal σ state rate) := by
  have hwait := measurable_stateActiveRaceWaitE hσ hstate hrate
  apply measurable_pi_lambda
  intro l
  exact ((measurable_pi_apply l).comp hσ.measurable).add
    ((measurable_coe_nnreal_ennreal.comp
      ((measurable_pi_apply l).comp (hrate.comp hstate))).mul hwait)

theorem extendedLine_le_stateActiveNextInternal
    (σ : ExtendedCellLine ι) (state : CellFamily ι → S)
    (rate : S → ι → ℝ≥0) :
    ∀ c l, σ c l ≤ stateActiveNextInternal σ state rate c l := by
  intro c l
  exact le_add_of_nonneg_right zero_le

/-- State-dependent zero-aware successor, by countable stopped-past fibres. -/
theorem stateActiveNextInternal_isExtendedStoppingLine
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    {state : CellFamily ι → S}
    (hstate : Measurable[extendedStoppedPast σ hσ] state)
    {rate : S → ι → ℝ≥0} (hrate : Measurable rate) :
    ExtendedCellStoppingLine
      (stateActiveNextInternal σ state rate) := by
  have hstateAmbient : Measurable state :=
    measurable_extendedStoppedPast_ambient hstate
  refine ⟨measurable_stateActiveNextInternal
      hσ hstateAmbient hrate, ?_⟩
  intro u
  have heq :
      extendedLineBelow (stateActiveNextInternal σ state rate) u =
        ⋃ x : S,
          {c | state c = x} ∩
            extendedLineBelow (activeNextInternal σ (rate x)) u := by
    ext c
    constructor
    · intro hc
      exact Set.mem_iUnion.mpr ⟨state c, rfl, hc⟩
    · intro hc
      obtain ⟨x, hx, hline⟩ := Set.mem_iUnion.mp hc
      have hxc : state c = x := hx
      subst x
      exact hline
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  let τx := activeNextInternal σ (rate x)
  let hτx : ExtendedCellStoppingLine τx :=
    activeNextInternal_isExtendedStoppingLine hσ (rate x)
  have hfiberσ :
      MeasurableSet[extendedStoppedPast σ hσ] {c | state c = x} :=
    hstate (measurableSet_singleton x)
  have hfiberτ :
      MeasurableSet[extendedStoppedPast τx hτx] {c | state c = x} :=
    (extendedStoppedPast_mono hσ hτx
      (extendedLine_le_activeNextInternal σ (rate x))) _ hfiberσ
  exact extendedStoppedPast_inter_below hfiberτ u

/-- The chosen record holding time is read from the winning advanced
coordinate.  The finite sum avoids a separate measurable random-index lemma. -/
noncomputable def observableActiveHoldingTime
    (σ τ : ExtendedCellLine ι)
    (state : CellFamily ι → S) (rate : S → ι → ℝ≥0)
    (c : CellFamily ι) : ℝ :=
  ∑ l, if HasActiveRate (rate (state c)) ∧
      observableWinner σ τ c = l then
    ((τ c l - σ c l) /
      (rate (state c) l : ℝ≥0∞)).toReal
  else 0

@[fun_prop]
theorem measurable_observableActiveHoldingTime
    {σ τ : ExtendedCellLine ι}
    (hσ : ExtendedCellStoppingLine σ)
    (hτ : ExtendedCellStoppingLine τ)
    (hle : ∀ c l, σ c l ≤ τ c l)
    {state : CellFamily ι → S}
    (hstate : Measurable[extendedStoppedPast σ hσ] state)
    {rate : S → ι → ℝ≥0} (hrate : Measurable rate) :
    Measurable[extendedStoppedPast τ hτ]
      (observableActiveHoldingTime σ τ state rate) := by
  classical
  have hσline : Measurable[extendedStoppedPast τ hτ] σ :=
    Measurable.mono (measurable_extendedLine_stoppedPast hσ)
      (extendedStoppedPast_mono hσ hτ hle) le_rfl
  have hstateτ : Measurable[extendedStoppedPast τ hτ] state :=
    Measurable.mono hstate
      (extendedStoppedPast_mono hσ hτ hle) le_rfl
  have hactive : MeasurableSet[extendedStoppedPast τ hτ]
      {c | HasActiveRate (rate (state c))} :=
    hstateτ ((Set.to_countable
      {x : S | HasActiveRate (rate x)}).measurableSet)
  have hwinner := measurable_observableWinner hσ hτ hle
  apply Finset.measurable_sum
  intro l _
  have hwin : MeasurableSet[extendedStoppedPast τ hτ]
      {c | observableWinner σ τ c = l} :=
    hwinner (measurableSet_singleton l)
  have hrateτ : Measurable[extendedStoppedPast τ hτ]
      (fun c => (rate (state c) l : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp
      ((measurable_pi_apply l).comp (hrate.comp hstateτ))
  have hquot : Measurable[extendedStoppedPast τ hτ]
      (fun c => ((τ c l - σ c l) /
        (rate (state c) l : ℝ≥0∞)).toReal) :=
    ENNReal.measurable_toReal.comp
      ((((measurable_pi_apply l).comp
        (measurable_extendedLine_stoppedPast hτ)).sub
          ((measurable_pi_apply l).comp hσline)).div hrateτ)
  exact Measurable.ite (hactive.inter hwin) hquot measurable_const

theorem observableActiveHoldingTime_eq_of_active
    (σ τ : ExtendedCellLine ι)
    (state : CellFamily ι → S) (rate : S → ι → ℝ≥0)
    (c : CellFamily ι)
    (hactive : HasActiveRate (rate (state c))) :
    observableActiveHoldingTime σ τ state rate c =
      ((τ c (observableWinner σ τ c) -
          σ c (observableWinner σ τ c)) /
        (rate (state c) (observableWinner σ τ c) : ℝ≥0∞)).toReal := by
  classical
  unfold observableActiveHoldingTime
  rw [Finset.sum_eq_single (observableWinner σ τ c)]
  · simp [hactive]
  · intro l _ hne
    simp [Ne.symm hne]
  · simp

noncomputable def activeNextRecordValue
    (σ τ : ExtendedCellLine ι)
    (state : CellFamily ι → S) (rate : S → ι → ℝ≥0)
    (step : S → ι → S) (c : CellFamily ι) : ℝ × S :=
  if HasActiveRate (rate (state c)) then
    (observableActiveHoldingTime σ τ state rate c,
      step (state c) (observableWinner σ τ c))
  else (0, state c)

@[fun_prop]
theorem measurable_activeNextRecordValue
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
      (activeNextRecordValue σ τ state rate step) := by
  have hstateτ : Measurable[extendedStoppedPast τ hτ] state :=
    Measurable.mono hstate
      (extendedStoppedPast_mono hσ hτ hle) le_rfl
  have hactive : MeasurableSet[extendedStoppedPast τ hτ]
      {c | HasActiveRate (rate (state c))} :=
    hstateτ ((Set.to_countable
      {x : S | HasActiveRate (rate x)}).measurableSet)
  have hwinner := measurable_observableWinner hσ hτ hle
  have hnextState : Measurable[extendedStoppedPast τ hτ]
      (fun c => step (state c) (observableWinner σ τ c)) :=
    hstep.comp (hstateτ.prodMk hwinner)
  exact Measurable.ite hactive
    ((measurable_observableActiveHoldingTime
      hσ hτ hle hstate hrate).prodMk hnextState)
    (measurable_const.prodMk hstateτ)

/-- Finiteness propagation.  A positive coordinate supplies a finite upper
bound for the race minimum; a zero coordinate contributes the finite product
`0`. -/
theorem stateActiveNextInternal_finite_ae
    {σ : ExtendedCellLine ι}
    (state : CellFamily ι → S) (rate : S → ι → ℝ≥0)
    (hline : ∀ᵐ c ∂cellFamilyLaw ι,
      c ∈ extendedLineFinite σ)
    (hresidual : ∀ᵐ c ∂cellFamilyLaw ι,
      ∀ l, extendedResidualWaitE σ c l ≠ ∞) :
    ∀ᵐ c ∂cellFamilyLaw ι,
      c ∈ extendedLineFinite
        (stateActiveNextInternal σ state rate) := by
  filter_upwards [hline, hresidual] with c hc hres
  intro l
  apply ENNReal.add_ne_top.2
  refine ⟨hc l, ?_⟩
  by_cases hl : 0 < rate (state c) l
  · have hterm :
        activeRaceTermE σ (rate (state c)) c l ≠ ∞ := by
      simp only [activeRaceTermE, if_pos hl]
      exact ENNReal.div_ne_top (hres l)
        (by exact_mod_cast hl.ne')
    have hactive : HasActiveRate (rate (state c)) := ⟨l, hl⟩
    have hwait : stateActiveRaceWaitE σ state rate c ≠ ∞ := by
      rw [stateActiveRaceWaitE, if_pos hactive]
      exact ne_top_of_le_ne_top hterm
        (iInf_le (activeRaceTermE σ (rate (state c)) c) l)
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hwait
  · have hz : rate (state c) l = 0 :=
      le_antisymm (not_lt.mp hl) zero_le
    simp [hz]

/-- Positivity of a line increment is the threshold event for the old residual. -/
theorem activeLineIncrement_pos_iff
    {σ : ExtendedCellLine ι} {rate : ι → ℝ≥0}
    {c : CellFamily ι} {l : ι}
    (hline : σ c l ≠ ∞)
    (hwait : activeRaceWaitE σ rate c ≠ ∞)
    (hl : 0 < rate l) :
    0 < lineIncrement σ (activeNextInternal σ rate) l c ↔
      extendedResidualWaitE σ c l ≤
        (rate l : ℝ≥0∞) * activeRaceWaitE σ rate c := by
  let delta : ℝ≥0∞ :=
    (rate l : ℝ≥0∞) * activeRaceWaitE σ rate c
  have hdelta : delta ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hwait
  have hfinitePart :
      finitePart (activeNextInternal σ rate) c l =
        finitePart σ c l + delta.toNNReal := by
    change (σ c l + delta).toNNReal =
      (σ c l).toNNReal + delta.toNNReal
    exact ENNReal.toNNReal_add hline hdelta
  have hincrement :
      lineIncrement σ (activeNextInternal σ rate) l c =
        shiftedCount (finitePart σ) c l delta.toNNReal := by
    unfold lineIncrement extendedPathAt shiftedCount
    rw [hfinitePart]
    rfl
  rw [hincrement]
  have hcoe : (delta.toNNReal : ℝ≥0∞) = delta :=
    ENNReal.coe_toNNReal hdelta
  have hiff := (residualWaitE_le_coe_iff_shiftedCount_pos
    (finitePart σ) c l delta.toNNReal).symm
  rw [hcoe] at hiff
  exact hiff

/-- Complete zero-aware index successor.  The returned freshness is for the
whole fixed channel vector, which is the invariant needed for iteration. -/
theorem oneStepActiveRecordRecursion
    {R : CellFamily ι → ℕ → ℝ × S} {k : ℕ}
    {σ : ExtendedCellLine ι} (hσ : ExtendedCellStoppingLine σ)
    (hHistory :
      Measurable[extendedStoppedPast σ hσ] (recordPrefix R k))
    (hfinite : ∀ᵐ c ∂cellFamilyLaw ι,
      c ∈ extendedLineFinite σ)
    (base : ℕ → ℝ × S)
    {rate : S → ι → ℝ≥0} (hrate : Measurable rate)
    {step : S → ι → S}
    (hstep : Measurable (Function.uncurry step)) :
    let state : CellFamily ι → S := fun c => (R c k).2
    let τ := stateActiveNextInternal σ state rate
    let next := activeNextRecordValue σ τ state rate step
    let Rnext := extendRecord R k next
    ∃ hτ : ExtendedCellStoppingLine τ,
      Measurable[extendedStoppedPast τ hτ]
          (recordPrefix Rnext (k + 1)) ∧
        (∀ᵐ c ∂cellFamilyLaw ι,
          c ∈ extendedLineFinite τ) ∧
        FreshResidualsAt (cellFamilyLaw ι) Rnext
          (extendedStoppingResidual τ) (k + 1) := by
  dsimp only
  let state : CellFamily ι → S := fun c => (R c k).2
  have hstate : Measurable[extendedStoppedPast σ hσ] state := by
    have heval := (measurable_pi_apply
      (⟨k, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).comp hHistory
    simpa [state, recordPrefix] using measurable_snd.comp heval
  let τ := stateActiveNextInternal σ state rate
  let hτ : ExtendedCellStoppingLine τ :=
    stateActiveNextInternal_isExtendedStoppingLine hσ hstate hrate
  have hle : ∀ c l, σ c l ≤ τ c l :=
    extendedLine_le_stateActiveNextInternal σ state rate
  let next := activeNextRecordValue σ τ state rate step
  have hnext : Measurable[extendedStoppedPast τ hτ] next :=
    measurable_activeNextRecordValue hσ hτ hle hstate hrate hstep
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
    stateActiveNextInternal_finite_ae state rate hfinite hresidual
  have hnextFresh : FreshResidualsAt (cellFamilyLaw ι) Rnext
      (extendedStoppingResidual τ) (k + 1) :=
    extendedCellStoppingLine_freshResidualsAt
      hτ hnextHistory hnextFinite base
  exact ⟨hτ, hnextHistory, hnextFinite, hnextFresh⟩

end StateDependent

/-!
THEOREM LIST
* `activeNextInternal_isExtendedStoppingLine`
* `stateActiveNextInternal_isExtendedStoppingLine`
* `stateActiveNextInternal_finite_ae`
* `activeLineIncrement_pos_iff`
* `oneStepActiveRecordRecursion`

CLOSES
* Zero rates are masked from the minimum and their coordinates do not advance.
* The absorbing branch leaves the line unchanged.
* The state-dependent successor is an `ExtendedCellStoppingLine`.
* A.s. finiteness propagates through both active and absorbing fibres.
* The next record prefix is measurable in the next stopped past.
* Full-vector `FreshResidualsAt` is re-established at `k+1`.

UNFINISHED
* Nothing in the zero-aware stopping-line successor.  The density/channel
  identification and structural iteration are in the next file.
END
-/

end Ripple.Kurtz.StrongApprox.CellZeroAwareExtendedRace

end

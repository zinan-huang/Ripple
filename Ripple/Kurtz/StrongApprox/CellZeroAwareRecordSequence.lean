-- Ripple/Kurtz/StrongApprox/CellZeroAwareRecordSequence.lean
import Ripple.Kurtz.StrongApprox.CellZeroAwareExtendedRace

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellZeroAwareRecordSequence

open MeasureTheory ProbabilityTheory Set Filter Preorder
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open ExponentialRace
open CellStoppingLineFreshness CellExtendedStoppingLine
open CellExtendedRaceRecursion CellExtendedRecordSequence
open CellExtendedRandomTime
open CellZeroAwareExtendedRace
open CellActiveRaceRecordKernel
open CellDensityChannelAlignment

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable [Fintype S] [DecidableEq S] [Countable S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-! ## One structural recursion -/

structure ZeroAwareRecordNode (ι S : Type*) where
  recordTime : CellFamily ι → ℝ
  state : CellFamily ι → S
  line : ExtendedCellLine ι

noncomputable def initialNode
    (ι : Type*) (x0 : S) : ZeroAwareRecordNode ι S where
  recordTime := fun _ => 0
  state := fun _ => x0
  line := initialInternalLine ι

noncomputable def advanceNode
    (rate : S → ι → ℝ≥0) (step : S → ι → S)
    (q : ZeroAwareRecordNode ι S) : ZeroAwareRecordNode ι S :=
  let nextLine := stateActiveNextInternal q.line q.state rate
  let nextValue := activeNextRecordValue
    q.line nextLine q.state rate step
  { recordTime := fun c => (nextValue c).1
    state := fun c => (nextValue c).2
    line := nextLine }

noncomputable def recordNode
    (x0 : S) (rate : S → ι → ℝ≥0) (step : S → ι → S) :
    ℕ → ZeroAwareRecordNode ι S
  | 0 => initialNode ι x0
  | k + 1 => advanceNode rate step (recordNode x0 rate step k)

noncomputable def recursiveRecord
    (x0 : S) (rate : S → ι → ℝ≥0) (step : S → ι → S)
    (c : CellFamily ι) (k : ℕ) : ℝ × S :=
  let q := recordNode x0 rate step k
  (q.recordTime c, q.state c)

noncomputable def recursiveInternal
    (x0 : S) (rate : S → ι → ℝ≥0) (step : S → ι → S)
    (k : ℕ) : ExtendedCellLine ι :=
  (recordNode x0 rate step k).line

@[simp] theorem recursiveRecord_zero
    (x0 : S) (rate : S → ι → ℝ≥0) (step : S → ι → S)
    (c : CellFamily ι) :
    recursiveRecord x0 rate step c 0 = (0, x0) := rfl

@[simp] theorem recursiveInternal_zero
    (x0 : S) (rate : S → ι → ℝ≥0) (step : S → ι → S) :
    recursiveInternal x0 rate step 0 = initialInternalLine ι := rfl

@[simp] theorem recursiveInternal_succ
    (x0 : S) (rate : S → ι → ℝ≥0) (step : S → ι → S)
    (k : ℕ) :
    recursiveInternal x0 rate step (k + 1) =
      stateActiveNextInternal
        (recursiveInternal x0 rate step k)
        (fun c => (recursiveRecord x0 rate step c k).2) rate := rfl

@[simp] theorem recursiveRecord_succ
    (x0 : S) (rate : S → ι → ℝ≥0) (step : S → ι → S)
    (c : CellFamily ι) (k : ℕ) :
    recursiveRecord x0 rate step c (k + 1) =
      activeNextRecordValue
        (recursiveInternal x0 rate step k)
        (recursiveInternal x0 rate step (k + 1))
        (fun z => (recursiveRecord x0 rate step z k).2)
        rate step c := rfl

structure IndexReceipt
    (R : CellFamily ι → ℕ → ℝ × S)
    (internal : ℕ → ExtendedCellLine ι) (k : ℕ) : Prop where
  stopping : ExtendedCellStoppingLine (internal k)
  finite : ∀ᵐ c ∂cellFamilyLaw ι,
    c ∈ extendedLineFinite (internal k)
  history : Measurable[extendedStoppedPast (internal k) stopping]
    (recordPrefix R k)

/-- Iteration of the zero-aware one-step theorem. -/
theorem recursiveIndexReceipt
    (x0 : S) (rate : S → ι → ℝ≥0) (step : S → ι → S)
    (hrate : Measurable rate)
    (hstep : Measurable (Function.uncurry step))
    (k : ℕ) :
    IndexReceipt
      (recursiveRecord x0 rate step)
      (recursiveInternal x0 rate step) k := by
  induction k with
  | zero =>
      have hline : ExtendedCellStoppingLine
          (recursiveInternal x0 rate step 0) := by
        simpa only [recursiveInternal_zero] using
          (initialInternalLine_isExtendedStoppingLine (ι := ι))
      have hfinite : ∀ᵐ c ∂cellFamilyLaw ι,
          c ∈ extendedLineFinite
            (recursiveInternal x0 rate step 0) := by
        simpa only [recursiveInternal_zero] using
          (initialInternalLine_finite_ae (ι := ι))
      have hhistory : Measurable[extendedStoppedPast
          (recursiveInternal x0 rate step 0) hline]
          (recordPrefix (recursiveRecord x0 rate step) 0) := by
        have hzero : recordPrefix (recursiveRecord x0 rate step) 0 =
            fun _ _ => (0, x0) := by
          funext c j
          rcases j with ⟨j, hj⟩
          have hjzero : j = 0 :=
            Nat.le_zero.mp (Finset.mem_Iic.mp hj)
          subst j
          rfl
        rw [hzero]
        exact measurable_const
      exact ⟨hline, hfinite, hhistory⟩
  | succ k ih =>
      let currentState : CellFamily ι → S :=
        fun c => (recursiveRecord x0 rate step c k).2
      let nextLine : ExtendedCellLine ι :=
        stateActiveNextInternal
          (recursiveInternal x0 rate step k) currentState rate
      let nextValue : CellFamily ι → ℝ × S :=
        activeNextRecordValue
          (recursiveInternal x0 rate step k)
          nextLine currentState rate step
      have hresult :
          ∃ hnextLine : ExtendedCellStoppingLine nextLine,
            Measurable[extendedStoppedPast nextLine hnextLine]
                (recordPrefix
                  (extendRecord
                    (recursiveRecord x0 rate step) k nextValue)
                  (k + 1)) ∧
              (∀ᵐ c ∂cellFamilyLaw ι,
                c ∈ extendedLineFinite nextLine) ∧
              FreshResidualsAt (cellFamilyLaw ι)
                (extendRecord
                  (recursiveRecord x0 rate step) k nextValue)
                (extendedStoppingResidual nextLine) (k + 1) := by
        simpa only [currentState, nextLine, nextValue] using
          (oneStepActiveRecordRecursion
            (R := recursiveRecord x0 rate step) (k := k)
            (σ := recursiveInternal x0 rate step k)
            ih.stopping ih.history ih.finite
            (recursiveBase x0) hrate hstep)
      have hlineEq : nextLine =
          recursiveInternal x0 rate step (k + 1) := rfl
      rw [hlineEq] at hresult
      rcases hresult with
        ⟨hline, hhistoryNext, hfiniteNext, _⟩
      have hvalue (c : CellFamily ι) :
          recursiveRecord x0 rate step c (k + 1) = nextValue c := rfl
      have hrecords :
          recordPrefix
              (extendRecord
                (recursiveRecord x0 rate step) k nextValue)
              (k + 1) =
            recordPrefix (recursiveRecord x0 rate step) (k + 1) :=
        recordPrefix_extendRecord_succ
          (recursiveRecord x0 rate step) k nextValue hvalue
      have hhistory : Measurable[extendedStoppedPast
          (recursiveInternal x0 rate step (k + 1)) hline]
          (recordPrefix (recursiveRecord x0 rate step) (k + 1)) := by
        rw [← hrecords]
        exact hhistoryNext
      exact ⟨hline, hfiniteNext, hhistory⟩

/-- Full extended filtration realization for the zero-aware recursion. -/
theorem recursiveFiltrationRealization
    (x0 : S) (rate : S → ι → ℝ≥0) (step : S → ι → S)
    (hrate : Measurable rate)
    (hstep : Measurable (Function.uncurry step)) :
    ExtendedCellRecordFiltrationRealization
      (recursiveRecord x0 rate step)
      (recursiveInternal x0 rate step) := by
  let H := fun k => recursiveIndexReceipt
    x0 rate step hrate hstep k
  exact
    { stopping := fun k => (H k).stopping
      finite := fun k => (H k).finite
      history := fun k => (H k).history }

/-- Full-vector fresh residuals at every recursive record. -/
theorem recursiveFreshResidualsAt
    (x0 : S) (rate : S → ι → ℝ≥0) (step : S → ι → S)
    (hrate : Measurable rate)
    (hstep : Measurable (Function.uncurry step))
    (k : ℕ) :
    FreshResidualsAt (cellFamilyLaw ι)
      (recursiveRecord x0 rate step)
      (extendedStoppingResidual
        (recursiveInternal x0 rate step k)) k :=
  (recursiveFiltrationRealization
    x0 rate step hrate hstep).freshResidualsAt
      (recursiveBase x0) k

/-! ## The aligned active race is the observable successor -/

variable {d : ℕ}
variable {Gamma : Ripple.Kurtz.RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ}
variable {xDensity : Fin d → ℝ}
variable {latticeStart : ∀ n : ℕ, 0 < n → Fin d → Fin (n + 1)}
variable (A : DensityChannelAlignment
  Gamma beta v xDensity latticeStart)
variable {n : ℕ} (hn : 0 < n)
variable (K : KernelReadyDensityChannelAlignment A n hn)

private abbrev DensityState := Fin d → Fin (n + 1)
private abbrev DensityModel := DensityDepCTMC.mk n hn Gamma

@[fun_prop]
theorem measurable_aligned_rate :
    Measurable (A.latticeRate n hn :
      DensityState (n := n) → ι → ℝ≥0) := by
  exact measurable_of_countable _

@[fun_prop]
theorem measurable_aligned_step :
    Measurable (Function.uncurry
      (A.latticeStep n hn : DensityState (n := n) → ι →
        DensityState (n := n))) := by
  exact measurable_of_countable _

theorem aligned_channel_rate_coe
    (x : DensityState (n := n))
    (a : RegenerativeRace.ActiveTarget
      (DensityModel (Gamma := Gamma) hn).toQMatrix x) :
    ((A.latticeRate n hn x (K.embedding.channel x a) : ℝ≥0) : ℝ) =
      (DensityModel (Gamma := Gamma) hn).toQMatrix.rate x a.1 := by
  have hp := RegenerativeRace.targetRate_pos
    (DensityModel (Gamma := Gamma) hn).toQMatrix x a
  have hd : 0 < A.densityRate n hn x
      (K.embedding.channel x a) := by
    rw [← K.rate_eq x a]
    exact hp
  change (Real.toNNReal
    (A.densityRate n hn x (K.embedding.channel x a)) : ℝ) = _
  rw [Real.coe_toNNReal _ hd.le]
  exact (K.rate_eq x a).symm

theorem aligned_channel_rate_pos
    (x : DensityState (n := n))
    (a : RegenerativeRace.ActiveTarget
      (DensityModel (Gamma := Gamma) hn).toQMatrix x) :
    0 < A.latticeRate n hn x (K.embedding.channel x a) := by
  apply (NNReal.coe_pos).mp
  rw [aligned_channel_rate_coe A hn K x a]
  exact RegenerativeRace.targetRate_pos
    (DensityModel (Gamma := Gamma) hn).toQMatrix x a

include K in
theorem aligned_has_active_iff
    (x : DensityState (n := n)) :
    HasActiveRate (A.latticeRate n hn x) ↔
      ¬ (DensityModel (Gamma := Gamma) hn).toQMatrix.IsAbsorbing x := by
  constructor
  · rintro ⟨l, hl⟩ habs
    obtain ⟨a, ha⟩ := K.complete x l hl
    exact a.2.2 (QMatrix.IsAbsorbing.rate_eq_zero _ habs a.1 a.2.1.symm)
  · intro hnon
    letI : Nonempty (RegenerativeRace.ActiveTarget
        (DensityModel (Gamma := Gamma) hn).toQMatrix x) :=
      RegenerativeRace.activeTarget_nonempty
        (DensityModel (Gamma := Gamma) hn).toQMatrix hnon
    let a : RegenerativeRace.ActiveTarget
        (DensityModel (Gamma := Gamma) hn).toQMatrix x :=
      Classical.choice inferInstance
    exact ⟨K.embedding.channel x a,
      aligned_channel_rate_pos A hn K x a⟩

theorem aligned_channel_step
    (x : DensityState (n := n))
    (a : RegenerativeRace.ActiveTarget
      (DensityModel (Gamma := Gamma) hn).toQMatrix x) :
    A.latticeStep n hn x (K.embedding.channel x a) = a.1 := by
  have hp := aligned_channel_rate_pos A hn K x a
  have hs := A.latticeStep_spec_of_positive n hn x
    (K.embedding.channel x a) hp
  funext i
  apply Fin.ext
  have hi := hs i
  have hj := K.jump_eq x a i
  have hz :
      (A.latticeStep n hn x (K.embedding.channel x a) i : ℤ) =
        (a.1 i : ℤ) := by
    linarith
  exact_mod_cast hz

/-- Strict winners exist almost surely for every finite positive race. -/
theorem strictWinner_exists_ae
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ a, 0 < r a) :
    ∀ᵐ E ∂clockLaw κ, ∃ a, strictClockWin r a E := by
  let U : Set (κ → ℝ) := ⋃ a, {E | strictClockWin r a E}
  have hU : MeasurableSet U :=
    MeasurableSet.iUnion fun a => strictClockWin_measurableSet r a
  have hdisj : Pairwise fun a b : κ => Disjoint
      {E : κ → ℝ | strictClockWin r a E}
      {E : κ → ℝ | strictClockWin r b E} := by
    intro a b hab
    rw [Set.disjoint_left]
    intro E ha hb
    exact (ha b hab.symm).asymm (hb a hab)
  have hmass : clockLaw κ U = 1 := by
    rw [measure_iUnion hdisj
      (fun a => strictClockWin_measurableSet r a), tsum_fintype]
    simp_rw [strictClockWin_measure_of_rates r hr]
    have hsum : ∑ a, r a / rateTotal r = 1 :=
      sum_normalizedRate r hr
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun a _ => div_nonneg (hr a).le
        (rateTotal_pos r hr).le), hsum]
    norm_num
  have hae := (mem_ae_iff_prob_eq_one hU).2 hmass
  filter_upwards [hae] with E hE
  exact Set.mem_iUnion.mp hE

theorem cellStrictWinner_exists_ae
    (x : DensityState (n := n))
    (hnon : ¬ (DensityModel (Gamma := Gamma) hn).toQMatrix.IsAbsorbing x) :
    ∀ᵐ E ∂clockLaw ι,
      ∃ a : RegenerativeRace.ActiveTarget
        (DensityModel (Gamma := Gamma) hn).toQMatrix x,
        strictClockWin
          (RegenerativeRace.targetRate
            (DensityModel (Gamma := Gamma) hn).toQMatrix x) a
          (cellStateClocks K.embedding x E) := by
  letI : Nonempty (RegenerativeRace.ActiveTarget
      (DensityModel (Gamma := Gamma) hn).toQMatrix x) :=
    RegenerativeRace.activeTarget_nonempty
      (DensityModel (Gamma := Gamma) hn).toQMatrix hnon
  have htarget := strictWinner_exists_ae
    (RegenerativeRace.targetRate
      (DensityModel (Gamma := Gamma) hn).toQMatrix x)
    (RegenerativeRace.targetRate_pos
      (DensityModel (Gamma := Gamma) hn).toQMatrix x)
  have hmapped :
      ∀ᵐ z ∂(clockLaw ι).map (cellStateClocks K.embedding x),
        ∃ a, strictClockWin
          (RegenerativeRace.targetRate
            (DensityModel (Gamma := Gamma) hn).toQMatrix x) a z := by
    rw [cellStateClocks_law K.embedding x]
    exact htarget
  exact MeasureTheory.ae_of_ae_map
    (measurable_cellStateClocks K.embedding x).aemeasurable hmapped

/-- Conditional on the record past, the current-state active race has a strict
winner almost surely. -/
theorem currentStateStrictWinner_ae
    {record : CellFamily ι → ℕ → ℝ × DensityState (n := n)}
    {residual : CellFamily ι → ι → ℝ} {k : ℕ}
    (H : FreshResidualsAt (cellFamilyLaw ι) record residual k) :
    ∀ᵐ c ∂cellFamilyLaw ι,
      (DensityModel (Gamma := Gamma) hn).toQMatrix.IsAbsorbing
          (record c k).2 ∨
        ∃ a : RegenerativeRace.ActiveTarget
          (DensityModel (Gamma := Gamma) hn).toQMatrix (record c k).2,
          strictClockWin
            (RegenerativeRace.targetRate
              (DensityModel (Gamma := Gamma) hn).toQMatrix (record c k).2) a
            (cellStateClocks K.embedding (record c k).2 (residual c)) := by
  classical
  have hall : ∀ᵐ c ∂cellFamilyLaw ι, ∀ x : DensityState (n := n),
      (record c k).2 = x →
        (DensityModel (Gamma := Gamma) hn).toQMatrix.IsAbsorbing x ∨
          ∃ a : RegenerativeRace.ActiveTarget
            (DensityModel (Gamma := Gamma) hn).toQMatrix x,
            strictClockWin
              (RegenerativeRace.targetRate
                (DensityModel (Gamma := Gamma) hn).toQMatrix x) a
              (cellStateClocks K.embedding x (residual c)) := by
    apply ae_all_iff.2
    intro x
    by_cases habs :
        (DensityModel (Gamma := Gamma) hn).toQMatrix.IsAbsorbing x
    · filter_upwards [] with c
      intro _
      exact Or.inl habs
    · let good : Set (ι → ℝ) :=
        {E | ∃ a : RegenerativeRace.ActiveTarget
          (DensityModel (Gamma := Gamma) hn).toQMatrix x,
          strictClockWin
            (RegenerativeRace.targetRate
              (DensityModel (Gamma := Gamma) hn).toQMatrix x) a
            (cellStateClocks K.embedding x E)}
      have hgood : MeasurableSet good := by
        let U : Set
            (RegenerativeRace.ActiveTarget
              (DensityModel (Gamma := Gamma) hn).toQMatrix x → ℝ) :=
          ⋃ a, {z | strictClockWin
            (RegenerativeRace.targetRate
              (DensityModel (Gamma := Gamma) hn).toQMatrix x) a z}
        have hU : MeasurableSet U :=
          MeasurableSet.iUnion fun a => strictClockWin_measurableSet _ a
        have heq : good = (cellStateClocks K.embedding x) ⁻¹' U := by
          ext E
          simp [good, U]
        rw [heq]
        exact hU.preimage (measurable_cellStateClocks K.embedding x)
      have hclock : clockLaw ι goodᶜ = 0 := by
        have hw := cellStrictWinner_exists_ae A hn K x habs
        rw [ae_iff] at hw
        exact hw
      let histories := (i : Finset.Iic k) →
        ℝ × DensityState (d := d) (n := n)
      let current : histories → DensityState (n := n) :=
        QMatrix.currentStateFromHistory k
      have hcurrent : Measurable current :=
        measurable_snd.comp (measurable_pi_apply
          (⟨k, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k))
      let historySet : Set histories := {hist | current hist = x}
      have hhistorySet : MeasurableSet historySet :=
        hcurrent (measurableSet_singleton x)
      have hm := H.measure_history_residual
        hhistorySet hgood.compl
      rw [hclock, mul_zero] at hm
      rw [ae_iff]
      have heq :
          {c | ¬ ((record c k).2 = x →
            (DensityModel (Gamma := Gamma) hn).toQMatrix.IsAbsorbing x ∨
              ∃ a, strictClockWin
                (RegenerativeRace.targetRate
                  (DensityModel (Gamma := Gamma) hn).toQMatrix x) a
                (cellStateClocks K.embedding x (residual c)))} =
          {c | recordPrefix record k c ∈ historySet ∧ residual c ∈ goodᶜ} := by
        ext c
        simp [historySet, current, good, recordPrefix,
          QMatrix.currentStateFromHistory, habs]
        exact fun _ => Iff.rfl
      rw [heq]
      exact hm
  filter_upwards [hall] with c hc
  exact hc (record c k).2 rfl

private theorem activeRaceTerm_toReal
    {σ : ExtendedCellLine ι} {rate : ι → ℝ≥0}
    {c : CellFamily ι} {l : ι} (hl : 0 < rate l) :
    (activeRaceTermE σ rate c l).toReal =
      extendedStoppingResidual σ c l / (rate l : ℝ) := by
  simp [activeRaceTermE, hl, extendedStoppingResidual,
    CellRandomTimeEvaluation.residualVector,
    CellRandomTimeEvaluation.residualWait,
    extendedResidualWaitE, ENNReal.toReal_div]

/-- On a strict target winner, the masked channel minimum is exactly that
winner's scaled residual. -/
theorem alignedRaceWait_eq_winner
    {σ : ExtendedCellLine ι} {c : CellFamily ι}
    (x : DensityState (n := n))
    (hres : ∀ l, extendedResidualWaitE σ c l ≠ ∞)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel (Gamma := Gamma) hn).toQMatrix x)
    (ha : strictClockWin
      (RegenerativeRace.targetRate
        (DensityModel (Gamma := Gamma) hn).toQMatrix x) a
      (cellStateClocks K.embedding x
        (extendedStoppingResidual σ c))) :
    activeRaceWaitE σ (A.latticeRate n hn x) c =
      activeRaceTermE σ (A.latticeRate n hn x) c
        (K.embedding.channel x a) := by
  classical
  have hactive := (aligned_has_active_iff A hn K x).2
    (fun habs => a.2.2
      (QMatrix.IsAbsorbing.rate_eq_zero _ habs a.1 a.2.1.symm))
  rw [activeRaceWaitE, if_pos hactive]
  apply le_antisymm
  · exact iInf_le _ (K.embedding.channel x a)
  · apply le_iInf
    intro l
    by_cases hl : 0 < A.latticeRate n hn x l
    · obtain ⟨b, hb⟩ := K.complete x l hl
      subst l
      by_cases hba : b = a
      · subst b
        exact le_rfl
      · have hpa := aligned_channel_rate_pos A hn K x a
        have hpb := aligned_channel_rate_pos A hn K x b
        have hleft : activeRaceTermE σ (A.latticeRate n hn x) c
            (K.embedding.channel x a) ≠ ∞ := by
          simp only [activeRaceTermE, if_pos hpa]
          exact ENNReal.div_ne_top (hres _)
            (by exact_mod_cast hpa.ne')
        have hright : activeRaceTermE σ (A.latticeRate n hn x) c
            (K.embedding.channel x b) ≠ ∞ := by
          simp only [activeRaceTermE, if_pos hpb]
          exact ENNReal.div_ne_top (hres _)
            (by exact_mod_cast hpb.ne')
        apply (ENNReal.toReal_le_toReal hleft hright).mp
        rw [activeRaceTerm_toReal hpa,
          activeRaceTerm_toReal hpb,
          aligned_channel_rate_coe A hn K x a,
          aligned_channel_rate_coe A hn K x b]
        simpa [cellStateClocks, RegenerativeRace.targetRate] using
          (ha b hba).le
    · simp [activeRaceTermE, hl]

private theorem firstPositiveChannel_eq_of_unique
    (z : ι → ℕ) (winner : ι)
    (hpos : 0 < z winner)
    (hother : ∀ l, l ≠ winner → ¬ 0 < z l) :
    firstPositiveChannel z = winner := by
  classical
  unfold firstPositiveChannel
  rw [dif_pos ⟨winner, hpos⟩]
  let chosen := Classical.choose
    (show ∃ l, 0 < z l from ⟨winner, hpos⟩)
  have hchosen : 0 < z chosen :=
    Classical.choose_spec
      (show ∃ l, 0 < z l from ⟨winner, hpos⟩)
  by_contra hne
  exact hother chosen hne hchosen

/-- Pointwise race observation on the probability-one finite/strict event. -/
theorem alignedNextRecord_eq_cellRaceStep
    {σ : ExtendedCellLine ι}
    (state : CellFamily ι → DensityState (n := n))
    (c : CellFamily ι)
    (hline : c ∈ extendedLineFinite σ)
    (hres : ∀ l, extendedResidualWaitE σ c l ≠ ∞)
    (hgood :
      (DensityModel (Gamma := Gamma) hn).toQMatrix.IsAbsorbing
          (state c) ∨
        ∃ a : RegenerativeRace.ActiveTarget
          (DensityModel (Gamma := Gamma) hn).toQMatrix (state c),
          strictClockWin
            (RegenerativeRace.targetRate
              (DensityModel (Gamma := Gamma) hn).toQMatrix (state c)) a
            (cellStateClocks K.embedding (state c)
              (extendedStoppingResidual σ c))) :
    activeNextRecordValue σ
        (stateActiveNextInternal σ state (A.latticeRate n hn))
        state (A.latticeRate n hn) (A.latticeStep n hn) c =
      cellRaceStep (DensityModel (Gamma := Gamma) hn).toQMatrix
        K.embedding (state c)
        (extendedStoppingResidual σ c) := by
  classical
  let Q := (DensityModel (Gamma := Gamma) hn).toQMatrix
  let x := state c
  by_cases habs : Q.IsAbsorbing x
  · have hno : ¬ HasActiveRate (A.latticeRate n hn x) := by
      rw [aligned_has_active_iff A hn K x]
      exact not_not.mpr habs
    rw [cellRaceStep_eq_of_absorbing Q K.embedding habs]
    simp [activeNextRecordValue, x, hno]
  · obtain ⟨winner, hwinnerStrict⟩ := hgood.resolve_left habs
    have hactive : HasActiveRate (A.latticeRate n hn x) :=
      (aligned_has_active_iff A hn K x).2 habs
    have hwaitEq := alignedRaceWait_eq_winner
      A hn K x hres winner hwinnerStrict
    have hwinnerRate := aligned_channel_rate_pos A hn K x winner
    have hwinnerTermFinite :
        activeRaceTermE σ (A.latticeRate n hn x) c
          (K.embedding.channel x winner) ≠ ∞ := by
      simp only [activeRaceTermE, if_pos hwinnerRate]
      exact ENNReal.div_ne_top (hres _)
        (by exact_mod_cast hwinnerRate.ne')
    have hwaitFinite :
        activeRaceWaitE σ (A.latticeRate n hn x) c ≠ ∞ := by
      rw [hwaitEq]
      exact hwinnerTermFinite
    have hwinnerThreshold :
        extendedResidualWaitE σ c (K.embedding.channel x winner) ≤
          (A.latticeRate n hn x (K.embedding.channel x winner) : ℝ≥0∞) *
            activeRaceWaitE σ (A.latticeRate n hn x) c := by
      have hdiv :
          extendedResidualWaitE σ c (K.embedding.channel x winner) /
              (A.latticeRate n hn x
                (K.embedding.channel x winner) : ℝ≥0∞) ≤
            activeRaceWaitE σ (A.latticeRate n hn x) c := by
        rw [hwaitEq]
        simp only [activeRaceTermE, if_pos hwinnerRate, le_refl]
      exact (ENNReal.div_le_iff
        (by exact_mod_cast hwinnerRate.ne') ENNReal.coe_ne_top).1 hdiv
        |>.trans_eq (by rw [mul_comm])
    have hwinnerInc :
        0 < lineIncrement σ
          (activeNextInternal σ (A.latticeRate n hn x))
          (K.embedding.channel x winner) c :=
      (activeLineIncrement_pos_iff
        (hline _) hwaitFinite hwinnerRate).2 hwinnerThreshold
    have hother : ∀ l,
        l ≠ K.embedding.channel x winner →
        ¬ 0 < lineIncrement σ
          (activeNextInternal σ (A.latticeRate n hn x)) l c := by
      intro l hne
      by_cases hl : 0 < A.latticeRate n hn x l
      · obtain ⟨other, hotherChannel⟩ := K.complete x l hl
        have hotherNe : other ≠ winner := by
          intro heq
          subst other
          exact hne hotherChannel.symm
        intro hinc
        have hthreshold :=
          (activeLineIncrement_pos_iff (hline l) hwaitFinite hl).1 hinc
        have hdiv :
            activeRaceTermE σ (A.latticeRate n hn x) c l ≤
              activeRaceWaitE σ (A.latticeRate n hn x) c := by
          simp only [activeRaceTermE, if_pos hl]
          exact (ENNReal.div_le_iff
            (by exact_mod_cast hl.ne') ENNReal.coe_ne_top).2
            (by simpa [mul_comm] using hthreshold)
        rw [← hotherChannel, hwaitEq] at hdiv
        have hotherRate := aligned_channel_rate_pos A hn K x other
        have hotherFinite :
            activeRaceTermE σ (A.latticeRate n hn x) c
              (K.embedding.channel x other) ≠ ∞ := by
          simp only [activeRaceTermE, if_pos hotherRate]
          exact ENNReal.div_ne_top (hres _)
            (by exact_mod_cast hotherRate.ne')
        have hreal :=
          (ENNReal.toReal_le_toReal hotherFinite hwinnerTermFinite).mpr hdiv
        rw [activeRaceTerm_toReal hotherRate,
          activeRaceTerm_toReal hwinnerRate,
          aligned_channel_rate_coe A hn K x other,
          aligned_channel_rate_coe A hn K x winner] at hreal
        have hstrict := hwinnerStrict other hotherNe
        simp [cellStateClocks, RegenerativeRace.targetRate] at hstrict
        linarith
      · have hz : A.latticeRate n hn x l = 0 :=
          le_antisymm (not_lt.mp hl) zero_le
        intro hinc
        have heq :
            activeNextInternal σ (A.latticeRate n hn x) c l = σ c l := by
          simp [activeNextInternal, hz]
        simp [lineIncrement, extendedPathAt, finitePart, heq] at hinc
    have hobsWinner :
        observableWinner σ
          (stateActiveNextInternal σ state (A.latticeRate n hn)) c =
            K.embedding.channel x winner := by
      unfold observableWinner
      have hcongr :
          (fun l => lineIncrement σ
            (stateActiveNextInternal σ state (A.latticeRate n hn)) l c) =
          (fun l => lineIncrement σ
            (activeNextInternal σ (A.latticeRate n hn (state c))) l c) := by
        funext l
        unfold lineIncrement extendedPathAt finitePart
        rw [stateActiveNextInternal_eq_fixed]
      rw [hcongr]
      exact firstPositiveChannel_eq_of_unique _ _ hwinnerInc hother
    have hholding :
        observableActiveHoldingTime σ
          (stateActiveNextInternal σ state (A.latticeRate n hn))
          state (A.latticeRate n hn) c =
        (activeRaceWaitE σ (A.latticeRate n hn x) c).toReal := by
      rw [observableActiveHoldingTime_eq_of_active
        σ _ state (A.latticeRate n hn) c hactive, hobsWinner,
        stateActiveNextInternal_eq_fixed]
      simp only [activeNextInternal]
      have hcancel :
          ((A.latticeRate n hn x (K.embedding.channel x winner) : ℝ≥0∞) *
              activeRaceWaitE σ (A.latticeRate n hn x) c) /
            (A.latticeRate n hn x (K.embedding.channel x winner) : ℝ≥0∞) =
          activeRaceWaitE σ (A.latticeRate n hn x) c := by
        rw [div_eq_mul_inv, mul_comm
          (A.latticeRate n hn x (K.embedding.channel x winner) : ℝ≥0∞)
          (activeRaceWaitE σ (A.latticeRate n hn x) c), mul_assoc,
          ENNReal.mul_inv_cancel (by exact_mod_cast hwinnerRate.ne')
            ENNReal.coe_ne_top, mul_one]
      rw [ENNReal.add_sub_cancel_left (hline _), hcancel]
    have hstep := aligned_channel_step A hn K x winner
    rw [cellRaceStep_eq_of_nonabsorbing Q K.embedding habs]
    unfold liveCellRaceStep
    letI : Nonempty (RegenerativeRace.ActiveTarget Q x) :=
      RegenerativeRace.activeTarget_nonempty Q habs
    have hraceWinner := raceWinner_eq_of_strict
      (RegenerativeRace.targetRate Q x) winner
      (cellStateClocks K.embedding x
        (extendedStoppingResidual σ c)) hwinnerStrict
    rw [activeNextRecordValue, if_pos hactive]
    rw [hobsWinner, hholding, hstep]
    simp only [racePair, raceWait, hraceWinner]
    rw [hwaitEq, activeRaceTerm_toReal hwinnerRate,
      aligned_channel_rate_coe A hn K x winner]
    simp only [cellStateClocks, RegenerativeRace.targetRate, Q]

/-- The recursive observable successor agrees almost surely with the canonical
active-target row. -/
theorem alignedNextRecord_eq_cellRaceStep_ae
    (hrate : Measurable (A.latticeRate n hn :
      DensityState (n := n) → ι → ℝ≥0))
    (hstep : Measurable (Function.uncurry
      (A.latticeStep n hn : DensityState (n := n) → ι →
        DensityState (n := n))))
    (hfiltration : ExtendedCellRecordFiltrationRealization
      (recursiveRecord (latticeStart n hn)
        (A.latticeRate n hn) (A.latticeStep n hn))
      (recursiveInternal (latticeStart n hn)
        (A.latticeRate n hn) (A.latticeStep n hn)))
    (k : ℕ) :
    ∀ᵐ c ∂cellFamilyLaw ι,
      recursiveRecord (latticeStart n hn)
          (A.latticeRate n hn) (A.latticeStep n hn) c (k + 1) =
        cellRaceStep (DensityModel (Gamma := Gamma) hn).toQMatrix
          K.embedding
          (recursiveRecord (latticeStart n hn)
            (A.latticeRate n hn) (A.latticeStep n hn) c k).2
          (extendedStoppingResidual
            (recursiveInternal (latticeStart n hn)
              (A.latticeRate n hn) (A.latticeStep n hn) k) c) := by
  let H := hfiltration.freshResidualsAt
    (fun _ => (0, latticeStart n hn)) k
  have hres := residualWaitE_finite_ae H
  have hgood := currentStateStrictWinner_ae A hn K H
  have hline := hfiltration.finite k
  filter_upwards [hline, hres, hgood] with c hc hrc hgc
  have hrec := recursiveRecord_succ
    (x0 := latticeStart n hn)
    (rate := A.latticeRate n hn)
    (step := A.latticeStep n hn) c k
  rw [hrec, recursiveInternal_succ]
  exact alignedNextRecord_eq_cellRaceStep A hn K
    (fun z => (recursiveRecord (latticeStart n hn)
      (A.latticeRate n hn) (A.latticeStep n hn) z k).2) c hc hrc hgc

/-! ## Density specialization and canonical laws -/

/-- The generic recursive record with aligned lattice rates is exactly the
zero-aware recursion hypothesis. -/
theorem densityZeroAwareCellRecordRecursion :
    ZeroAwareCellRecordRecursion
      (DensityModel (Gamma := Gamma) hn).toQMatrix
      (latticeStart n hn)
      (recursiveRecord (latticeStart n hn)
        (A.latticeRate n hn) (A.latticeStep n hn))
      (recursiveInternal (latticeStart n hn)
        (A.latticeRate n hn) (A.latticeStep n hn))
      K.embedding := by
  let hrate := measurable_aligned_rate A hn
  let hstep := measurable_aligned_step A hn
  let hfiltration := recursiveFiltrationRealization
    (latticeStart n hn) (A.latticeRate n hn)
      (A.latticeStep n hn) hrate hstep
  refine
    { filtration := hfiltration
      initial := ?_
      step := ?_ }
  · rw [Measure.map_map
      (measurable_frestrictLe
        (X := fun _ : ℕ => ℝ × DensityState (n := n)) 0)
      hfiltration.measurable_record]
    have hconst :
        (frestrictLe
          (π := fun _ : ℕ => ℝ × DensityState (n := n)) 0) ∘
            recursiveRecord (latticeStart n hn)
              (A.latticeRate n hn) (A.latticeStep n hn) =
          fun _ => (MeasurableEquiv.piUnique
            (fun _ : Finset.Iic 0 =>
              ℝ × DensityState (n := n))).symm
                (0, latticeStart n hn) := by
      funext c i
      rcases i with ⟨i, hi⟩
      have hizero : i = 0 :=
        Nat.le_zero.mp (Finset.mem_Iic.mp hi)
      subst i
      rfl
    rw [hconst]
    simp
  · intro k
    exact alignedNextRecord_eq_cellRaceStep_ae
      A hn K hrate hstep hfiltration k

include K in
/-- Canonical record law of the actual zero-aware cell recursion. -/
theorem densityCellRecord_law :
    (cellFamilyLaw ι).map
        (recursiveRecord (latticeStart n hn)
          (A.latticeRate n hn) (A.latticeStep n hn)) =
      (DensityModel (Gamma := Gamma) hn).toQMatrix.canonicalRecordMeasure
        (latticeStart n hn) :=
  (densityZeroAwareCellRecordRecursion A hn K).record_law

include K in
/-- Canonical density readout law of the zero-aware cell-built process. -/
theorem densityCellReadout_law :
    (cellFamilyLaw ι).map
        (AlignedCellCoupling.canonicalDensityNonnegative
          (DensityModel (Gamma := Gamma) hn) ∘
          recursiveRecord (latticeStart n hn)
            (A.latticeRate n hn) (A.latticeStep n hn)) =
      ((DensityModel (Gamma := Gamma) hn).toQMatrix.canonicalRecordMeasure
        (latticeStart n hn)).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityModel (Gamma := Gamma) hn)) :=
  (densityZeroAwareCellRecordRecursion A hn K).readout_law

/-!
THEOREM LIST
* `recursiveIndexReceipt`
* `recursiveFiltrationRealization`
* `recursiveFreshResidualsAt`
* `strictWinner_exists_ae`
* `currentStateStrictWinner_ae`
* `alignedNextRecord_eq_cellRaceStep`
* `densityZeroAwareCellRecordRecursion`
* `densityCellRecord_law`
* `densityCellReadout_law`

CLOSES
* One structural recursion carrying record time, lattice state, and extended
  internal line.
* Iteration of the zero-aware successor for every record index.
* Full-vector freshness at every index, including coordinates that are
  currently inactive.
* Almost-sure identification of the observable successor with the
  `cellRaceStep` of `CellZeroAwareExtendedRace`.
* An inhabitant of `ZeroAwareCellRecordRecursion`.
* `IsDensityRecordRealization`, canonical record law, and canonical density
  readout law for the cell-built record process.

UNFINISHED
* `K : KernelReadyDensityChannelAlignment A n hn` is an explicit input;
  deriving it from `DensityChannelAlignment` remains that file's finite
  channel-aggregation item.
* Equality of this canonical record readout with the original
  `cellTimeChangeNonnegative` path remains the separate β/v pathwise
  identification item.
END
-/

end Ripple.Kurtz.StrongApprox.CellZeroAwareRecordSequence

end

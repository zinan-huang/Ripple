-- Ripple/Kurtz/StrongApprox/CellPerScaleRecordRecursion.lean
import Ripple.Kurtz.StrongApprox.CellPerScaleDensityAlignment

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellPerScaleRecordRecursion

open MeasureTheory ProbabilityTheory Set Filter Preorder
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open Ripple.Kurtz
open ExponentialRace
open CellStoppingLineFreshness CellExtendedStoppingLine
open CellExtendedRaceRecursion
open CellExtendedRandomTime
open CellZeroAwareExtendedRace
open CellActiveRaceRecordKernel
open CellDensityChannelAlignment
open CellPerScaleDensityAlignment
open CellZeroAwareRecordSequence
  (strictWinner_exists_ae recursiveRecord recursiveInternal
    recursiveFiltrationRealization recursiveRecord_succ
    recursiveInternal_succ)

/-! ## Scale-free active race data

The recursion proof never uses the density alignment itself, only the
three facts below about the active-target embedding at one scale. -/

section Generic

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable [Fintype S] [DecidableEq S] [Countable S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable {Q : QMatrix S} {rate : S → ι → ℝ≥0} {step : S → ι → S}

structure ActiveRaceData (Q : QMatrix S) (rate : S → ι → ℝ≥0)
    (step : S → ι → S) : Type _ where
  embedding : ActiveTargetClockEmbedding Q ι
  rate_coe : ∀ x (a : RegenerativeRace.ActiveTarget Q x),
    ((rate x (embedding.channel x a) : ℝ≥0) : ℝ) = Q.rate x a.1
  step_eq : ∀ x (a : RegenerativeRace.ActiveTarget Q x),
    step x (embedding.channel x a) = a.1
  complete : ∀ x l, 0 < rate x l →
    ∃ a : RegenerativeRace.ActiveTarget Q x, embedding.channel x a = l

variable (R : ActiveRaceData Q rate step)

theorem aligned_channel_rate_pos
    (x : S) (a : RegenerativeRace.ActiveTarget Q x) :
    0 < rate x (R.embedding.channel x a) := by
  apply (NNReal.coe_pos).mp
  rw [R.rate_coe x a]
  exact RegenerativeRace.targetRate_pos Q x a

include R in
theorem aligned_has_active_iff (x : S) :
    HasActiveRate (rate x) ↔ ¬ Q.IsAbsorbing x := by
  constructor
  · rintro ⟨l, hl⟩ habs
    obtain ⟨a, ha⟩ := R.complete x l hl
    exact a.2.2 (QMatrix.IsAbsorbing.rate_eq_zero _ habs a.1 a.2.1.symm)
  · intro hnon
    letI : Nonempty (RegenerativeRace.ActiveTarget Q x) :=
      RegenerativeRace.activeTarget_nonempty Q hnon
    let a : RegenerativeRace.ActiveTarget Q x :=
      Classical.choice inferInstance
    exact ⟨R.embedding.channel x a, aligned_channel_rate_pos R x a⟩

theorem cellStrictWinner_exists_ae
    (x : S)
    (hnon : ¬ Q.IsAbsorbing x) :
    ∀ᵐ E ∂clockLaw ι,
      ∃ a : RegenerativeRace.ActiveTarget
        Q x,
        strictClockWin
          (RegenerativeRace.targetRate
            Q x) a
          (cellStateClocks R.embedding x E) := by
  letI : Nonempty (RegenerativeRace.ActiveTarget
      Q x) :=
    RegenerativeRace.activeTarget_nonempty
      Q hnon
  have htarget := strictWinner_exists_ae
    (RegenerativeRace.targetRate
      Q x)
    (RegenerativeRace.targetRate_pos
      Q x)
  have hmapped :
      ∀ᵐ z ∂(clockLaw ι).map (cellStateClocks R.embedding x),
        ∃ a, strictClockWin
          (RegenerativeRace.targetRate
            Q x) a z := by
    rw [cellStateClocks_law R.embedding x]
    exact htarget
  exact MeasureTheory.ae_of_ae_map
    (measurable_cellStateClocks R.embedding x).aemeasurable hmapped

/-- Conditional on the record past, the current-state active race has a strict
winner almost surely. -/
theorem currentStateStrictWinner_ae
    {record : CellFamily ι → ℕ → ℝ × S}
    {residual : CellFamily ι → ι → ℝ} {k : ℕ}
    (H : FreshResidualsAt (cellFamilyLaw ι) record residual k) :
    ∀ᵐ c ∂cellFamilyLaw ι,
      Q.IsAbsorbing
          (record c k).2 ∨
        ∃ a : RegenerativeRace.ActiveTarget
          Q (record c k).2,
          strictClockWin
            (RegenerativeRace.targetRate
              Q (record c k).2) a
            (cellStateClocks R.embedding (record c k).2 (residual c)) := by
  classical
  have hall : ∀ᵐ c ∂cellFamilyLaw ι, ∀ x : S,
      (record c k).2 = x →
        Q.IsAbsorbing x ∨
          ∃ a : RegenerativeRace.ActiveTarget
            Q x,
            strictClockWin
              (RegenerativeRace.targetRate
                Q x) a
              (cellStateClocks R.embedding x (residual c)) := by
    apply ae_all_iff.2
    intro x
    by_cases habs :
        Q.IsAbsorbing x
    · filter_upwards [] with c
      intro _
      exact Or.inl habs
    · let good : Set (ι → ℝ) :=
        {E | ∃ a : RegenerativeRace.ActiveTarget
          Q x,
          strictClockWin
            (RegenerativeRace.targetRate
              Q x) a
            (cellStateClocks R.embedding x E)}
      have hgood : MeasurableSet good := by
        let U : Set
            (RegenerativeRace.ActiveTarget
              Q x → ℝ) :=
          ⋃ a, {z | strictClockWin
            (RegenerativeRace.targetRate
              Q x) a z}
        have hU : MeasurableSet U :=
          MeasurableSet.iUnion fun a => strictClockWin_measurableSet _ a
        have heq : good = (cellStateClocks R.embedding x) ⁻¹' U := by
          ext E
          simp [good, U]
        rw [heq]
        exact hU.preimage (measurable_cellStateClocks R.embedding x)
      have hclock : clockLaw ι goodᶜ = 0 := by
        have hw := cellStrictWinner_exists_ae R x habs
        rw [ae_iff] at hw
        exact hw
      let histories := (i : Finset.Iic k) →
        ℝ × S
      let current : histories → S :=
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
            Q.IsAbsorbing x ∨
              ∃ a, strictClockWin
                (RegenerativeRace.targetRate
                  Q x) a
                (cellStateClocks R.embedding x (residual c)))} =
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
    (x : S)
    (hres : ∀ l, extendedResidualWaitE σ c l ≠ ∞)
    (a : RegenerativeRace.ActiveTarget
      Q x)
    (ha : strictClockWin
      (RegenerativeRace.targetRate
        Q x) a
      (cellStateClocks R.embedding x
        (extendedStoppingResidual σ c))) :
    activeRaceWaitE σ (rate x) c =
      activeRaceTermE σ (rate x) c
        (R.embedding.channel x a) := by
  classical
  have hactive := (aligned_has_active_iff R x).2
    (fun habs => a.2.2
      (QMatrix.IsAbsorbing.rate_eq_zero _ habs a.1 a.2.1.symm))
  rw [activeRaceWaitE, if_pos hactive]
  apply le_antisymm
  · exact iInf_le _ (R.embedding.channel x a)
  · apply le_iInf
    intro l
    by_cases hl : 0 < rate x l
    · obtain ⟨b, hb⟩ := R.complete x l hl
      subst l
      by_cases hba : b = a
      · subst b
        exact le_rfl
      · have hpa := aligned_channel_rate_pos R x a
        have hpb := aligned_channel_rate_pos R x b
        have hleft : activeRaceTermE σ (rate x) c
            (R.embedding.channel x a) ≠ ∞ := by
          simp only [activeRaceTermE, if_pos hpa]
          exact ENNReal.div_ne_top (hres _)
            (by exact_mod_cast hpa.ne')
        have hright : activeRaceTermE σ (rate x) c
            (R.embedding.channel x b) ≠ ∞ := by
          simp only [activeRaceTermE, if_pos hpb]
          exact ENNReal.div_ne_top (hres _)
            (by exact_mod_cast hpb.ne')
        apply (ENNReal.toReal_le_toReal hleft hright).mp
        rw [activeRaceTerm_toReal hpa,
          activeRaceTerm_toReal hpb,
          R.rate_coe x a,
          R.rate_coe x b]
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
    (state : CellFamily ι → S)
    (c : CellFamily ι)
    (hline : c ∈ extendedLineFinite σ)
    (hres : ∀ l, extendedResidualWaitE σ c l ≠ ∞)
    (hgood :
      Q.IsAbsorbing
          (state c) ∨
        ∃ a : RegenerativeRace.ActiveTarget
          Q (state c),
          strictClockWin
            (RegenerativeRace.targetRate
              Q (state c)) a
            (cellStateClocks R.embedding (state c)
              (extendedStoppingResidual σ c))) :
    activeNextRecordValue σ
        (stateActiveNextInternal σ state (rate))
        state (rate) (step) c =
      cellRaceStep Q
        R.embedding (state c)
        (extendedStoppingResidual σ c) := by
  classical
  let x := state c
  by_cases habs : Q.IsAbsorbing x
  · have hno : ¬ HasActiveRate (rate x) := by
      rw [aligned_has_active_iff R x]
      exact not_not.mpr habs
    rw [cellRaceStep_eq_of_absorbing Q R.embedding habs]
    simp [activeNextRecordValue, x, hno]
  · obtain ⟨winner, hwinnerStrict⟩ := hgood.resolve_left habs
    have hactive : HasActiveRate (rate x) :=
      (aligned_has_active_iff R x).2 habs
    have hwaitEq := alignedRaceWait_eq_winner
      R x hres winner hwinnerStrict
    have hwinnerRate := aligned_channel_rate_pos R x winner
    have hwinnerTermFinite :
        activeRaceTermE σ (rate x) c
          (R.embedding.channel x winner) ≠ ∞ := by
      simp only [activeRaceTermE, if_pos hwinnerRate]
      exact ENNReal.div_ne_top (hres _)
        (by exact_mod_cast hwinnerRate.ne')
    have hwaitFinite :
        activeRaceWaitE σ (rate x) c ≠ ∞ := by
      rw [hwaitEq]
      exact hwinnerTermFinite
    have hwinnerThreshold :
        extendedResidualWaitE σ c (R.embedding.channel x winner) ≤
          (rate x (R.embedding.channel x winner) : ℝ≥0∞) *
            activeRaceWaitE σ (rate x) c := by
      have hdiv :
          extendedResidualWaitE σ c (R.embedding.channel x winner) /
              (rate x
                (R.embedding.channel x winner) : ℝ≥0∞) ≤
            activeRaceWaitE σ (rate x) c := by
        rw [hwaitEq]
        simp only [activeRaceTermE, if_pos hwinnerRate, le_refl]
      exact (ENNReal.div_le_iff
        (by exact_mod_cast hwinnerRate.ne') ENNReal.coe_ne_top).1 hdiv
        |>.trans_eq (by rw [mul_comm])
    have hwinnerInc :
        0 < lineIncrement σ
          (activeNextInternal σ (rate x))
          (R.embedding.channel x winner) c :=
      (activeLineIncrement_pos_iff
        (hline _) hwaitFinite hwinnerRate).2 hwinnerThreshold
    have hother : ∀ l,
        l ≠ R.embedding.channel x winner →
        ¬ 0 < lineIncrement σ
          (activeNextInternal σ (rate x)) l c := by
      intro l hne
      by_cases hl : 0 < rate x l
      · obtain ⟨other, hotherChannel⟩ := R.complete x l hl
        have hotherNe : other ≠ winner := by
          intro heq
          subst other
          exact hne hotherChannel.symm
        intro hinc
        have hthreshold :=
          (activeLineIncrement_pos_iff (hline l) hwaitFinite hl).1 hinc
        have hdiv :
            activeRaceTermE σ (rate x) c l ≤
              activeRaceWaitE σ (rate x) c := by
          simp only [activeRaceTermE, if_pos hl]
          exact (ENNReal.div_le_iff
            (by exact_mod_cast hl.ne') ENNReal.coe_ne_top).2
            (by simpa [mul_comm] using hthreshold)
        rw [← hotherChannel, hwaitEq] at hdiv
        have hotherRate := aligned_channel_rate_pos R x other
        have hotherFinite :
            activeRaceTermE σ (rate x) c
              (R.embedding.channel x other) ≠ ∞ := by
          simp only [activeRaceTermE, if_pos hotherRate]
          exact ENNReal.div_ne_top (hres _)
            (by exact_mod_cast hotherRate.ne')
        have hreal :=
          (ENNReal.toReal_le_toReal hotherFinite hwinnerTermFinite).mpr hdiv
        rw [activeRaceTerm_toReal hotherRate,
          activeRaceTerm_toReal hwinnerRate,
          R.rate_coe x other,
          R.rate_coe x winner] at hreal
        have hstrict := hwinnerStrict other hotherNe
        simp [cellStateClocks, RegenerativeRace.targetRate] at hstrict
        linarith
      · have hz : rate x l = 0 :=
          le_antisymm (not_lt.mp hl) zero_le
        intro hinc
        have heq :
            activeNextInternal σ (rate x) c l = σ c l := by
          simp [activeNextInternal, hz]
        simp [lineIncrement, extendedPathAt, finitePart, heq] at hinc
    have hobsWinner :
        observableWinner σ
          (stateActiveNextInternal σ state (rate)) c =
            R.embedding.channel x winner := by
      unfold observableWinner
      have hcongr :
          (fun l => lineIncrement σ
            (stateActiveNextInternal σ state (rate)) l c) =
          (fun l => lineIncrement σ
            (activeNextInternal σ (rate (state c))) l c) := by
        funext l
        unfold lineIncrement extendedPathAt finitePart
        rw [stateActiveNextInternal_eq_fixed]
      rw [hcongr]
      exact firstPositiveChannel_eq_of_unique _ _ hwinnerInc hother
    have hholding :
        observableActiveHoldingTime σ
          (stateActiveNextInternal σ state (rate))
          state (rate) c =
        (activeRaceWaitE σ (rate x) c).toReal := by
      rw [observableActiveHoldingTime_eq_of_active
        σ _ state (rate) c hactive, hobsWinner,
        stateActiveNextInternal_eq_fixed]
      simp only [activeNextInternal]
      have hcancel :
          ((rate x (R.embedding.channel x winner) : ℝ≥0∞) *
              activeRaceWaitE σ (rate x) c) /
            (rate x (R.embedding.channel x winner) : ℝ≥0∞) =
          activeRaceWaitE σ (rate x) c := by
        rw [div_eq_mul_inv, mul_comm
          (rate x (R.embedding.channel x winner) : ℝ≥0∞)
          (activeRaceWaitE σ (rate x) c), mul_assoc,
          ENNReal.mul_inv_cancel (by exact_mod_cast hwinnerRate.ne')
            ENNReal.coe_ne_top, mul_one]
      rw [ENNReal.add_sub_cancel_left (hline _), hcancel]
    have hstep := R.step_eq x winner
    rw [cellRaceStep_eq_of_nonabsorbing Q R.embedding habs]
    unfold liveCellRaceStep
    letI : Nonempty (RegenerativeRace.ActiveTarget Q x) :=
      RegenerativeRace.activeTarget_nonempty Q habs
    have hraceWinner := raceWinner_eq_of_strict
      (RegenerativeRace.targetRate Q x) winner
      (cellStateClocks R.embedding x
        (extendedStoppingResidual σ c)) hwinnerStrict
    rw [activeNextRecordValue, if_pos hactive]
    rw [hobsWinner, hholding, hstep]
    simp only [racePair, raceWait, hraceWinner]
    rw [hwaitEq, activeRaceTerm_toReal hwinnerRate,
      R.rate_coe x winner]
    simp only [cellStateClocks, RegenerativeRace.targetRate]

/-- The recursive observable successor agrees almost surely with the canonical
active-target row. -/
theorem alignedNextRecord_eq_cellRaceStep_ae
    (x0 : S)
    (hfiltration : ExtendedCellRecordFiltrationRealization
      (recursiveRecord x0 rate step)
      (recursiveInternal x0 rate step))
    (k : ℕ) :
    ∀ᵐ c ∂cellFamilyLaw ι,
      recursiveRecord x0 rate step c (k + 1) =
        cellRaceStep Q R.embedding
          (recursiveRecord x0 rate step c k).2
          (extendedStoppingResidual
            (recursiveInternal x0 rate step k) c) := by
  let H := hfiltration.freshResidualsAt
    (fun _ => (0, x0)) k
  have hres := residualWaitE_finite_ae H
  have hgood := currentStateStrictWinner_ae R H
  have hline := hfiltration.finite k
  filter_upwards [hline, hres, hgood] with c hc hrc hgc
  have hrec := recursiveRecord_succ
    (x0 := x0) (rate := rate) (step := step) c k
  rw [hrec, recursiveInternal_succ]
  exact alignedNextRecord_eq_cellRaceStep R
    (fun z => (recursiveRecord x0 rate step z k).2) c hc hrc hgc

/-- The zero-aware recursion for any scale-free active race data. -/
theorem recursionOfActiveRaceData
    (x0 : S) (hrate : Measurable rate)
    (hstep : Measurable (Function.uncurry step)) :
    ZeroAwareCellRecordRecursion Q x0
      (recursiveRecord x0 rate step)
      (recursiveInternal x0 rate step)
      R.embedding := by
  let hfiltration := recursiveFiltrationRealization
    x0 rate step hrate hstep
  refine
    { filtration := hfiltration
      initial := ?_
      step := ?_ }
  · rw [Measure.map_map
      (measurable_frestrictLe
        (X := fun _ : ℕ => ℝ × S) 0)
      hfiltration.measurable_record]
    have hconst :
        (frestrictLe
          (π := fun _ : ℕ => ℝ × S) 0) ∘
            recursiveRecord x0 rate step =
          fun _ => (MeasurableEquiv.piUnique
            (fun _ : Finset.Iic 0 => ℝ × S)).symm (0, x0) := by
      funext c i
      rcases i with ⟨i, hi⟩
      have hizero : i = 0 :=
        Nat.le_zero.mp (Finset.mem_Iic.mp hi)
      subst i
      rfl
    rw [hconst]
    simp
  · intro k
    exact alignedNextRecord_eq_cellRaceStep_ae R x0 hfiltration k

end Generic

/-! ## The per-scale density alignment supplies the data -/

section PerScale

variable {d : ℕ} {ι : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable {Gamma : RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ}
variable {n : ℕ} {hn : 0 < n}

/-- The three facts about the embedding, derived from the four fields of the
per-scale kernel-ready record. -/
noncomputable def activeRaceDataOf
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    ActiveRaceData (DensityDepCTMC.mk n hn Gamma).toQMatrix
      A.latticeRate A.latticeStep where
  embedding := (CellPerScaleDensityAlignment.kernelReady A).embedding
  rate_coe := by
    intro x a
    let K := CellPerScaleDensityAlignment.kernelReady A
    have hp := RegenerativeRace.targetRate_pos
      (DensityDepCTMC.mk n hn Gamma).toQMatrix x a
    have hd : 0 < A.densityRate x (K.embedding.channel x a) := by
      rw [← K.rate_eq x a]
      exact hp
    change (Real.toNNReal
      (A.densityRate x (K.embedding.channel x a)) : ℝ) = _
    rw [Real.coe_toNNReal _ hd.le]
    exact (K.rate_eq x a).symm
  step_eq := by
    intro x a
    let K := CellPerScaleDensityAlignment.kernelReady A
    have hp : 0 < A.latticeRate x (K.embedding.channel x a) := by
      apply (NNReal.coe_pos).mp
      have hd : 0 < A.densityRate x (K.embedding.channel x a) := by
        rw [← K.rate_eq x a]
        exact RegenerativeRace.targetRate_pos
          (DensityDepCTMC.mk n hn Gamma).toQMatrix x a
      change 0 < (Real.toNNReal
        (A.densityRate x (K.embedding.channel x a)) : ℝ)
      rw [Real.coe_toNNReal _ hd.le]
      exact hd
    have hs := A.latticeStep_spec_of_positive x
      (K.embedding.channel x a) hp
    funext i
    apply Fin.ext
    have hi := hs i
    have hj := K.jump_eq x a i
    have hz :
        (A.latticeStep x (K.embedding.channel x a) i : ℤ) =
          (a.1 i : ℤ) := by
      linarith
    exact_mod_cast hz
  complete := (CellPerScaleDensityAlignment.kernelReady A).complete

/-- **The per-scale recursion.**  For a single-scale alignment, the concrete
zero-aware recursion started at the scale's own lattice start. -/
noncomputable def perScaleRecursion
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    ZeroAwareCellRecordRecursion
      (DensityDepCTMC.mk n hn Gamma).toQMatrix A.latticeStart
      (recursiveRecord A.latticeStart A.latticeRate A.latticeStep)
      (recursiveInternal A.latticeStart A.latticeRate A.latticeStep)
      (CellPerScaleDensityAlignment.kernelReady A).embedding :=
  recursionOfActiveRaceData (activeRaceDataOf A) A.latticeStart
    (measurable_of_countable _) (measurable_of_countable _)

variable {b : ι → ℝ}
variable {hbetaZero : ∀ l y, 0 ≤ beta l y}
variable {hbetaBound : ∀ l y, beta l y ≤ b l}
variable {hbetaMeasurable : ∀ l, Measurable (beta l)}

/-- A per-scale cell system from the coupling alone. -/
noncomputable def systemOfCoupling
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (coupling :
      AlignedCellCoupling (v := v)
        (DensityDepCTMC.mk n hn Gamma) A.latticeStart
        hbetaZero hbetaBound hbetaMeasurable A.xStart) :
    PerScaleDensityCellSystem
      (b := b) (hbetaZero := hbetaZero)
      (hbetaBound := hbetaBound)
      (hbetaMeasurable := hbetaMeasurable) A :=
  { recursion := perScaleRecursion A
    coupling := coupling }

end PerScale

/-!
THEOREM LIST
* `ActiveRaceData`
* `recursionOfActiveRaceData`
* `activeRaceDataOf`
* `perScaleRecursion`
* `systemOfCoupling`
END
-/

end Ripple.Kurtz.StrongApprox.CellPerScaleRecordRecursion

end

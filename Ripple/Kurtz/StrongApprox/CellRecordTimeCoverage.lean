-- Ripple/Kurtz/StrongApprox/CellRecordTimeCoverage.lean
import Ripple.Kurtz.StrongApprox.CellRecordRaceRegularAE
import Ripple.Kurtz.StrongApprox.SIPDensityCellRecordFromClockProducer

/-!
# Physical-time coverage of the recursive record, and the alignment-only SIP theorem

For a simple, race-regular cell family the record starts either pass any
horizon `t` (then `t` lies in a half-open record interval), or stay below `t`
forever.  In the latter case the chain must absorb at a finite record: every
active record consumes exactly one cell point, while the points available up
to horizon `t` are finite because the internal line of channel `l` is at most
`(sum over states of the lattice rate of l) * (record start time)`.
After the first inactive record the readout is frozen.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellRecordTimeCoverage

open MeasureTheory ProbabilityTheory Set Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open Ripple.Kurtz
open CellFamilySimplePoints
open CellPerScaleDensityAlignment
open CellPerScaleRecordPathAE
open CellRecursiveClockEquationProducer
open CellExtendedStoppingLine
open CellExtendedRandomTime
open CellExtendedRaceRecursion
open CellExtendedRecordSequence
open CellZeroAwareExtendedRace
open CellZeroAwareRecordSequence
open CellPerScaleRecordRecursion
open CellSimpleFirstArrival
open CellRecursiveClockLedger
open CellRecordRaceRegularAE

variable {d : ℕ} {ι : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable {Gamma : RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ}
variable {n : ℕ} {hn : 0 < n}

private abbrev DensityState (d n : ℕ) :=
  Fin d → Fin (n + 1)

private abbrev DensityModel
    (Gamma : RateSpec d) (n : ℕ) (hn : 0 < n) :=
  DensityDepCTMC.mk n hn Gamma

private theorem firstPositiveChannel_eq_of_unique
    (z : ι → ℕ) (winner : ι)
    (hpositive : 0 < z winner)
    (hother : ∀ l, l ≠ winner → z l = 0) :
    firstPositiveChannel z = winner := by
  classical
  unfold firstPositiveChannel
  rw [dif_pos ⟨winner, hpositive⟩]
  let chosen := Classical.choose
    (show ∃ l, 0 < z l from ⟨winner, hpositive⟩)
  have hchosen : 0 < z chosen :=
    Classical.choose_spec
      (show ∃ l, 0 < z l from ⟨winner, hpositive⟩)
  by_contra hne
  rw [hother chosen hne] at hchosen
  exact (lt_irrefl 0 hchosen)

/-- The recursive successor line, evaluated at the current cell sample, is the
fixed-rate active successor for the current record state. -/
private theorem internalMap_succ_apply
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ) :
    internalMap A (k + 1) c =
      activeNextInternal (internalMap A k) (recordRate A c k) c := by
  change stateActiveNextInternal
      (internalMap A k)
      (fun z => (recordMap A z k).2) A.latticeRate c =
    activeNextInternal (internalMap A k)
      (A.latticeRate (recordMap A c k).2) c
  rfl

/-- Complete deterministic active-record receipt on the corrected regular
simple event.  The winning line increment is one, all other increments are
zero, and the stored record uses that winner and the common race wait. -/
private theorem activeRecordStep_of_simple
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    {c : CellFamily ι}
    (hsimple : SimpleCellFamily c)
    (hregular : RecordRaceRegular A c)
    (k : ℕ)
    (hactive : HasActiveRate (recordRate A c k)) :
    ∃ winner : ι,
      0 < recordRate A c k winner ∧
      recordWait A c k ≠ ∞ ∧
      lineIncrement (internalMap A k) (internalMap A (k + 1))
          winner c = 1 ∧
      (∀ l, l ≠ winner →
        lineIncrement (internalMap A k) (internalMap A (k + 1))
          l c = 0) ∧
      recordMap A c (k + 1) =
        ((recordWait A c k).toReal,
          A.latticeStep (recordMap A c k).2 winner) := by
  obtain ⟨winner, hwinnerRate, hwinner, hstrict⟩ :=
    hregular.active_strict k hactive
  have hwait : recordWait A c k ≠ ∞ := by
    rw [hwinner]
    simp only [activeRaceTermE, if_pos hwinnerRate]
    exact ENNReal.div_ne_top
      (hregular.residual_finite k winner)
      (by exact_mod_cast hwinnerRate.ne')
  have hwinnerFixed :
      lineIncrement (internalMap A k)
          (activeNextInternal (internalMap A k) (recordRate A c k))
          winner c = 1 :=
    activeLineIncrement_eq_one_of_simple
      (hsimple winner)
      (hregular.line_finite k winner)
      (hregular.residual_finite k winner)
      hwait hwinnerRate hwinner
  have hotherFixed : ∀ l, l ≠ winner →
      lineIncrement (internalMap A k)
          (activeNextInternal (internalMap A k) (recordRate A c k))
          l c = 0 := by
    intro l hne
    by_cases hl : 0 < recordRate A c k l
    · apply Nat.eq_zero_of_not_pos
      intro hinc
      have hthreshold :=
        (activeLineIncrement_pos_iff
          (hregular.line_finite k l) hwait hl).1 hinc
      have hdiv :
          activeRaceTermE (internalMap A k)
              (recordRate A c k) c l ≤ recordWait A c k := by
        simp only [activeRaceTermE, if_pos hl]
        exact (ENNReal.div_le_iff
          (by exact_mod_cast hl.ne') ENNReal.coe_ne_top).2
            (by simpa [mul_comm] using hthreshold)
      exact (not_le_of_gt (hstrict l hne)) hdiv
    · have hz : recordRate A c k l = 0 :=
        le_antisymm (not_lt.mp hl) zero_le
      have heq :
          activeNextInternal (internalMap A k)
              (recordRate A c k) c l = internalMap A k c l := by
        simp [activeNextInternal, hz]
      simp [lineIncrement, extendedPathAt, finitePart, heq]
  have hnext := internalMap_succ_apply A c k
  have hwinnerNext :
      lineIncrement (internalMap A k) (internalMap A (k + 1))
          winner c = 1 := by
    unfold lineIncrement extendedPathAt finitePart at hwinnerFixed ⊢
    rw [hnext]
    exact hwinnerFixed
  have hotherNext : ∀ l, l ≠ winner →
      lineIncrement (internalMap A k) (internalMap A (k + 1))
          l c = 0 := by
    intro l hne
    unfold lineIncrement extendedPathAt finitePart at hotherFixed ⊢
    rw [hnext]
    exact hotherFixed l hne
  have hobservable :
      observableWinner (internalMap A k) (internalMap A (k + 1)) c =
        winner := by
    unfold observableWinner
    exact firstPositiveChannel_eq_of_unique _ winner
      (by rw [hwinnerNext]; simp)
      (fun l hne => hotherNext l hne)
  have hholding :
      observableActiveHoldingTime
          (internalMap A k) (internalMap A (k + 1))
          (fun z => (recordMap A z k).2) A.latticeRate c =
        (recordWait A c k).toReal := by
    rw [observableActiveHoldingTime_eq_of_active
      (internalMap A k) (internalMap A (k + 1))
      (fun z => (recordMap A z k).2) A.latticeRate c hactive,
      hobservable]
    change (((internalMap A (k + 1) c winner -
        internalMap A k c winner) /
          (recordRate A c k winner : ℝ≥0∞)).toReal =
        (recordWait A c k).toReal)
    have hcoord :
        internalMap A (k + 1) c winner =
          internalMap A k c winner +
            (recordRate A c k winner : ℝ≥0∞) *
              recordWait A c k := by
      rw [hnext]
      rfl
    have hcancel :
        ((recordRate A c k winner : ℝ≥0∞) * recordWait A c k) /
            (recordRate A c k winner : ℝ≥0∞) =
          recordWait A c k := by
      rw [div_eq_mul_inv,
        mul_comm (recordRate A c k winner : ℝ≥0∞)
          (recordWait A c k), mul_assoc,
        ENNReal.mul_inv_cancel
          (by exact_mod_cast hwinnerRate.ne') ENNReal.coe_ne_top,
        mul_one]
    rw [hcoord,
      ENNReal.add_sub_cancel_left (hregular.line_finite k winner),
      hcancel]
  have hrecord :
      recordMap A c (k + 1) =
        ((recordWait A c k).toReal,
          A.latticeStep (recordMap A c k).2 winner) := by
    change activeNextRecordValue
        (internalMap A k) (internalMap A (k + 1))
        (fun z => (recordMap A z k).2)
        A.latticeRate A.latticeStep c = _
    have hactive' :
        HasActiveRate (A.latticeRate (recordMap A c k).2) := hactive
    rw [activeNextRecordValue, if_pos hactive', hholding, hobservable]
  exact ⟨winner, hwinnerRate, hwait, hwinnerNext,
    hotherNext, hrecord⟩

private theorem recordRate_intervalIntegrable
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (l : ι) (a b : ℝ) :
    IntervalIntegrable
      (fun s => beta l (recordRealPath A c s)) volume a b := by
  refine ⟨?_, ?_⟩
  · have h :=
      (DensityModel Gamma n hn).integrableOn_comp_frozenStateAt
        (recordMap A c)
        (fun z => beta l ((DensityModel Gamma n hn).scaledState z)) a b
    simpa [recordRealPath] using h.mono_set Ioc_subset_Icc_self
  · have h :=
      (DensityModel Gamma n hn).integrableOn_comp_frozenStateAt
        (recordMap A c)
        (fun z => beta l ((DensityModel Gamma n hn).scaledState z)) b a
    simpa [recordRealPath] using h.mono_set Ioc_subset_Icc_self


/-- Inactive record: the next record repeats the state with holding time zero
and the internal line does not move. -/
theorem record_succ_of_inactive
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ)
    (h : ¬ HasActiveRate (recordRate A c k)) :
    recordMap A c (k + 1) = (0, (recordMap A c k).2) ∧
      internalMap A (k + 1) c = internalMap A k c := by
  have hactive' : ¬ HasActiveRate (A.latticeRate (recordMap A c k).2) := h
  constructor
  · change activeNextRecordValue
        (internalMap A k) (internalMap A (k + 1))
        (fun z => (recordMap A z k).2)
        A.latticeRate A.latticeStep c = _
    rw [activeNextRecordValue, if_neg hactive']
  · rw [internalMap_succ_apply A c k,
      activeNextInternal_eq_self_of_no_active
        (internalMap A k) (recordRate A c k) h]

/-- After an inactive record the state and the start time never change. -/
theorem inactive_persist
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ)
    (h : ¬ HasActiveRate (recordRate A c k)) :
    ∀ m, k ≤ m →
      (recordMap A c m).2 = (recordMap A c k).2 ∧
        recordStartTime A c m = recordStartTime A c k := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ m hm ih =>
    have hin : ¬ HasActiveRate (recordRate A c m) := by
      have : recordRate A c m = recordRate A c k := by
        unfold recordRate
        rw [ih.1]
      rw [this]
      exact h
    obtain ⟨hrec, _⟩ := record_succ_of_inactive A c m hin
    refine ⟨by rw [hrec]; exact ih.1, ?_⟩
    rw [recordStartTime_succ, hrec]
    simpa using ih.2

/-- An active record moves the state. -/
theorem active_state_ne
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    {c : CellFamily ι}
    (hsimple : SimpleCellFamily c)
    (hregular : RecordRaceRegular A c) (k : ℕ)
    (hactive : HasActiveRate (recordRate A c k)) :
    (recordMap A c (k + 1)).2 ≠ (recordMap A c k).2 := by
  obtain ⟨winner, hwinnerRate, _hwait, _h1, _h2, hrecord⟩ :=
    activeRecordStep_of_simple A hsimple hregular k hactive
  rw [hrecord]
  intro heq
  have heq' : A.latticeStep (recordMap A c k).2 winner =
      (recordMap A c k).2 := heq
  have hs := A.latticeStep_spec_of_positive (recordMap A c k).2 winner
    (by simpa [recordRate] using hwinnerRate)
  apply A.jump_ne_zero winner
  funext i
  have hi := hs i
  rw [heq'] at hi
  simpa using hi.symm

/-- The frozen readout after the first inactive record. -/
theorem recordRealPath_frozen_of_first_inactive
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    {c : CellFamily ι}
    (hsimple : SimpleCellFamily c)
    (hregular : RecordRaceRegular A c) (k : ℕ)
    (hk : ¬ HasActiveRate (recordRate A c k))
    (hmin : ∀ j < k, HasActiveRate (recordRate A c j)) :
    ∀ s, recordStartTime A c k ≤ s →
      recordRealPath A c s =
        (DensityModel Gamma n hn).scaledState (recordMap A c k).2 := by
  intro s hs
  let path := (DensityModel Gamma n hn).canonicalPathMap (recordMap A c)
  have hmono : Monotone path.sojournStart := recordStartTime_mono A c
  have hno : ∀ m, ¬ s < path.times m := by
    intro m
    change ¬ s < path.sojournStart (m + 1)
    rcases le_or_gt (m + 1) k with hmk | hmk
    · exact not_lt.mpr ((hmono hmk).trans hs)
    · have h := (inactive_persist A c k hk (m + 1) hmk.le).2
      change ¬ s < recordStartTime A c (m + 1)
      rw [h]
      exact not_lt.mpr hs
  have hseq : ∀ j, path.stateSeq j = (recordMap A c j).2 :=
    fun j => (DensityModel Gamma n hn).canonicalPathMap_stateSeq
      (recordMap A c) j
  have hstable : path.stateSeq k = path.stateSeq (k + 1) := by
    rw [hseq, hseq, (record_succ_of_inactive A c k hk).1]
  have hminS : ∀ j ∈ Finset.range k,
      path.stateSeq j ≠ path.stateSeq (j + 1) := by
    intro j hj
    rw [hseq, hseq]
    exact (active_state_ne A hsimple hregular j
      (hmin j (Finset.mem_range.mp hj))).symm
  have hfrozen : path.frozenStateAt s = path.stateSeq k :=
    path.frozenStateAt_eq_stateSeq_of_first_stable s k hno hstable hminS
  change (DensityModel Gamma n hn).scaledState (path.frozenStateAt s) = _
  rw [hfrozen, hseq]

/-- An active record consumes exactly one cell point in total. -/
theorem sum_count_step
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    {c : CellFamily ι}
    (hsimple : SimpleCellFamily c)
    (hregular : RecordRaceRegular A c) (k : ℕ)
    (hactive : HasActiveRate (recordRate A c k)) :
    ∑ l, extendedPathAt (internalMap A (k + 1)) l c =
      ∑ l, extendedPathAt (internalMap A k) l c + 1 := by
  obtain ⟨winner, _hwinnerRate, _hwait, hincWinner, hincOther, _hrecord⟩ :=
    activeRecordStep_of_simple A hsimple hregular k hactive
  have hnext := internalMap_succ_apply A c k
  have hlineLe (l : ι) :
      internalMap A k c l ≤ internalMap A (k + 1) c l := by
    rw [hnext]
    exact extendedLine_le_activeNextInternal
      (internalMap A k) (recordRate A c k) c l
  have hcountLe (l : ι) :
      extendedPathAt (internalMap A k) l c ≤
        extendedPathAt (internalMap A (k + 1)) l c := by
    unfold extendedPathAt
    apply cellPath_mono
    exact_mod_cast
      (ENNReal.toNNReal_mono
        (hregular.line_finite (k + 1) l) (hlineLe l))
  have hcountStep (l : ι) :
      extendedPathAt (internalMap A (k + 1)) l c =
        extendedPathAt (internalMap A k) l c +
          lineIncrement (internalMap A k)
            (internalMap A (k + 1)) l c := by
    have hm := hcountLe l
    unfold lineIncrement
    omega
  rw [Finset.sum_congr rfl (fun l _ => hcountStep l),
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single winner]
  · exact hincWinner
  · intro l _ hl
    exact hincOther l hl
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The internal line of channel `l` is at most
`(sum of the lattice rates of l over all states)` times the record start. -/
theorem finitePart_le_rate_mul_start
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    {c : CellFamily ι}
    (hsimple : SimpleCellFamily c)
    (hregular : RecordRaceRegular A c) :
    ∀ k l, ((finitePart (internalMap A k) c l : ℝ≥0) : ℝ) ≤
      (∑ x, ((A.latticeRate x l : ℝ≥0) : ℝ)) * recordStartTime A c k := by
  intro k
  induction k with
  | zero =>
    intro l
    simp [internalMap, finitePart, initialInternalLine, recordStartTime]
  | succ k ih =>
    intro l
    by_cases hactive : HasActiveRate (recordRate A c k)
    · obtain ⟨winner, _hwinnerRate, hwait, _h1, _h2, hrecord⟩ :=
        activeRecordStep_of_simple A hsimple hregular k hactive
      have hnext := internalMap_succ_apply A c k
      have hwait' :
          activeRaceWaitE (internalMap A k) (recordRate A c k) c ≠ ∞ :=
        hwait
      have hlineStep :
          ((finitePart (internalMap A (k + 1)) c l : ℝ≥0) : ℝ) =
            ((finitePart (internalMap A k) c l : ℝ≥0) : ℝ) +
              ((recordRate A c k l : ℝ≥0) : ℝ) *
                (recordWait A c k).toReal := by
        change (internalMap A (k + 1) c l).toReal =
          (internalMap A k c l).toReal +
            ((recordRate A c k l : ℝ≥0) : ℝ) *
              (recordWait A c k).toReal
        rw [hnext]
        unfold activeNextInternal
        rw [ENNReal.toReal_add
          (hregular.line_finite k l)
          (ENNReal.mul_ne_top ENNReal.coe_ne_top hwait')]
        simp [recordWait]
      have hstart : recordStartTime A c (k + 1) =
          recordStartTime A c k + (recordWait A c k).toReal := by
        rw [recordStartTime_succ, hrecord]
      have hrate : ((recordRate A c k l : ℝ≥0) : ℝ) ≤
          ∑ x, ((A.latticeRate x l : ℝ≥0) : ℝ) := by
        unfold recordRate
        exact Finset.single_le_sum
          (f := fun x => ((A.latticeRate x l : ℝ≥0) : ℝ))
          (fun x _ => NNReal.coe_nonneg _) (Finset.mem_univ _)
      have hw : 0 ≤ (recordWait A c k).toReal := ENNReal.toReal_nonneg
      rw [hlineStep, hstart]
      have := ih l
      nlinarith [mul_le_mul_of_nonneg_right hrate hw]
    · obtain ⟨hrec, hline⟩ := record_succ_of_inactive A c k hactive
      have hfin : finitePart (internalMap A (k + 1)) c l =
          finitePart (internalMap A k) c l := by
        unfold finitePart
        rw [hline]
      have hstart : recordStartTime A c (k + 1) = recordStartTime A c k := by
        rw [recordStartTime_succ, hrec]
        simp
      rw [hfin, hstart]
      exact ih l

/-- Zeno exclusion: if all record starts stay below `t`, some record is
inactive. -/
theorem exists_inactive_of_bounded
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    {c : CellFamily ι}
    (hsimple : SimpleCellFamily c)
    (hregular : RecordRaceRegular A c) (t : ℝ)
    (ht : ∀ k, recordStartTime A c k ≤ t) :
    ∃ k, ¬ HasActiveRate (recordRate A c k) := by
  by_contra hall
  push_neg at hall
  have hcount : ∀ k, ∑ l, extendedPathAt (internalMap A k) l c = k := by
    intro k
    induction k with
    | zero =>
      simp [extendedPathAt, finitePart, internalMap, initialInternalLine,
        cellPath_zero]
    | succ k ih =>
      rw [sum_count_step A hsimple hregular k (hall k), ih]
  let B : ℕ := ∑ l, cellPath
    ((∑ x, ((A.latticeRate x l : ℝ≥0) : ℝ)) * t) (c l)
  have hle : ∀ k, ∑ l, extendedPathAt (internalMap A k) l c ≤ B := by
    intro k
    apply Finset.sum_le_sum
    intro l _
    unfold extendedPathAt
    apply cellPath_mono
    calc
      ((finitePart (internalMap A k) c l : ℝ≥0) : ℝ) ≤
          (∑ x, ((A.latticeRate x l : ℝ≥0) : ℝ)) *
            recordStartTime A c k :=
        finitePart_le_rate_mul_start A hsimple hregular k l
      _ ≤ (∑ x, ((A.latticeRate x l : ℝ≥0) : ℝ)) * t :=
        mul_le_mul_of_nonneg_left (ht k)
          (Finset.sum_nonneg (fun x _ => NNReal.coe_nonneg _))
  have h := hle (B + 1)
  rw [hcount] at h
  omega

/-- The integrated clock is linear on a segment on which the readout is
constant. -/
theorem clock_const_segment
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ) (l : ι) (t : ℝ)
    (hkt : recordStartTime A c k ≤ t)
    (hconst : ∀ s, recordStartTime A c k ≤ s → s ≤ t →
      recordRealPath A c s =
        (DensityModel Gamma n hn).scaledState (recordMap A c k).2) :
    clock beta (recordRealPath A c) l t =
      clock beta (recordRealPath A c) l (recordStartTime A c k) +
        (t - recordStartTime A c k) *
          beta l ((DensityModel Gamma n hn).scaledState
            (recordMap A c k).2) := by
  have hpiece :
      ∫ s in recordStartTime A c k..t,
          beta l (recordRealPath A c s) =
        (t - recordStartTime A c k) *
          beta l ((DensityModel Gamma n hn).scaledState
            (recordMap A c k).2) := by
    calc
      ∫ s in recordStartTime A c k..t, beta l (recordRealPath A c s) =
        ∫ _s in recordStartTime A c k..t,
          beta l ((DensityModel Gamma n hn).scaledState
            (recordMap A c k).2) := by
              refine intervalIntegral.integral_congr ?_
              intro s hs
              rw [Set.uIcc_of_le hkt] at hs
              simp only
              rw [hconst s hs.1 hs.2]
      _ = _ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
  unfold clock
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (recordRate_intervalIntegrable A c l 0 (recordStartTime A c k))
      (recordRate_intervalIntegrable A c l (recordStartTime A c k) t),
    hpiece]

/-- Driver counts on a segment where the readout is constant and the clock has
not reached the next residual of any active channel. -/
theorem driver_count_of_const
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (c : CellFamily ι) (k : ℕ) (hledger : RecordLedgerAt A c k) (t : ℝ)
    (hkt : recordStartTime A c k ≤ t)
    (hconst : ∀ s, recordStartTime A c k ≤ s → s ≤ t →
      recordRealPath A c s =
        (DensityModel Gamma n hn).scaledState (recordMap A c k).2)
    (hfin : ∀ l, extendedResidualWaitE (internalMap A k) c l ≠ ∞)
    (hq : ∀ l, 0 < recordRate A c k l →
      (t - recordStartTime A c k) * ((recordRate A c k l : ℝ≥0) : ℝ) <
        (extendedResidualWaitE (internalMap A k) c l).toReal) :
    ∀ l, cellPath
        ((n : ℝ) * clock beta (recordRealPath A c) l t) (c l) =
      extendedPathAt (internalMap A k) l c := by
  intro l
  have hclock := clock_const_segment A c k l t hkt hconst
  have hnonneg : 0 ≤ A.densityRate (recordMap A c k).2 l := by
    unfold PerScaleDensityChannelAlignment.densityRate
    exact mul_nonneg (Nat.cast_nonneg _) (hbetaZero l _)
  have hrate : ((recordRate A c k l : ℝ≥0) : ℝ) =
      (n : ℝ) * beta l ((DensityModel Gamma n hn).scaledState
        (recordMap A c k).2) := by
    unfold recordRate
    change (Real.toNNReal (A.densityRate (recordMap A c k).2 l) : ℝ) = _
    rw [Real.coe_toNNReal _ hnonneg]
    rfl
  have hn' : (n : ℝ) * clock beta (recordRealPath A c) l t =
      ((finitePart (internalMap A k) c l : ℝ≥0) : ℝ) +
        (t - recordStartTime A c k) *
          ((recordRate A c k l : ℝ≥0) : ℝ) := by
    rw [hclock, mul_add, ← hledger.internal_clock l, hrate]
    ring
  rw [hn']
  by_cases hpos : 0 < recordRate A c k l
  · have hq0 : 0 ≤ (t - recordStartTime A c k) *
        ((recordRate A c k l : ℝ≥0) : ℝ) :=
      mul_nonneg (sub_nonneg.2 hkt) (NNReal.coe_nonneg _)
    have hzero : CellRandomTimeEvaluation.shiftedCount (finitePart (internalMap A k)) c l
        (Real.toNNReal ((t - recordStartTime A c k) *
          ((recordRate A c k l : ℝ≥0) : ℝ))) = 0 := by
      by_contra hne
      have hpos' := Nat.pos_of_ne_zero hne
      have hle := (residualWaitE_le_coe_iff_shiftedCount_pos
        (finitePart (internalMap A k)) c l _).2 hpos'
      have hlt : ((Real.toNNReal ((t - recordStartTime A c k) *
            ((recordRate A c k l : ℝ≥0) : ℝ)) : ℝ≥0) : ℝ≥0∞) <
          extendedResidualWaitE (internalMap A k) c l := by
        rw [← ENNReal.coe_toNNReal (hfin l)]
        apply ENNReal.coe_lt_coe.2
        apply NNReal.coe_lt_coe.1
        rw [Real.coe_toNNReal _ hq0, ENNReal.coe_toNNReal_eq_toReal]
        exact hq l hpos
      exact absurd hle (not_le.2 hlt)
    unfold CellRandomTimeEvaluation.shiftedCount at hzero
    rw [Real.coe_toNNReal _ hq0] at hzero
    have hm : cellPath ((finitePart (internalMap A k) c l : ℝ≥0) : ℝ)
          (c l) ≤
        cellPath ((finitePart (internalMap A k) c l : ℝ≥0) +
          (t - recordStartTime A c k) *
            ((recordRate A c k l : ℝ≥0) : ℝ)) (c l) :=
      cellPath_mono (by linarith) (c l)
    unfold extendedPathAt
    omega
  · have hz : recordRate A c k l = 0 :=
      le_antisymm (not_lt.1 hpos) zero_le
    rw [hz]
    simp [extendedPathAt]

/-- On an active record the clock room before every active channel's next
residual: `(t - start_k) * rate_l < residual_l`. -/
theorem active_room
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    {c : CellFamily ι}
    (hsimple : SimpleCellFamily c)
    (hregular : RecordRaceRegular A c) (k : ℕ)
    (hactive : HasActiveRate (recordRate A c k)) (t : ℝ)
    (hge : recordStartTime A c k ≤ t)
    (hlt : t < recordStartTime A c (k + 1)) (l : ι)
    (hl : 0 < recordRate A c k l) :
    (t - recordStartTime A c k) * ((recordRate A c k l : ℝ≥0) : ℝ) <
      (extendedResidualWaitE (internalMap A k) c l).toReal := by
  obtain ⟨winner, hwinnerRate, hwait, _h1, _h2, hrecord⟩ :=
    activeRecordStep_of_simple A hsimple hregular k hactive
  obtain ⟨w, hwrate, hwEq, hwStrict⟩ := hregular.active_strict k hactive
  have hstart : recordStartTime A c (k + 1) =
      recordStartTime A c k + (recordWait A c k).toReal := by
    rw [recordStartTime_succ, hrecord]
  have hwle : recordWait A c k ≤
      activeRaceTermE (internalMap A k) (recordRate A c k) c l := by
    by_cases hlw : l = w
    · subst hlw
      exact hwEq.le
    · exact (hwStrict l hlw).le
  have hterm : activeRaceTermE (internalMap A k) (recordRate A c k) c l =
      extendedResidualWaitE (internalMap A k) c l /
        (recordRate A c k l : ℝ≥0∞) := by
    simp [activeRaceTermE, hl]
  rw [hterm] at hwle
  have hmul : recordWait A c k * (recordRate A c k l : ℝ≥0∞) ≤
      extendedResidualWaitE (internalMap A k) c l :=
    (ENNReal.le_div_iff_mul_le
      (.inl (by exact_mod_cast hl.ne')) (.inl ENNReal.coe_ne_top)).1 hwle
  have hreal : (recordWait A c k).toReal *
      ((recordRate A c k l : ℝ≥0) : ℝ) ≤
      (extendedResidualWaitE (internalMap A k) c l).toReal := by
    have := ENNReal.toReal_mono (hregular.residual_finite k l) hmul
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
  have hlt' : t - recordStartTime A c k < (recordWait A c k).toReal := by
    linarith
  have hratePos : (0 : ℝ) < ((recordRate A c k l : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.2 hl
  calc
    (t - recordStartTime A c k) * ((recordRate A c k l : ℝ≥0) : ℝ) <
        (recordWait A c k).toReal * ((recordRate A c k l : ℝ≥0) : ℝ) :=
      mul_lt_mul_of_pos_right hlt' hratePos
    _ ≤ _ := hreal

/-- **Coverage.**  Every nonnegative physical time lies in a record segment. -/
theorem recordSegment_exists
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    {c : CellFamily ι}
    (hsimple : SimpleCellFamily c)
    (hregular : RecordRaceRegular A c)
    (hledger : ∀ k, RecordLedgerAt A c k)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ k, RecordSegmentAt A c t k := by
  classical
  by_cases hcross : ∃ m, t < recordStartTime A c m
  · have hm0pos : Nat.find hcross ≠ 0 := by
      intro h
      have hspec := Nat.find_spec hcross
      rw [h] at hspec
      have h0 : recordStartTime A c 0 = 0 := rfl
      rw [h0] at hspec
      linarith
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0pos
    have hlt : t < recordStartTime A c (k + 1) := by
      have hspec := Nat.find_spec hcross
      rw [hk] at hspec
      exact hspec
    have hge : recordStartTime A c k ≤ t :=
      not_lt.mp (Nat.find_min hcross (by omega : k < Nat.find hcross))
    have hactive : HasActiveRate (recordRate A c k) := by
      by_contra hin
      have h := (inactive_persist A c k hin (k + 1) (Nat.le_succ k)).2
      rw [h] at hlt
      exact absurd hge (not_le.2 hlt)
    refine ⟨k, hge, Or.inl hlt,
      recordRealPath_eq_scaledState_of_interval A c k hge hlt, ?_⟩
    apply driver_count_of_const A hbetaZero c k (hledger k) t hge
    · intro s hs1 hs2
      exact recordRealPath_eq_scaledState_of_interval A c k hs1
        (lt_of_le_of_lt hs2 hlt)
    · exact hregular.residual_finite k
    · intro l hl
      exact active_room A hsimple hregular k hactive t hge hlt l hl
  · push_neg at hcross
    obtain ⟨k0, hk0⟩ :=
      exists_inactive_of_bounded A hsimple hregular t hcross
    have hex : ∃ k, ¬ HasActiveRate (recordRate A c k) := ⟨k0, hk0⟩
    have hk : ¬ HasActiveRate (recordRate A c (Nat.find hex)) :=
      Nat.find_spec hex
    have hmin : ∀ j < Nat.find hex, HasActiveRate (recordRate A c j) := by
      intro j hj
      by_contra hin
      exact Nat.find_min hex hj hin
    have hfrozen := recordRealPath_frozen_of_first_inactive A hsimple
      hregular (Nat.find hex) hk hmin
    have habs : (DensityModel Gamma n hn).toQMatrix.IsAbsorbing
        (recordMap A c (Nat.find hex)).2 := by
      by_contra hna
      exact hk ((aligned_has_active_iff (activeRaceDataOf A) _).2 hna)
    refine ⟨Nat.find hex, hcross _, Or.inr habs,
      hfrozen t (hcross _), ?_⟩
    apply driver_count_of_const A hbetaZero c (Nat.find hex)
      (hledger _) t (hcross _)
    · intro s hs1 _
      exact hfrozen s hs1
    · exact hregular.residual_finite _
    · intro l hl
      exact absurd ⟨l, hl⟩ hk

/-! ## Assembly -/

/-- The deterministic bridge on regular simple cell families. -/
structure RegularRecordClockProducer
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) : Prop where
  bridge_on_regular : ∀ c, SimpleCellFamily c → RecordRaceRegular A c →
    RecordClockBridge A c

/-- The regular producer is constructed from the alignment. -/
theorem regularRecordClockProducerOfAlignment
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (hbetaZero : ∀ l y, 0 ≤ beta l y) :
    RegularRecordClockProducer A where
  bridge_on_regular := fun c hsimple hregular =>
    { initial := recordRealPath_zero A c hsimple hregular
      ledger := recordLedgerAt_of_simple A hbetaZero c hsimple hregular
      locate := fun t ht =>
        recordSegment_exists A hbetaZero hsimple hregular
          (recordLedgerAt_of_simple A hbetaZero c hsimple hregular) t ht }

theorem recordClockBridgeAE_of_alignment
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (hbetaZero : ∀ l y, 0 ≤ beta l y) :
    RecordClockBridgeAE A := by
  filter_upwards [simpleCellFamily_ae (ι := ι), recordRaceRegular_ae A]
    with c hsimple hregular
  exact (regularRecordClockProducerOfAlignment A hbetaZero).bridge_on_regular
    c hsimple hregular

/-- **The recursive clock equation holds almost surely, from the alignment
alone.** -/
theorem recursiveClockEquationAE_of_alignment
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (hbetaZero : ∀ l y, 0 ≤ beta l y) :
    RecursiveClockEquationAE A :=
  recursiveClockEquationAE_of_recordClockBridgeAE A
    (recordClockBridgeAE_of_alignment A hbetaZero)

/-- The same-driver certificate is derived from the alignment. -/
theorem sameDriverCertificate_of_alignment
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (hbetaZero : ∀ l y, 0 ≤ beta l y) :
    SameDriverCertificate A :=
  ⟨recursiveClockEquationAE_of_alignment A hbetaZero⟩


/-! ## The per-scale-start SIP theorem from alignments alone -/

section SIP

open SIPDensityCellRecordPerScaleAE

variable {Omega : Type*} [MeasurableSpace Omega]
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {N : ℕ → Omega → ℕ}
variable {b : ι → ℝ}

/-- The same-driver certificate family built from alignments; every `sameDriver` field is
derived. -/
noncomputable def familyOfAlignments
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (hbetaBound : ∀ l y, beta l y ≤ b l)
    (hbetaMeasurable : ∀ l, Measurable (beta l))
    (alignment : ∀ scale : ℕ, ∀ hscale : 0 < scale,
      PerScaleDensityChannelAlignment Gamma beta v scale hscale) :
    AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable where
  alignment := alignment
  sameDriver := fun scale hscale =>
    sameDriverCertificate_of_alignment (alignment scale hscale) hbetaZero

/-- **Per-scale-start strong approximation from the alignments alone.** -/
theorem sip_density_strong_approximation_of_alignments
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (hbetaBound : ∀ l y, beta l y ≤ b l)
    (hbetaMeasurable : ∀ l, Measurable (beta l))
    (alignment : ∀ scale : ℕ, ∀ hscale : 0 < scale,
      PerScaleDensityChannelAlignment Gamma beta v scale hscale)
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {omega | N i omega = k} = ENNReal.ofReal (poisTerm k 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ y z,
      ‖tcDrift beta v y - tcDrift beta v z‖ ≤ L * ‖y - z‖)
    {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → Fin d → ℝ} {xZero : Fin d → ℝ}
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Icc (0 : ℝ) T,
      x t = xZero +
        ∫ s in (0 : ℝ)..t, tcDrift beta v (x s)) :
    (∀ scale : ℕ, ∀ hscale : 0 < scale,
      (familyMeasure ι P).map
          (fun (omega : ι → PathSpace Omega) (t : ℝ≥0) =>
            namedPoissonTimeChange (N := N)
              beta v b hbetaZero hbetaBound hbetaMeasurable
              ((familyOfAlignments hbetaZero hbetaBound hbetaMeasurable
                alignment).startDensity scale) scale omega t) =
        ((DensityDepCTMC.mk scale hscale Gamma).toQMatrix.canonicalRecordMeasure
          (alignment scale hscale).latticeStart).map
            (AlignedCellCoupling.canonicalDensityNonnegative
              (DensityDepCTMC.mk scale hscale Gamma))) ∧
      (∀ᵐ omega ∂familyMeasure ι P,
        ∀ᶠ scale : ℕ in atTop,
          ∀ t ∈ Icc (0 : ℝ) T,
            ‖namedPoissonTimeChange (N := N)
                beta v b hbetaZero hbetaBound hbetaMeasurable
                ((familyOfAlignments hbetaZero hbetaBound hbetaMeasurable
                  alignment).startDensity scale) scale omega t - x t‖ ≤
              Real.exp (L * T) *
                (‖(familyOfAlignments hbetaZero hbetaBound hbetaMeasurable
                    alignment).startDensity scale - xZero‖ +
                  SIPDensityPerScaleStart.densityLILError
                    v b T scale)) :=
  (familyOfAlignments hbetaZero hbetaBound hbetaMeasurable
    alignment).sip_density_strong_approximation_of_ae_cell_records
      hNm hN hNl hL hF hT hxc hx

end SIP

/-!
THEOREM LIST
* `record_succ_of_inactive`, `inactive_persist`, `active_state_ne`
* `recordRealPath_frozen_of_first_inactive`
* `sum_count_step`, `finitePart_le_rate_mul_start`
* `exists_inactive_of_bounded`
* `clock_const_segment`, `driver_count_of_const`, `active_room`
* `recordSegment_exists`
* `RegularRecordClockProducer`, `regularRecordClockProducerOfAlignment`
* `recordClockBridgeAE_of_alignment`
* `recursiveClockEquationAE_of_alignment`
* `sameDriverCertificate_of_alignment`
* `familyOfAlignments`, `sip_density_strong_approximation_of_alignments`
END
-/

end Ripple.Kurtz.StrongApprox.CellRecordTimeCoverage

end

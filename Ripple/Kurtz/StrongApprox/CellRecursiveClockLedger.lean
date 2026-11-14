-- Ripple/Kurtz/StrongApprox/CellRecursiveClockLedger.lean
import Ripple.Kurtz.StrongApprox.CellSimpleFirstArrival

/-!
# Record-index clock and count ledger on the regular simple event

`RecordRaceRegular` is the corrected pointwise event.  It contains exactly the
finite-line, finite-residual, and unique scaled-residual winner facts needed
at each record.  The file proves the state/count and integrated-clock
induction, and the time-zero readout.  It does not address physical-time
coverage (`RecordClockBridge.locate`).
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellRecursiveClockLedger

open MeasureTheory ProbabilityTheory Set Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open Ripple.Kurtz
open CellFamilySimplePoints
open CellSimpleFirstArrival
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

/-- Active-rate vector at recursive record `k`. -/
noncomputable def recordRate
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ) : ι → ℝ≥0 :=
  A.latticeRate (recordMap A c k).2

/-- Common active-race holding time at recursive record `k`. -/
noncomputable def recordWait
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ) : ℝ≥0∞ :=
  activeRaceWaitE (internalMap A k) (recordRate A c k) c

/-- The pointwise regularity missing from `SimpleCellFamily`.

The last field says that, whenever a rate is active, one channel is the unique
strict minimizer of the scaled residual terms.  It does not mention the
selected state, line increments, cell counts, record ledger, or clock
integrals. -/
structure RecordRaceRegular
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) : Prop where
  line_finite : ∀ k l, internalMap A k c l ≠ ∞
  residual_finite : ∀ k l,
    extendedResidualWaitE (internalMap A k) c l ≠ ∞
  active_strict : ∀ k,
    HasActiveRate (recordRate A c k) →
      ∃ winner : ι,
        0 < recordRate A c k winner ∧
        recordWait A c k =
          activeRaceTermE (internalMap A k)
            (recordRate A c k) c winner ∧
        ∀ l, l ≠ winner →
          recordWait A c k <
            activeRaceTermE (internalMap A k)
              (recordRate A c k) c l

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

/-- Every recursively stored holding coordinate is nonnegative, without any
regularity assumption. -/
theorem recordHolding_nonneg
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ) :
    0 ≤ (recordMap A c (k + 1)).1 := by
  change 0 ≤ (activeNextRecordValue
      (internalMap A k) (internalMap A (k + 1))
      (fun z => (recordMap A z k).2)
      A.latticeRate A.latticeStep c).1
  unfold activeNextRecordValue
  split_ifs with hactive
  · simp only [Prod.fst]
    rw [observableActiveHoldingTime_eq_of_active
      (internalMap A k) (internalMap A (k + 1))
      (fun z => (recordMap A z k).2) A.latticeRate c hactive]
    exact ENNReal.toReal_nonneg
  · simp

@[simp]
theorem recordStartTime_succ
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ) :
    recordStartTime A c (k + 1) =
      recordStartTime A c k + (recordMap A c (k + 1)).1 := by
  simpa [recordStartTime] using
    (DensityModel Gamma n hn).canonicalPathMap_sojournStart_succ
      (recordMap A c) k

/-- Cumulative record starts are monotone because every stored holding
coordinate is nonnegative. -/
theorem recordStartTime_mono
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) :
    Monotone (recordStartTime A c) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [recordStartTime_succ]
  exact le_add_of_nonneg_right (recordHolding_nonneg A c k)

/-- The frozen recursive readout is the current scaled lattice state on a
half-open record interval. -/
theorem recordRealPath_eq_scaledState_of_interval
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ) {t : ℝ}
    (hleft : recordStartTime A c k ≤ t)
    (hright : t < recordStartTime A c (k + 1)) :
    recordRealPath A c t =
      (DensityModel Gamma n hn).scaledState (recordMap A c k).2 := by
  let path :=
    (DensityModel Gamma n hn).canonicalPathMap (recordMap A c)
  have hstate : path.frozenStateAt t = path.stateSeq k :=
    path.frozenStateAt_eq_stateSeq_of_sojourn
      (by simpa [path, recordStartTime] using recordStartTime_mono A c)
      k hleft hright
  unfold recordRealPath
  rw [show path.frozenStateAt t =
      ((DensityModel Gamma n hn).canonicalPathMap
        (recordMap A c)).frozenStateAt t from rfl]
  rw [hstate]
  exact congrArg (DensityModel Gamma n hn).scaledState
    ((DensityModel Gamma n hn).canonicalPathMap_stateSeq
      (recordMap A c) k)

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

/-- The integrated beta clock advances linearly across one record interval.
The endpoint may carry the successor state, but it is a volume-null singleton. -/
theorem recordClock_succ
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ) (l : ι) :
    clock beta (recordRealPath A c) l (recordStartTime A c (k + 1)) =
      clock beta (recordRealPath A c) l (recordStartTime A c k) +
        (recordMap A c (k + 1)).1 *
          beta l ((DensityModel Gamma n hn).scaledState
            (recordMap A c k).2) := by
  have hle : recordStartTime A c k ≤ recordStartTime A c (k + 1) :=
    recordStartTime_mono A c (Nat.le_succ k)
  have hae : ∀ᵐ s ∂volume,
      s ≠ recordStartTime A c (k + 1) := by
    filter_upwards
      [(Set.countable_singleton
        (recordStartTime A c (k + 1))).ae_notMem volume]
      with s hs
    simpa using hs
  have hpiece :
      ∫ s in recordStartTime A c k..recordStartTime A c (k + 1),
          beta l (recordRealPath A c s) =
        (recordStartTime A c (k + 1) - recordStartTime A c k) *
          beta l ((DensityModel Gamma n hn).scaledState
            (recordMap A c k).2) := by
    calc
      ∫ s in recordStartTime A c k..recordStartTime A c (k + 1),
          beta l (recordRealPath A c s) =
        ∫ _s in recordStartTime A c k..recordStartTime A c (k + 1),
          beta l ((DensityModel Gamma n hn).scaledState
            (recordMap A c k).2) := by
              refine intervalIntegral.integral_congr_ae ?_
              filter_upwards [hae] with s hs hmem
              rw [Set.uIoc_of_le hle] at hmem
              have hslt : s < recordStartTime A c (k + 1) :=
                lt_of_le_of_ne hmem.2 hs
              rw [recordRealPath_eq_scaledState_of_interval
                A c k hmem.1.le hslt]
      _ = _ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
  unfold clock
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (recordRate_intervalIntegrable A c l 0 (recordStartTime A c k))
      (recordRate_intervalIntegrable A c l
        (recordStartTime A c k) (recordStartTime A c (k + 1))),
    hpiece, recordStartTime_succ, add_sub_cancel_left]

/-- **Corrected record-index ledger.**  Same-cell simplicity supplies unit
jumps; `RecordRaceRegular` supplies the separate finite-residual and
cross-channel strict-winner facts. -/
theorem recordLedgerAt_of_simple
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (c : CellFamily ι)
    (hsimple : SimpleCellFamily c)
    (hregular : RecordRaceRegular A c) :
    ∀ k, RecordLedgerAt A c k := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · simpa [recordMap, internalMap, extendedPathAt, finitePart,
          initialInternalLine, cellPath_zero] using A.initial_alignment
      · intro l
        simp [internalMap, finitePart, initialInternalLine,
          recordStartTime, clock]
  | succ k ih =>
      let x : DensityState d n := (recordMap A c k).2
      by_cases hactive : HasActiveRate (recordRate A c k)
      · obtain ⟨winner, hwinnerRate, hwait, hincWinner,
          hincOther, hrecord⟩ :=
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
        have hsum :
            ∑ l, (((extendedPathAt (internalMap A (k + 1)) l c : ℕ) : ℝ) /
                (n : ℝ)) • v l =
              (∑ l, (((extendedPathAt (internalMap A k) l c : ℕ) : ℝ) /
                (n : ℝ)) • v l) +
                (n : ℝ)⁻¹ • v winner := by
          calc
            ∑ l, (((extendedPathAt (internalMap A (k + 1)) l c : ℕ) : ℝ) /
                (n : ℝ)) • v l =
              ∑ l, ((((extendedPathAt (internalMap A k) l c : ℕ) : ℝ) /
                  (n : ℝ)) • v l +
                if l = winner then (n : ℝ)⁻¹ • v winner else 0) := by
                  apply Finset.sum_congr rfl
                  intro l _
                  by_cases hl : l = winner
                  · subst l
                    rw [hcountStep, hincWinner]
                    ext i
                    simp only [Nat.cast_add, Nat.cast_one, Pi.add_apply,
                      Pi.smul_apply, smul_eq_mul]
                    simp
                    ring
                  · rw [hcountStep, hincOther l hl]
                    simp [hl]
            _ = _ := by
              rw [Finset.sum_add_distrib]
              simp
        have hscaled :
            (DensityModel Gamma n hn).scaledState
                (A.latticeStep x winner) =
              (DensityModel Gamma n hn).scaledState x +
                (n : ℝ)⁻¹ • v winner :=
          scaledState_latticeStep_eq A x winner
            (by simpa [recordRate, x] using hwinnerRate)
        have hrate (l : ι) :
            ((recordRate A c k l : ℝ≥0) : ℝ) =
              (n : ℝ) * beta l
                ((DensityModel Gamma n hn).scaledState x) := by
          calc
            ((recordRate A c k l : ℝ≥0) : ℝ) =
                (n : ℝ) * Gamma.rate (A.jump l)
                  ((DensityModel Gamma n hn).scaledState x) := by
              simpa [recordRate, x] using
                latticeRate_coe_eq_gamma A hbetaZero
                  (recordMap A c k).2 l
            _ = (n : ℝ) * beta l
                ((DensityModel Gamma n hn).scaledState x) := by
              simp [A.beta_eq, PerScaleDensityChannelAlignment.jump]
        have hlineStep (l : ι) :
            ((finitePart (internalMap A (k + 1)) c l : ℝ≥0) : ℝ) =
              ((finitePart (internalMap A k) c l : ℝ≥0) : ℝ) +
                ((recordRate A c k l : ℝ≥0) : ℝ) *
                  (recordWait A c k).toReal := by
          change (internalMap A (k + 1) c l).toReal =
            (internalMap A k c l).toReal +
              ((recordRate A c k l : ℝ≥0) : ℝ) *
                (recordWait A c k).toReal
          have hwait' :
              activeRaceWaitE (internalMap A k) (recordRate A c k) c ≠ ∞ :=
            hwait
          rw [hnext]
          unfold activeNextInternal
          rw [ENNReal.toReal_add
            (hregular.line_finite k l)
            (ENNReal.mul_ne_top ENNReal.coe_ne_top hwait')]
          simp [recordWait]
        refine ⟨?_, ?_⟩
        · rw [hrecord]
          simp only [Prod.snd]
          calc
            (DensityModel Gamma n hn).scaledState
                (A.latticeStep x winner) =
              (DensityModel Gamma n hn).scaledState x +
                (n : ℝ)⁻¹ • v winner := hscaled
            _ = (A.xStart +
                ∑ l, (((extendedPathAt (internalMap A k) l c : ℕ) : ℝ) /
                  (n : ℝ)) • v l) +
                    (n : ℝ)⁻¹ • v winner := by
              rw [ih.state_count]
            _ = A.xStart +
                ∑ l, (((extendedPathAt (internalMap A (k + 1)) l c : ℕ) : ℝ) /
                  (n : ℝ)) • v l := by
              rw [hsum]
              abel
        · intro l
          have hclock := recordClock_succ A c k l
          rw [hrecord] at hclock
          simp only [Prod.fst] at hclock
          calc
            ((finitePart (internalMap A (k + 1)) c l : ℝ≥0) : ℝ) =
                ((finitePart (internalMap A k) c l : ℝ≥0) : ℝ) +
                  ((recordRate A c k l : ℝ≥0) : ℝ) *
                    (recordWait A c k).toReal := hlineStep l
            _ = (n : ℝ) *
                  clock beta (recordRealPath A c) l
                    (recordStartTime A c k) +
                ((n : ℝ) * beta l
                  ((DensityModel Gamma n hn).scaledState x)) *
                    (recordWait A c k).toReal := by
              rw [ih.internal_clock l, hrate l]
            _ = (n : ℝ) *
                (clock beta (recordRealPath A c) l
                    (recordStartTime A c k) +
                  (recordWait A c k).toReal *
                    beta l ((DensityModel Gamma n hn).scaledState x)) := by
              ring
            _ = (n : ℝ) *
                clock beta (recordRealPath A c) l
                  (recordStartTime A c (k + 1)) := by
              rw [hclock]
      · have _habsorbing :
            (DensityModel Gamma n hn).toQMatrix.IsAbsorbing x := by
          by_contra hnon
          apply hactive
          have h :=
            (aligned_has_active_iff (activeRaceDataOf A) x).2 hnon
          simpa [recordRate, x] using h
        have hnextLine :
            internalMap A (k + 1) c = internalMap A k c := by
          rw [internalMap_succ_apply A c k,
            activeNextInternal_eq_self_of_no_active
              (internalMap A k) (recordRate A c k) hactive]
        have hrecord : recordMap A c (k + 1) = (0, x) := by
          change activeNextRecordValue
              (internalMap A k) (internalMap A (k + 1))
              (fun z => (recordMap A z k).2)
              A.latticeRate A.latticeStep c = _
          have hactive' :
              ¬ HasActiveRate (A.latticeRate (recordMap A c k).2) := hactive
          rw [activeNextRecordValue, if_neg hactive']
        have hpathEq (l : ι) :
            extendedPathAt (internalMap A (k + 1)) l c =
              extendedPathAt (internalMap A k) l c := by
          unfold extendedPathAt finitePart
          rw [hnextLine]
        have htimeEq :
            recordStartTime A c (k + 1) = recordStartTime A c k := by
          rw [recordStartTime_succ, hrecord]
          simp
        refine ⟨?_, ?_⟩
        · rw [hrecord]
          simp only [Prod.snd]
          simpa [hpathEq] using ih.state_count
        · intro l
          have hfin : finitePart (internalMap A (k + 1)) c l =
              finitePart (internalMap A k) c l := by
            unfold finitePart
            rw [hnextLine]
          rw [hfin, htimeEq]
          exact ih.internal_clock l

/-- If the initial state has no active channel, every recursive record remains
`(0,latticeStart)` and every internal line remains the zero line at this
sample. -/
private theorem records_freeze_of_no_active
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι)
    (hno : ¬ HasActiveRate (A.latticeRate A.latticeStart)) :
    ∀ k,
      recordMap A c k = (0, A.latticeStart) ∧
        internalMap A k c = internalMap A 0 c := by
  intro k
  induction k with
  | zero =>
      exact ⟨by simp [recordMap], rfl⟩
  | succ k ih =>
      have hstate : (recordMap A c k).2 = A.latticeStart := by
        rw [ih.1]
      have hnoCurrent : ¬ HasActiveRate (recordRate A c k) := by
        simpa [recordRate, hstate] using hno
      have hline : internalMap A (k + 1) c = internalMap A k c := by
        rw [internalMap_succ_apply A c k,
          activeNextInternal_eq_self_of_no_active
            (internalMap A k) (recordRate A c k) hnoCurrent]
      have hrecord : recordMap A c (k + 1) = (0, A.latticeStart) := by
        change activeNextRecordValue
            (internalMap A k) (internalMap A (k + 1))
            (fun z => (recordMap A z k).2)
            A.latticeRate A.latticeStep c = _
        have hnoCurrent' :
            ¬ HasActiveRate (A.latticeRate (recordMap A c k).2) := hnoCurrent
        rw [activeNextRecordValue, if_neg hnoCurrent']
        simpa [hstate]
      exact ⟨hrecord, hline.trans ih.2⟩

/-- **Corrected initial field.**  A regular simple family has no zero-time
active jump, while an initially absorbing state is frozen forever. -/
theorem recordRealPath_zero
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι)
    (hsimple : SimpleCellFamily c)
    (hregular : RecordRaceRegular A c) :
    recordRealPath A c 0 = A.xStart := by
  by_cases hactive : HasActiveRate (A.latticeRate A.latticeStart)
  · have hactiveZero : HasActiveRate (recordRate A c 0) := by
      simpa [recordRate, recordMap] using hactive
    obtain ⟨winner, _hwinnerRate, hwait, hincWinner,
        _hincOther, hrecord⟩ :=
      activeRecordStep_of_simple A hsimple hregular 0 hactiveZero
    have hwaitNeZero : recordWait A c 0 ≠ 0 := by
      intro hzero
      have hzeroWait :
          activeRaceWaitE (internalMap A 0) (recordRate A c 0) c = 0 :=
        hzero
      have hsame : internalMap A 1 c = internalMap A 0 c := by
        rw [internalMap_succ_apply A c 0]
        funext l
        simp [activeNextInternal, hzeroWait]
      have hzeroInc :
          lineIncrement (internalMap A 0) (internalMap A 1)
            winner c = 0 := by
        unfold lineIncrement extendedPathAt finitePart
        rw [hsame]
        simp
      exact absurd (hzeroInc.symm.trans hincWinner) (by norm_num)
    have hwaitPos : 0 < (recordWait A c 0).toReal :=
      ENNReal.toReal_pos hwaitNeZero hwait
    have hstartZero : recordStartTime A c 0 = 0 := rfl
    have hstartOne : 0 < recordStartTime A c 1 := by
      rw [recordStartTime_succ, hstartZero, hrecord]
      simpa using hwaitPos
    have hpath := recordRealPath_eq_scaledState_of_interval
      A c 0 (by rw [hstartZero]) hstartOne
    calc
      recordRealPath A c 0 =
          (DensityModel Gamma n hn).scaledState (recordMap A c 0).2 :=
        hpath
      _ = (DensityModel Gamma n hn).scaledState A.latticeStart := by
        simp [recordMap]
      _ = A.xStart := A.initial_alignment
  · have hfreeze := records_freeze_of_no_active A c hactive
    let path :=
      (DensityModel Gamma n hn).canonicalPathMap (recordMap A c)
    have htimes : ∀ m, path.times m = 0 := by
      intro m
      dsimp [path]
      rw [(DensityModel Gamma n hn).canonicalPathMap_times]
      apply Finset.sum_eq_zero
      intro j _
      rw [(hfreeze (j + 1)).1]
    have hnoTime : ∀ m, ¬ (0 : ℝ) < path.times m := by
      intro m hm
      rw [htimes m] at hm
      exact (lt_irrefl 0 hm)
    have hseq0 : path.stateSeq 0 = (recordMap A c 0).2 :=
      (DensityModel Gamma n hn).canonicalPathMap_stateSeq (recordMap A c) 0
    have hseq1 : path.stateSeq 1 = (recordMap A c 1).2 :=
      (DensityModel Gamma n hn).canonicalPathMap_stateSeq (recordMap A c) 1
    have hstable : path.stateSeq 0 = path.stateSeq 1 := by
      rw [hseq0, hseq1, (hfreeze 0).1, (hfreeze 1).1]
    have hfrozen : path.frozenStateAt 0 = path.stateSeq 0 :=
      path.frozenStateAt_eq_stateSeq_of_first_stable
        0 0 hnoTime hstable (by
          intro j hj
          simp at hj)
    change (DensityModel Gamma n hn).scaledState
      (path.frozenStateAt 0) = A.xStart
    rw [hfrozen, hseq0, (hfreeze 0).1]
    exact A.initial_alignment

/-!
THEOREM LIST
* `recordRate`
* `recordWait`
* `RecordRaceRegular`
* `recordHolding_nonneg`
* `recordStartTime_succ`
* `recordStartTime_mono`
* `recordRealPath_eq_scaledState_of_interval`
* `recordClock_succ`
* `recordLedgerAt_of_simple`
* `recordRealPath_zero`

CLOSES
* Part 1 after the necessary correction: one winning cell point is consumed,
  all other channel increments are zero under the strict scaled-residual
  winner event.
* Part 2 after the necessary correction: `RecordLedgerAt A c k` for every
  record index.
* The `initial` field `recordRealPath A c 0 = A.xStart`.
* Active and absorbing recursion branches, including the integrated clock
  increment across each half-open holding interval.

UNFINISHED
* Prove `RecordRaceRegular A c` almost surely by taking the countable
  intersection of the existing recursive-line finiteness,
  `residualWaitE_finite_ae`, and `currentStateStrictWinner_ae` events.
* Replace or supplement the compiled `SimpleRecordClockProducer` interface:
  `SimpleCellFamily` alone is insufficient, so its pointwise
  `bridge_on_simple` field cannot be constructed as stated.
* Construct `RecordClockBridge.locate`; physical-time coverage remains a
  separate item.
END
-/

end Ripple.Kurtz.StrongApprox.CellRecursiveClockLedger

end

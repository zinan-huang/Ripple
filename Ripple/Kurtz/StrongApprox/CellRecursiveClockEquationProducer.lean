-- Ripple/Kurtz/StrongApprox/CellRecursiveClockEquationProducer.lean
import Ripple.Kurtz.StrongApprox.CellFamilySimplePoints
import Ripple.Kurtz.StrongApprox.CellPerScaleRecordPathAE

/-!
# The exact deterministic producer interface for the recursive clock equation

`RecordLedgerAt` is the record-index induction invariant. It uses cumulative
physical record time, never the one-step holding time stored in the record.
`RecordSegmentAt` is the corrected coverage statement: it permits either a
genuine next segment or an absorbing record.

The theorem in this file is deliberately not a path-equality assumption. It
turns the discrete state/count ledger and the inter-record no-crossing fact
into the time-change equation on the original cell sample.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellRecursiveClockEquationProducer

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open Ripple.Kurtz
open CellPerScaleDensityAlignment
open CellPerScaleRecordPathAE
open CellExtendedStoppingLine
open CellExtendedRandomTime
open CellFamilySimplePoints

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

/-- Cumulative physical start time of record `k`. -/
noncomputable def recordStartTime
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ) : ℝ :=
  ((DensityModel Gamma n hn).canonicalPathMap
    (recordMap A c)).sojournStart k

/-- Induction invariant at one record index.

The first field reconstructs the scaled state from the actual cell counts at
the recursive internal line. The second identifies that line with `n` times
the integrated beta-clock at the cumulative physical record time. -/
structure RecordLedgerAt
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (k : ℕ) : Prop where
  state_count :
    (DensityModel Gamma n hn).scaledState (recordMap A c k).2 =
      A.xStart +
        ∑ l, (((extendedPathAt (internalMap A k) l c : ℕ) : ℝ) /
          (n : ℝ)) • v l
  internal_clock : ∀ l,
    ((finitePart (internalMap A k) c l : ℝ≥0) : ℝ) =
      (n : ℝ) *
        clock beta (recordRealPath A c) l
          (recordStartTime A c k)

/-- Readout and driver counts on the physical segment containing `t`.

`end_or_absorbing` is the corrected replacement for a blanket assertion that
record times diverge. -/
structure RecordSegmentAt
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (t : ℝ) (k : ℕ) : Prop where
  start_le : recordStartTime A c k ≤ t
  end_or_absorbing :
    t < recordStartTime A c (k + 1) ∨
      (DensityModel Gamma n hn).toQMatrix.IsAbsorbing
        (recordMap A c k).2
  state_readout :
    recordRealPath A c t =
      (DensityModel Gamma n hn).scaledState (recordMap A c k).2
  driver_count : ∀ l,
    cellPath
        ((n : ℝ) * clock beta (recordRealPath A c) l t) (c l) =
      extendedPathAt (internalMap A k) l c

/-- Non-circular deterministic content needed from the simple-cell record
induction. -/
structure RecordClockBridge
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) : Prop where
  initial : recordRealPath A c 0 = A.xStart
  ledger : ∀ k, RecordLedgerAt A c k
  locate : ∀ t : ℝ, 0 ≤ t → ∃ k,
    RecordSegmentAt A c t k

/-- Probability-one bridge target. -/
def RecordClockBridgeAE
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) : Prop :=
  ∀ᵐ c ∂cellFamilyLaw ι, RecordClockBridge A c

/-- The only deterministic construction still missing after the simplicity
law. Its field is exactly route items (2)--(5), corrected for cumulative
record times and absorption. -/
structure SimpleRecordClockProducer
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) : Prop where
  bridge_on_simple : ∀ c,
    SimpleCellFamily c → RecordClockBridge A c

/-- A record/count bridge gives the recursive clock equation pointwise. -/
theorem recursiveClockEquation_of_recordClockBridge
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    {c : CellFamily ι} (H : RecordClockBridge A c) :
    RecursiveClockEquation A c := by
  refine ⟨H.initial, ?_⟩
  intro t ht
  obtain ⟨k, hk⟩ := H.locate t ht
  calc
    recordRealPath A c t =
        (DensityModel Gamma n hn).scaledState (recordMap A c k).2 :=
      hk.state_readout
    _ = A.xStart +
        ∑ l, (((extendedPathAt (internalMap A k) l c : ℕ) : ℝ) /
          (n : ℝ)) • v l :=
      (H.ledger k).state_count
    _ = A.xStart +
        ∑ l, ((cellPath
          ((n : ℝ) * clock beta (recordRealPath A c) l t) (c l) : ℝ) /
            (n : ℝ)) • v l := by
      apply congrArg (fun z : Fin d → ℝ => A.xStart + z)
      apply Finset.sum_congr rfl
      intro l _
      rw [hk.driver_count l]

/-- Almost-sure bridge implies the producer target. -/
theorem recursiveClockEquationAE_of_recordClockBridgeAE
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (H : RecordClockBridgeAE A) :
    RecursiveClockEquationAE A :=
  H.mono (fun _ hc => recursiveClockEquation_of_recordClockBridge A hc)

/-- The probability-one simple-cell theorem removes all stochastic input from
`SimpleRecordClockProducer`; only its deterministic induction remains. -/
theorem recordClockBridgeAE_of_simpleProducer
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (P : SimpleRecordClockProducer A) :
    RecordClockBridgeAE A := by
  filter_upwards [simpleCellFamily_ae (ι := ι)] with c hc
  exact P.bridge_on_simple c hc

/-- Central producer, conditional only on the deterministic simple-cell
record induction. -/
theorem recursiveClockEquationAE_of_simpleProducer
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (P : SimpleRecordClockProducer A) :
    RecursiveClockEquationAE A :=
  recursiveClockEquationAE_of_recordClockBridgeAE A
    (recordClockBridgeAE_of_simpleProducer A P)

/-- The same-driver certificate is derived; it is not an input coupling. -/
def sameDriverCertificate_of_simpleProducer
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (P : SimpleRecordClockProducer A) :
    SameDriverCertificate A where
  clockEquationAE := recursiveClockEquationAE_of_simpleProducer A P

/-!
THEOREM LIST
* `recordStartTime`
* `RecordLedgerAt`
* `RecordSegmentAt`
* `RecordClockBridge`
* `RecordClockBridgeAE`
* `SimpleRecordClockProducer`
* `recursiveClockEquation_of_recordClockBridge`
* `recursiveClockEquationAE_of_recordClockBridgeAE`
* `recordClockBridgeAE_of_simpleProducer`
* `recursiveClockEquationAE_of_simpleProducer`
* `sameDriverCertificate_of_simpleProducer`

CLOSES
* The corrected cumulative-time statement of the induction invariant.
* The absorbing/nonabsorbing coverage disjunction.
* The pointwise and almost-sure conversion from the discrete clock ledger to
  `RecursiveClockEquation` / `RecursiveClockEquationAE`.
* Construction of the `SameDriverCertificate` without assuming a coupling.

UNFINISHED
* Construct `SimpleRecordClockProducer A` from an arbitrary alignment `A`.
  The exact missing Lean work is listed after all code blocks.
END
-/

end Ripple.Kurtz.StrongApprox.CellRecursiveClockEquationProducer

end

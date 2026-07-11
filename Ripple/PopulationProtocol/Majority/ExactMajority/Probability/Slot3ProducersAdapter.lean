import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3ResidualsDischarge

/-!
# Slot-3 producer and adapter wiring

This file is intentionally a thin assembly layer.  The producer side is fully
deterministic packaging of the landed leaf data.  The adapter side names the
remaining protocol-thread coupling obligations required by the current
`CoreRowsSnapshot617Adapter` interface and then packs them without adding any
new mathematical assumption implicitly.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The landed slot-3 leaf data at one concrete Core thread. -/
structure Slot3ChainProducerData
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  pre3 : Phase3Core.Pre3Seed (L := L) (K := K) D T
  h13 :
    Lemma613MarkedPullDrop.H13MarkedPullData
      (L := L) (K := K) D T
  h14 : Phase3Bridges.H14Bridge (L := L) (K := K) D T
  h15 : Phase3Engines.H15Engine (L := L) (K := K) D T
  h16 :
    Lemma616MarkedCancelMass.H16MarkedCancelData
      (L := L) (K := K) D T

namespace Slot3ChainProducerData

/-- Package the landed leaf data as the producer bundle consumed by
`snapshot617EntryTail_of_dischargedCore`. -/
noncomputable def toProducers
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : Slot3ChainProducerData (L := L) (K := K) D T) :
    DischargedCoreEngineProducers (L := L) (K := K) D T where
  pre3 := P.pre3
  h13 := P.h13
  h14 := P.h14
  h15 := P.h15
  h16 := P.h16

theorem lemma612_all
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : Slot3ChainProducerData (L := L) (K := K) D T) :
    ∀ h, h ≤ D.lastCoreHour →
      Phase3Core.Lemma612 (L := L) (K := K) D T h :=
  DischargedCoreEngineProducers.lemma612_all
    (L := L) (K := K) P.toProducers

end Slot3ChainProducerData

/-- Fields required to instantiate the current Core-row snapshot adapter at one
protocol thread.

The names are deliberately close to the target fields.  In particular,
`good0`, `gate_eq`, `next_of_rows`, and the `hourLen_h16_*` fields expose the
current shape obligations of `Phase3Post3.CoreRowsSnapshot617Adapter`; they are
not hidden behind the producer data. -/
structure Slot3CoreRowsAdapterData
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) where
  horizon : Phase3Post3.Snapshot617Horizon (L := L) (K := K) n ell
  gate : Set (Config (AgentState L K))
  H : ℕ
  hourLen : ℕ → ℕ
  Good : ℕ → Option (Config (AgentState L K)) → Prop
  hCore : ∀ i, i < H → i ≤ D.lastCoreHour
  gate_eq :
    ∀ i, i < H → gate = T.surface.hourGate i
  good0 :
    ∀ c₀,
      Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ c₀ →
        Good 0 (some c₀)
  none_bad :
    ¬ Good H none
  start_afterO :
    ∀ i, i < H → ∀ o,
      Good i o →
        ∃ c, o = some c ∧ c ∈ T.surface.checkpoint .afterO i
  start_afterPhi :
    ∀ i, i < H → ∀ o,
      Good i o →
        ∃ c, o = some c ∧ c ∈ T.surface.checkpoint .afterPhi i
  next_of_rows :
    ∀ i, i < H → ∀ c,
      Phase3Core.OFuelFloor (L := L) (K := K) D i c →
      Phase3Core.PhiPotentialDrop (L := L) (K := K) D i c →
      Phase3Core.TotalMassBound (L := L) (K := K) D i c →
        Good (i + 1) (some c)
  hourLen_h13_le :
    ∀ i, i < H →
      hourLen i ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput i) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput i)
  hourLen_h15_eq :
    ∀ i, i < H →
      hourLen i =
        Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput i)
  hourLen_h16_lo :
    ∀ i, i < H →
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput i) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i)
        ≤ hourLen i
  hourLen_h16_hi :
    ∀ i, i < H →
      hourLen i ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput i) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i)
  phase3 :
    ∀ c,
      Good H (some c) →
        Phase3Post3.AllPhase3 (L := L) (K := K) n c
  gap_eq :
    ∀ c,
      Good H (some c) →
        Phase3Post3.signedGap (L := L) (K := K) c = g₀
  total_mass_bound :
    ∀ c,
      Good H (some c) →
        Phase3Post3.weightedMass (L := L) (K := K) c ≤
          Lemma616TotalMass.Constants.rho_l * M * (2 : ℝ) ^ (-(ell : ℤ))
  muAbove_bound :
    ∀ c,
      Good H (some c) →
        Lemma615MassAbove.muAbove (L := L) (K := K) ell c ≤
          (1 / 500 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))
  minority_bound :
    ∀ c,
      Good H (some c) →
        Phase3Post3.minorityMass (L := L) (K := K) σ c ≤
          (1 / 250 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))
  main_confined :
    ∀ c,
      Good H (some c) →
        MainExponentConfinement.MainProfileConfinedToUseful
          (L := L) (K := K) c
  horizon_eq :
    horizon.T_end_l2 = ChapmanKolmogorovChain.hourPrefix hourLen H
  epsilon : ℝ≥0
  budget :
    (∑ i ∈ Finset.range H,
      Phase3Post3.coreRowError (L := L) (K := K) T i) ≤
        (epsilon : ℝ≥0∞)

namespace Slot3CoreRowsAdapterData

/-- Pack the endpoint readout fields into the readout structure. -/
def toReadout
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Slot3CoreRowsAdapterData
      (L := L) (K := K) D T n ell M g₀ σ) :
    Phase3Post3.CoreRowsSnapshot617Readout
      (L := L) (K := K) n ell M g₀ σ A.H A.Good where
  phase3 := A.phase3
  gap_eq := A.gap_eq
  total_mass_bound := A.total_mass_bound
  muAbove_bound := A.muAbove_bound
  minority_bound := A.minority_bound
  main_confined := A.main_confined

/-- Pack the named adapter data into the current Core-row snapshot adapter. -/
noncomputable def toAdapter
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Slot3CoreRowsAdapterData
      (L := L) (K := K) D T n ell M g₀ σ) :
    Phase3Post3.CoreRowsSnapshot617Adapter
      (L := L) (K := K) D T n ell M g₀ σ where
  horizon := A.horizon
  gate := A.gate
  H := A.H
  hourLen := A.hourLen
  Good := A.Good
  hCore := A.hCore
  gate_eq := A.gate_eq
  good0 := A.good0
  none_bad := A.none_bad
  start_afterO := A.start_afterO
  start_afterPhi := A.start_afterPhi
  next_of_rows := A.next_of_rows
  hourLen_h13_le := A.hourLen_h13_le
  hourLen_h15_eq := A.hourLen_h15_eq
  hourLen_h16_lo := A.hourLen_h16_lo
  hourLen_h16_hi := A.hourLen_h16_hi
  readout := A.toReadout
  horizon_eq := A.horizon_eq
  ε := A.epsilon
  budget := A.budget

end Slot3CoreRowsAdapterData

/-- Producer data plus the current adapter data at one protocol thread. -/
structure Slot3ProducersAdapterData
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) where
  producers : Slot3ChainProducerData (L := L) (K := K) D T
  adapter : Slot3CoreRowsAdapterData (L := L) (K := K) D T n ell M g₀ σ

namespace Slot3ProducersAdapterData

noncomputable def toProducers
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Slot3ProducersAdapterData
      (L := L) (K := K) D T n ell M g₀ σ) :
    DischargedCoreEngineProducers (L := L) (K := K) D T :=
  A.producers.toProducers

noncomputable def toAdapter
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Slot3ProducersAdapterData
      (L := L) (K := K) D T n ell M g₀ σ) :
    Phase3Post3.CoreRowsSnapshot617Adapter
      (L := L) (K := K) D T n ell M g₀ σ :=
  A.adapter.toAdapter

/-- The post-tail shape consumed by `Slot3ReadyClosureInputs`, once the concrete
entry seam is supplied. -/
noncomputable def toPostTailShapeInputs
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : Slot3ProducersAdapterData
      (L := L) (K := K) D T n ell M g₀ σ)
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry) :
    Slot3PostTailShapeInputs
      (L := L) (K := K) D T n ell M g₀ σ entry where
  entry_slot3 := hentry
  producers := A.toProducers
  adapter := A.toAdapter

/-- The final entry-specialized snapshot tail obtained from the producer and
adapter data. -/
noncomputable def entryTail
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : Slot3ProducersAdapterData
      (L := L) (K := K) D T n ell M g₀ σ)
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry) :
    Phase3Post3.Snapshot617EntryTail
      (L := L) (K := K) n ell M g₀ σ entry :=
  snapshot617EntryTail_of_dischargedCore
    (L := L) (K := K) A.toProducers A.toAdapter hentry

end Slot3ProducersAdapterData

end Phase3Assembly

end ExactMajority

#print axioms ExactMajority.Phase3Assembly.Slot3ChainProducerData.toProducers
#print axioms ExactMajority.Phase3Assembly.Slot3ChainProducerData.lemma612_all
#print axioms ExactMajority.Phase3Assembly.Slot3CoreRowsAdapterData.toReadout
#print axioms ExactMajority.Phase3Assembly.Slot3CoreRowsAdapterData.toAdapter
#print axioms ExactMajority.Phase3Assembly.Slot3ProducersAdapterData.entryTail

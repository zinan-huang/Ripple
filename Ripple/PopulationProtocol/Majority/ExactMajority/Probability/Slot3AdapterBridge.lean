import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3ProducersAdapter
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CoreSurfaceSixLeaf

/-!
# Slot-3 adapter bridge

This file isolates the adapter-to-predicate-surface interface.  It proves the
small bridges available from the existing predicate checkpoint surface and names
the residual facts that are not present in the current interfaces.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

namespace Slot3AdapterBridge

/-- The adapter's natural `Good` predicate when starts are represented by
predicate checkpoints: alive states must be at both row-start checkpoints. -/
def checkpointGood
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (i : ℕ) : Option (Config (AgentState L K)) → Prop
  | some c =>
      c ∈ T.surface.checkpoint .afterO i ∧
        c ∈ T.surface.checkpoint .afterPhi i
  | none => False

theorem checkpointGood_none
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (i : ℕ) :
    ¬ checkpointGood (L := L) (K := K) T i none := by
  simp [checkpointGood]

theorem checkpointGood_start_afterO
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (i : ℕ) :
    ∀ o,
      checkpointGood (L := L) (K := K) T i o →
        ∃ c, o = some c ∧ c ∈ T.surface.checkpoint .afterO i := by
  intro o ho
  cases o with
  | none =>
      exact False.elim ho
  | some c =>
      exact ⟨c, rfl, ho.1⟩

theorem checkpointGood_start_afterPhi
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (i : ℕ) :
    ∀ o,
      checkpointGood (L := L) (K := K) T i o →
        ∃ c, o = some c ∧ c ∈ T.surface.checkpoint .afterPhi i := by
  intro o ho
  cases o with
  | none =>
      exact False.elim ho
  | some c =>
      exact ⟨c, rfl, ho.2⟩

theorem slot3Entry_mem_afterO0_of_hourStart_bridge
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n : ℕ} {g₀ : ℝ}
    (hstart :
      ∀ c₀,
        Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ c₀ →
          c₀ ∈ T.surface.checkpoint .hourStart 0)
    (hwarm :
      T.surface.checkpoint .hourStart 0 ⊆
        T.surface.checkpoint .afterO 0) :
    ∀ c₀,
      Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ c₀ →
        c₀ ∈ T.surface.checkpoint .afterO 0 := by
  intro c₀ hentry
  exact hwarm (hstart c₀ hentry)

theorem slot3Entry_mem_afterPhi0_of_hourStart_bridge
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n : ℕ} {g₀ : ℝ}
    (hstart :
      ∀ c₀,
        Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ c₀ →
          c₀ ∈ T.surface.checkpoint .hourStart 0)
    (hwarm :
      T.surface.checkpoint .hourStart 0 ⊆
        T.surface.checkpoint .afterPhi 0) :
    ∀ c₀,
      Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ c₀ →
        c₀ ∈ T.surface.checkpoint .afterPhi 0 := by
  intro c₀ hentry
  exact hwarm (hstart c₀ hentry)

theorem pre3_entry_mem_afterO0_of_hourStart_bridge
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : Phase3Core.Pre3Seed (L := L) (K := K) D T)
    (hwarm :
      T.surface.checkpoint .hourStart 0 ⊆
        T.surface.checkpoint .afterO 0) :
    P.entry ∈ T.surface.checkpoint .afterO 0 :=
  hwarm P.entry_checkpoint

theorem pre3_entry_mem_afterPhi0_of_hourStart_bridge
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : Phase3Core.Pre3Seed (L := L) (K := K) D T)
    (hwarm :
      T.surface.checkpoint .hourStart 0 ⊆
        T.surface.checkpoint .afterPhi 0) :
    P.entry ∈ T.surface.checkpoint .afterPhi 0 :=
  hwarm P.entry_checkpoint

theorem checkpointGood_good0
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n : ℕ} {g₀ : ℝ}
    (hO0 :
      ∀ c₀,
        Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ c₀ →
          c₀ ∈ T.surface.checkpoint .afterO 0)
    (hPhi0 :
      ∀ c₀,
        Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ c₀ →
          c₀ ∈ T.surface.checkpoint .afterPhi 0) :
    ∀ c₀,
      Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ c₀ →
        checkpointGood (L := L) (K := K) T 0 (some c₀) := by
  intro c₀ hentry
  exact ⟨hO0 c₀ hentry, hPhi0 c₀ hentry⟩

/-- The same-hour predicate-surface bridge: rows plus hour-gate membership put a
state in the `afterMass h` checkpoint. -/
theorem rows_to_afterMass_of_predicateSurface
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {G :
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour}
    (F : CoreSurfacePredicateFacts (L := L) (K := K) D θ tr)
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (hsurface :
      T.surface =
        CoreSurfacePredicateFacts.mkSurface (L := L) (K := K) G F)
    {H : ℕ}
    (hgate :
      ∀ i, i < H → ∀ c,
        Phase3Core.OFuelFloor (L := L) (K := K) D i c →
        Phase3Core.PhiPotentialDrop (L := L) (K := K) D i c →
        Phase3Core.TotalMassBound (L := L) (K := K) D i c →
          c ∈ T.surface.hourGate i) :
    ∀ i, i < H → ∀ c,
      Phase3Core.OFuelFloor (L := L) (K := K) D i c →
      Phase3Core.PhiPotentialDrop (L := L) (K := K) D i c →
      Phase3Core.TotalMassBound (L := L) (K := K) D i c →
        c ∈ T.surface.checkpoint .afterMass i := by
  intro i hi c hO hPhi hMass
  have hg :
      c ∈
        (CoreSurfacePredicateFacts.mkSurface (L := L) (K := K) G F).hourGate i := by
    simpa [hsurface] using hgate i hi c hO hPhi hMass
  have hm :=
    CoreSurfacePredicateFacts.mem_afterMass_of_gate_of_floors
      (L := L) (K := K) F (h := i) (c := c) hg hO hPhi hMass
  simpa [hsurface] using hm

/-- The cut handoff still needed by the present adapter: same-hour rows first
enter `afterMass h`, and the inter-hour part moves that checkpoint to both
start checkpoints of hour `h+1`. -/
structure CoreRowsCutHandoff617
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (H : ℕ) : Prop where
  rows_to_afterMass :
    ∀ i, i < H → ∀ c,
      Phase3Core.OFuelFloor (L := L) (K := K) D i c →
      Phase3Core.PhiPotentialDrop (L := L) (K := K) D i c →
      Phase3Core.TotalMassBound (L := L) (K := K) D i c →
        c ∈ T.surface.checkpoint .afterMass i
  afterMass_to_next_afterO :
    ∀ i, i < H → ∀ c,
      c ∈ T.surface.checkpoint .afterMass i →
        c ∈ T.surface.checkpoint .afterO (i + 1)
  afterMass_to_next_afterPhi :
    ∀ i, i < H → ∀ c,
      c ∈ T.surface.checkpoint .afterMass i →
        c ∈ T.surface.checkpoint .afterPhi (i + 1)

theorem checkpointGood_next_of_rows
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {H : ℕ}
    (B : CoreRowsCutHandoff617 (L := L) (K := K) D T H) :
    ∀ i, i < H → ∀ c,
      Phase3Core.OFuelFloor (L := L) (K := K) D i c →
      Phase3Core.PhiPotentialDrop (L := L) (K := K) D i c →
      Phase3Core.TotalMassBound (L := L) (K := K) D i c →
        checkpointGood (L := L) (K := K) T (i + 1) (some c) := by
  intro i hi c hO hPhi hMass
  have hafterMass := B.rows_to_afterMass i hi c hO hPhi hMass
  exact
    ⟨B.afterMass_to_next_afterO i hi c hafterMass,
      B.afterMass_to_next_afterPhi i hi c hafterMass⟩

theorem surfaceOf_hourStart_subset_afterO
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (S : CoreSurfaceSixLeaf (L := L) (K := K) D θ tr)
    (G : Phase3GoodClockRegime.GoodClockUpTo
      (L := L) (K := K) D.M θ tr D.lastCoreHour)
    (h : ℕ) :
    (S.surfaceOf (L := L) (K := K) G).checkpoint .hourStart h ⊆
      (S.surfaceOf (L := L) (K := K) G).checkpoint .afterO h := by
  intro c hc
  dsimp [CoreSurfaceSixLeaf.surfaceOf, CoreSurfacePredicateFacts.mkSurface,
    CoreSurfaceSixLeaf.toFacts, Phase3Assembly.predicateCheckpoint] at hc ⊢
  exact ⟨hc.1, Or.inl (Set.mem_univ c)⟩

theorem surfaceOf_hourStart_subset_afterPhi
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (S : CoreSurfaceSixLeaf (L := L) (K := K) D θ tr)
    (G : Phase3GoodClockRegime.GoodClockUpTo
      (L := L) (K := K) D.M θ tr D.lastCoreHour)
    (h : ℕ) :
    (S.surfaceOf (L := L) (K := K) G).checkpoint .hourStart h ⊆
      (S.surfaceOf (L := L) (K := K) G).checkpoint .afterPhi h := by
  intro c hc
  dsimp [CoreSurfaceSixLeaf.surfaceOf, CoreSurfacePredicateFacts.mkSurface,
    CoreSurfaceSixLeaf.toFacts, Phase3Assembly.predicateCheckpoint] at hc ⊢
  exact ⟨hc.1, Or.inl (Set.mem_univ c)⟩

/-- The only hour length compatible with the current H15 equality field. -/
noncomputable def clockCutHourLen
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (i : ℕ) : ℕ :=
  Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i) -
    Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput i)

theorem clockCutHourLen_h15_eq
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (i : ℕ) :
    clockCutHourLen (L := L) (K := K) T i =
      Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i) -
        Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput i) :=
  rfl

theorem clockCutHourLen_h13_le
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (i : ℕ) :
    clockCutHourLen (L := L) (K := K) T i ≤
      Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput i) -
        Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput i) := by
  exact Nat.sub_le_sub_right
    (by
      simpa [Phase3Core.ClockCut.afterPhi] using
        (T.clockInput i).fortyOne_inside)
    (Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput i))

theorem clockCutHourLen_h16_lo_of_cut_arith
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (i : ℕ)
    (h47 :
      θ.fortySevenOverM ≤
        θ.fortyOneOverM + θ.fortyOneOverM) :
    Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput i) -
        Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i)
      ≤ clockCutHourLen (L := L) (K := K) T i := by
  unfold clockCutHourLen Phase3Core.ClockCut.afterMass
    Phase3Core.ClockCut.afterPhi Phase3Core.ClockCut.afterO
  omega

theorem clockCutHourLen_h16_hi_of_double_phi_inside
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (i : ℕ)
    (hinside :
      Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i) +
          clockCutHourLen (L := L) (K := K) T i
        ≤ Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput i)) :
    clockCutHourLen (L := L) (K := K) T i ≤
      Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput i) -
        Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i) := by
  omega

/-- The two timing facts not supplied by `ClockTimingParams`: H16 can use the
H15 length only if the 47/41 gap is short enough and `finish` is late enough. -/
structure ClockCutHourLenResiduals
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (H : ℕ) : Prop where
  h16_lo :
    ∀ i, i < H →
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput i) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i)
        ≤ clockCutHourLen (L := L) (K := K) T i
  h16_hi :
    ∀ i, i < H →
      clockCutHourLen (L := L) (K := K) T i ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput i) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i)

/-- Current single-gate requirement of the existing adapter.  The predicate
surface does not produce this automatically because `predicateHourGate` is
indexed by the hour. -/
structure SingleGateOnH
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (H : ℕ) : Prop where
  gate_eq_zero : ∀ i, i < H → T.surface.hourGate 0 = T.surface.hourGate i

theorem gate_eq_of_singleGateOnH
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {H : ℕ}
    (G : SingleGateOnH (L := L) (K := K) T H) :
    ∀ i, i < H → T.surface.hourGate 0 = T.surface.hourGate i :=
  G.gate_eq_zero

/-- Predicate-surface bridge input for the current `CoreRowsSnapshot617Adapter`.

The fields whose names contain `residual` are the precise remaining interface
facts: a single gate over all hours, the inter-hour cut handoff, and the H16
compatibility of the H15 clock length. -/
structure PredicateCheckpointAdapterInput
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) where
  horizon : Phase3Post3.Snapshot617Horizon (L := L) (K := K) n ell
  H : ℕ
  hCore : ∀ i, i < H → i ≤ D.lastCoreHour
  gate_residual : SingleGateOnH (L := L) (K := K) T H
  good0_afterO :
    ∀ c₀,
      Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ c₀ →
        c₀ ∈ T.surface.checkpoint .afterO 0
  good0_afterPhi :
    ∀ c₀,
      Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ c₀ →
        c₀ ∈ T.surface.checkpoint .afterPhi 0
  cut_handoff_residual :
    CoreRowsCutHandoff617 (L := L) (K := K) D T H
  hourLen_residual :
    ClockCutHourLenResiduals (L := L) (K := K) T H
  phase3 :
    ∀ c,
      checkpointGood (L := L) (K := K) T H (some c) →
        Phase3Post3.AllPhase3 (L := L) (K := K) n c
  gap_eq :
    ∀ c,
      checkpointGood (L := L) (K := K) T H (some c) →
        Phase3Post3.signedGap (L := L) (K := K) c = g₀
  total_mass_bound :
    ∀ c,
      checkpointGood (L := L) (K := K) T H (some c) →
        Phase3Post3.weightedMass (L := L) (K := K) c ≤
          Lemma616TotalMass.Constants.rho_l * M * (2 : ℝ) ^ (-(ell : ℤ))
  muAbove_bound :
    ∀ c,
      checkpointGood (L := L) (K := K) T H (some c) →
        Lemma615MassAbove.muAbove (L := L) (K := K) ell c ≤
          (1 / 500 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))
  minority_bound :
    ∀ c,
      checkpointGood (L := L) (K := K) T H (some c) →
        Phase3Post3.minorityMass (L := L) (K := K) σ c ≤
          (1 / 250 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))
  main_confined :
    ∀ c,
      checkpointGood (L := L) (K := K) T H (some c) →
        MainExponentConfinement.MainProfileConfinedToUseful
          (L := L) (K := K) c
  horizon_eq :
    horizon.T_end_l2 =
      ChapmanKolmogorovChain.hourPrefix (clockCutHourLen (L := L) (K := K) T) H
  epsilon : ℝ≥0
  budget :
    (∑ i ∈ Finset.range H,
      Phase3Post3.coreRowError (L := L) (K := K) T i) ≤
        (epsilon : ℝ≥0∞)

namespace PredicateCheckpointAdapterInput

/-- Pack the refined predicate-checkpoint bridge into the previously diagnosed
adapter data structure. -/
noncomputable def toCoreRowsAdapterData
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : PredicateCheckpointAdapterInput
      (L := L) (K := K) D T n ell M g₀ σ) :
    Slot3CoreRowsAdapterData (L := L) (K := K) D T n ell M g₀ σ where
  horizon := A.horizon
  gate := T.surface.hourGate 0
  H := A.H
  hourLen := clockCutHourLen (L := L) (K := K) T
  Good := checkpointGood (L := L) (K := K) T
  hCore := A.hCore
  gate_eq := gate_eq_of_singleGateOnH
    (L := L) (K := K) A.gate_residual
  good0 := checkpointGood_good0
    (L := L) (K := K) A.good0_afterO A.good0_afterPhi
  none_bad := checkpointGood_none (L := L) (K := K) T A.H
  start_afterO := by
    intro i _hi
    exact checkpointGood_start_afterO (L := L) (K := K) T i
  start_afterPhi := by
    intro i _hi
    exact checkpointGood_start_afterPhi (L := L) (K := K) T i
  next_of_rows :=
    checkpointGood_next_of_rows
      (L := L) (K := K) A.cut_handoff_residual
  hourLen_h13_le := by
    intro i _hi
    exact clockCutHourLen_h13_le (L := L) (K := K) T i
  hourLen_h15_eq := by
    intro i _hi
    exact clockCutHourLen_h15_eq (L := L) (K := K) T i
  hourLen_h16_lo := A.hourLen_residual.h16_lo
  hourLen_h16_hi := A.hourLen_residual.h16_hi
  phase3 := A.phase3
  gap_eq := A.gap_eq
  total_mass_bound := A.total_mass_bound
  muAbove_bound := A.muAbove_bound
  minority_bound := A.minority_bound
  main_confined := A.main_confined
  horizon_eq := A.horizon_eq
  epsilon := A.epsilon
  budget := A.budget

/-- Direct construction of the current target adapter from the refined bridge
input. -/
noncomputable def toAdapter
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : PredicateCheckpointAdapterInput
      (L := L) (K := K) D T n ell M g₀ σ) :
    Phase3Post3.CoreRowsSnapshot617Adapter
      (L := L) (K := K) D T n ell M g₀ σ :=
  A.toCoreRowsAdapterData.toAdapter

end PredicateCheckpointAdapterInput

end Slot3AdapterBridge

end Phase3Assembly

end ExactMajority

#print axioms ExactMajority.Phase3Assembly.Slot3AdapterBridge.checkpointGood_good0
#print axioms ExactMajority.Phase3Assembly.Slot3AdapterBridge.rows_to_afterMass_of_predicateSurface
#print axioms ExactMajority.Phase3Assembly.Slot3AdapterBridge.surfaceOf_hourStart_subset_afterO
#print axioms ExactMajority.Phase3Assembly.Slot3AdapterBridge.surfaceOf_hourStart_subset_afterPhi
#print axioms ExactMajority.Phase3Assembly.Slot3AdapterBridge.clockCutHourLen_h13_le
#print axioms ExactMajority.Phase3Assembly.Slot3AdapterBridge.clockCutHourLen_h16_lo_of_cut_arith
#print axioms ExactMajority.Phase3Assembly.Slot3AdapterBridge.clockCutHourLen_h16_hi_of_double_phi_inside
#print axioms ExactMajority.Phase3Assembly.Slot3AdapterBridge.PredicateCheckpointAdapterInput.toAdapter

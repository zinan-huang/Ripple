-- Ripple/PopulationProtocol/ExactMajority/Probability/LateMixedFuel.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFuelLedger
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCompletion
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedPotential

/-!
# N18 row 4: compatible fuel through the mixed Phase-5/6 prefix

The row-2 sample and mass facts are read at the actual completed snapshot.
The ledger is then transported deterministically to the genuine first
homogeneous Phase-6 state.  All probability statements remain under `law init`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateMixedFuel

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping

variable {n : ℕ}

/-- The exact information row 2 must attach to the completed snapshot.
Neither conjunct follows from sampling completion alone. -/
structure EntryFuelCertificate
    (n : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (σ : Sign) (M : ℝ) (Rlo Rhi : ℕ)
    (c : InputCfg n) : Prop where
  class_floors : Phase5To6FuelProducer.TwoClassSampleFloors
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    ell hell Rlo Rhi c
  mass_counts : Phase5To6FuelProducer.Lemma72MassCountBounds
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    σ ell M (LatePotential.fuelFloor n) Rlo Rhi c

/-- Deterministic conversion of the exact row-2 data into the N17 ledger. -/
theorem entryFuelCertificate_ledger
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (σ : Sign) (M : ℝ) (Rlo Rhi : ℕ) (c : InputCfg n)
    (h : EntryFuelCertificate n ell hell σ M Rlo Rhi c) :
    Phase6FuelLedger.TwoLevelFuelLedger
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (LatePotential.fuelFloor n) c := by
  exact Phase5To6FuelProducer.twoLevelFuelLedger_of_two_class_floors
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    σ ell hell M (LatePotential.fuelFloor n) Rlo Rhi c
    h.class_floors h.mass_counts

/-- The exact `.0687 n` compatible-fuel margin consumed by N17. -/
theorem phaseFiveSix_compatibleFuel_margin
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (σ : Sign) (M : ℝ) (Rlo Rhi : ℕ) (c : InputCfg n)
    (h : EntryFuelCertificate n ell hell σ M Rlo Rhi c) :
    Phase6FuelLedger.TwoLevelFuelLedger
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (LatePotential.fuelFloor n) c ∧
      LatePotential.fuelFloor n ≤
        Phase6FuelLedger.twoReserveFuel
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c ∧
      (687 / 10000 : ℝ) * n ≤
        (Phase6FuelLedger.twoReserveFuel
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c : ℝ) := by
  have hledger := entryFuelCertificate_ledger ell hell σ M Rlo Rhi c h
  have hfloor := Phase6FuelLedger.twoLevelFuelLedger_union_floor
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    ell hell (LatePotential.fuelFloor n) c hledger
  have hfloorReal :
      (687 / 10000 : ℝ) * n ≤
        (Phase6FuelLedger.twoReserveFuel
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) ell c : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hfloor)
  exact ⟨hledger, hfloor, hfloorReal⟩

/-! ## Genuine all-Phase-6 stopping time -/

/-- Exact homogeneous Phase 6, not merely a retrospective selected time. -/
def allPhaseSix (c : InputCfg n) : Prop :=
  ∀ a ∈ c, a.phase.val = 6

/-- First actual homogeneous Phase-6 configuration. -/
def homogeneousSixStart (init : InputCfg n) : InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init allPhaseSix

theorem homogeneousSixStart_isStoppingTime (init : InputCfg n) :
    IsStoppingTime
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
      (homogeneousSixStart init) :=
  TraceDrain.exitTime_isStoppingTime init allPhaseSix

theorem homogeneousSixStart_past (init : InputCfg n) :
    PairLogPastTime (homogeneousSixStart init) :=
  exitTime_pairLogPastTime init allPhaseSix

/-- The timer/epidemic input needed by row 4.  It is a prefix property: every
source state before the first homogeneous-six hit is exactly mixed 5/6. -/
structure MixedFiveSixPrefix
    (init : InputCfg n) (ω : InputLog n) (u v : ℕ) : Prop where
  six_start : homogeneousSixStart init ω = (v : WithTop ℕ)
  completion_le : u ≤ v
  source_window : ∀ k, u ≤ k → k < v →
    LateMixedFuelLedger.MixedFiveSixWin n (trace init ω k)

theorem MixedFiveSixPrefix.endpoint_phase_six
    {init : InputCfg n} {ω : InputLog n} {u v : ℕ}
    (h : MixedFiveSixPrefix init ω u v) :
    allPhaseSix (trace init ω v) := by
  have hfirst :=
    (exitTime_eq_iff_firstHit init allPhaseSix ω v).mp
      (by simpa only [homogeneousSixStart] using h.six_start)
  exact hfirst.1

/-! ## Deterministic transport along the actual pair log -/

private theorem applyDraw_preserves
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (c : InputCfg n)
    (hwin : LateMixedFuelLedger.MixedFiveSixWin n c)
    (hledger : Phase6FuelLedger.TwoLevelFuelLedger
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (LatePotential.fuelFloor n) c)
    (hsampled : ReserveSampling.ReserveSampled
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) c)
    (d : Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :
    Phase6FuelLedger.TwoLevelFuelLedger
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (LatePotential.fuelFloor n) (applyDraw c d) ∧
      ReserveSampling.ReserveSampled
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        (applyDraw c d) := by
  cases d with
  | none => exact ⟨hledger, hsampled⟩
  | some pair =>
      change
        Phase6FuelLedger.TwoLevelFuelLedger
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
            ell (LatePotential.fuelFloor n)
            (Protocol.stepOrSelf
              (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256)
              c pair.1.1 pair.2.1) ∧
          ReserveSampling.ReserveSampled
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
            (Protocol.stepOrSelf
              (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256)
              c pair.1.1 pair.2.1)
      exact LateMixedFuelLedger.mixedFiveSix_step_preserves
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell hell (LatePotential.fuelFloor n) n c
        hwin hledger hsampled pair.1.1 pair.2.1

/-- Ledger and sample lock survive every source state in the mixed prefix. -/
theorem phaseFiveSix_compatibleFuel_preserved
    (init : InputCfg n) (ω : InputLog n) (u v : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (huv : u ≤ v)
    (hwindow : ∀ k, u ≤ k → k < v →
      LateMixedFuelLedger.MixedFiveSixWin n (trace init ω k))
    (hledger : Phase6FuelLedger.TwoLevelFuelLedger
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (LatePotential.fuelFloor n) (trace init ω u))
    (hsampled : ReserveSampling.ReserveSampled
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      (trace init ω u)) :
    Phase6FuelLedger.TwoLevelFuelLedger
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (LatePotential.fuelFloor n) (trace init ω v) ∧
      ReserveSampling.ReserveSampled
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        (trace init ω v) := by
  revert hwindow
  induction v, huv using Nat.le_induction with
  | base =>
      intro _
      exact ⟨hledger, hsampled⟩
  | succ v huv ih =>
      intro hwindow
      have hprevious := ih (fun k huk hkv => hwindow k huk (by omega))
      have hsource := hwindow v huv (by omega)
      rw [trace_succ]
      exact applyDraw_preserves ell hell (trace init ω v)
        hsource hprevious.1 hprevious.2 (ω (v + 1))

/-- Row-4 output package.  Its endpoint fields match N17 literally. -/
structure CompatibleFuelReceipt
    (init : InputCfg n) (ω : InputLog n)
    (a four five u v : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (σ : Sign) (M : ℝ) (Rlo Rhi : ℕ) : Prop where
  completion : LateSamplingCompletion.CompletionReceipt
    init ω a four five u
      (EntryFuelCertificate n ell hell σ M Rlo Rhi)
  mixed_path : MixedFiveSixPrefix init ω u v
  population : (trace init ω v).card = n
  phase_six : ∀ b ∈ trace init ω v, b.phase.val = 6
  ledger : Phase6FuelLedger.TwoLevelFuelLedger
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    ell (LatePotential.fuelFloor n) (trace init ω v)
  sampled : ReserveSampling.ReserveSampled
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    (trace init ω v)
  natural_floor : LatePotential.fuelFloor n ≤
    Phase6FuelLedger.twoReserveFuel
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (trace init ω v)
  real_floor : (687 / 10000 : ℝ) * n ≤
    (Phase6FuelLedger.twoReserveFuel
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (trace init ω v) : ℝ)

/-- Assemble row 4 from the row-3 completion receipt, the exact row-2 snapshot
certificate, and the timer/epidemic mixed-prefix certificate. -/
theorem compatibleFuelReceipt_of_completion
    (init : InputCfg n) (ω : InputLog n)
    (a four five u v : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (σ : Sign) (M : ℝ) (Rlo Rhi : ℕ)
    (hcompletion : LateSamplingCompletion.CompletionReceipt
      init ω a four five u
        (EntryFuelCertificate n ell hell σ M Rlo Rhi))
    (hmixed : MixedFiveSixPrefix init ω u v) :
    CompatibleFuelReceipt init ω a four five u v
      ell hell σ M Rlo Rhi := by
  have hentry := entryFuelCertificate_ledger
    ell hell σ M Rlo Rhi (trace init ω u) hcompletion.snapshot
  have htransport := phaseFiveSix_compatibleFuel_preserved
    init ω u v ell hell hmixed.completion_le hmixed.source_window
    hentry hcompletion.complete.sampled
  have hpopulation : (trace init ω v).card = n :=
    (Protocol.reachable_card_eq
      (trace_reachable init ω hmixed.completion_le)).trans
        hcompletion.complete.population
  have hphase := hmixed.endpoint_phase_six
  have hfloor := Phase6FuelLedger.twoLevelFuelLedger_union_floor
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    ell hell (LatePotential.fuelFloor n) (trace init ω v) htransport.1
  have hfloorReal :
      (687 / 10000 : ℝ) * n ≤
        (Phase6FuelLedger.twoReserveFuel
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          ell (trace init ω v) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hfloor)
  exact
    ⟨hcompletion, hmixed, hpopulation, hphase,
      htransport.1, htransport.2, hfloor, hfloorReal⟩

/-- The receipt exposes exactly the N17 shallow-potential drift theorem. -/
theorem compatibleFuelReceipt_drift
    (hn : 2 ≤ n)
    {init : InputCfg n} {ω : InputLog n}
    {a four five u v : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {σ : Sign} {M : ℝ} {Rlo Rhi : ℕ}
    (h : CompatibleFuelReceipt init ω a four five u v
      ell hell σ M Rlo Rhi) :
    (∫ c', (LatePotential.shallowLargePotential ell.val c' : ℝ) ∂
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel
          (trace init ω v)) ≤
      (1 - (43281 : ℝ) / (320000 * ((n : ℝ) - 1))) *
        LatePotential.shallowLargePotential ell.val (trace init ω v) := by
  exact LatePotential.shallow_large_potential_kernel_drift
    n hn ell hell (trace init ω v) h.population h.phase_six h.ledger

/-! ## Original-law failure accounting -/

/-- Failure to produce the row-4 receipt. -/
def compatibleFuelFailure
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (σ : Sign) (M : ℝ) (Rlo Rhi : ℕ) : Set (InputLog n) :=
  {ω | ¬ ∃ a four five u v,
    CompatibleFuelReceipt init ω a four five u v
      ell hell σ M Rlo Rhi}

/-- Original-law row-4 tail.  `hcompletion` is the future row-2 headline
attached to the completion receipt; `hmixed` is the future timer/epidemic
prefix producer.  Both are unconditioned implications outside explicit failure
sets. -/
theorem law_compatibleFuelFailure_tail
    (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (σ : Sign) (M : ℝ) (Rlo Rhi : ℕ)
    (rowTwoFailure mixedFailure : Set (InputLog n))
    (εRow εMixed : ℝ≥0∞)
    (hrow : law init rowTwoFailure ≤ εRow)
    (hmixedTail : law init mixedFailure ≤ εMixed)
    (hcompletion : ∀ ω,
      ω ∉ LateSamplingCompletion.completionFailure init n →
      ω ∉ rowTwoFailure →
      ∃ a four five u,
        LateSamplingCompletion.CompletionReceipt
          init ω a four five u
            (EntryFuelCertificate n ell hell σ M Rlo Rhi))
    (hmixed : ∀ ω a four five u,
      ω ∉ mixedFailure →
      LateSamplingCompletion.CompletionReceipt
          init ω a four five u
            (EntryFuelCertificate n ell hell σ M Rlo Rhi) →
      ∃ v, MixedFiveSixPrefix init ω u v) :
    law init (compatibleFuelFailure init ell hell σ M Rlo Rhi) ≤
      ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ))) +
        εRow + εMixed := by
  have hsubset :
      compatibleFuelFailure init ell hell σ M Rlo Rhi ⊆
        (LateSamplingCompletion.completionFailure init n ∪ rowTwoFailure) ∪
          mixedFailure := by
    intro ω hbad
    by_contra hout
    have hcompletionNot :
        ω ∉ LateSamplingCompletion.completionFailure init n := by
      intro hmem
      exact hout (Or.inl (Or.inl hmem))
    have hrowNot : ω ∉ rowTwoFailure := by
      intro hmem
      exact hout (Or.inl (Or.inr hmem))
    have hmixedNot : ω ∉ mixedFailure := by
      intro hmem
      exact hout (Or.inr hmem)
    rcases hcompletion ω hcompletionNot hrowNot with
      ⟨a, four, five, u, hreceipt⟩
    rcases hmixed ω a four five u hmixedNot hreceipt with
      ⟨v, hpath⟩
    change ¬ ∃ a four five u v,
      CompatibleFuelReceipt init ω a four five u v
        ell hell σ M Rlo Rhi at hbad
    exact hbad
      ⟨a, four, five, u, v,
        compatibleFuelReceipt_of_completion
          init ω a four five u v ell hell σ M Rlo Rhi hreceipt hpath⟩
  calc
    law init (compatibleFuelFailure init ell hell σ M Rlo Rhi)
        ≤ law init
            ((LateSamplingCompletion.completionFailure init n ∪ rowTwoFailure) ∪
              mixedFailure) := measure_mono hsubset
    _ ≤ law init
          (LateSamplingCompletion.completionFailure init n ∪ rowTwoFailure) +
        law init mixedFailure := measure_union_le _ _
    _ ≤ (law init (LateSamplingCompletion.completionFailure init n) +
          law init rowTwoFailure) + law init mixedFailure := by
            exact add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal
            (Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ))) + εRow) +
          εMixed := by
            exact add_le_add
              (add_le_add
                (LateSamplingCompletion.law_completion_failure_tail init hn)
                hrow)
              hmixedTail
    _ = ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ))) +
        εRow + εMixed := rfl

end Ripple.PopulationProtocol.ExactMajority.LateMixedFuel

end

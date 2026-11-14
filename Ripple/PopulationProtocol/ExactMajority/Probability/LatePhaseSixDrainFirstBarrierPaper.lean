-- Ripple/PopulationProtocol/ExactMajority/Probability/LatePhaseSixDrainFirstBarrierPaper.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LatePhaseSixDrainPaperNumerics
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSharpPotentialNumerics
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6TwoLevelFuelSurvival
import Ripple.PopulationProtocol.ExactMajority.Probability.DriftSurvival
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoThresholds
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceEpidemics

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal NNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.LatePhaseSixDrainFirstBarrierPaper

open TimeTheorem PairLog TraceDrain PhaseOneDrainStopping
open LatePhaseSixDrainPaperNumerics
open LateMixedFuel LateSharpPotentialNumerics

variable {n : ℕ}

abbrev PhaseSixDrainReady
    (n : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (c : InputCfg n) : Prop :=
  Phase6TwoLevelFuelSurvival.Phase6TwoLevelReady
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    n ell (LatePotential.fuelFloor n) c

/-- The first Phase-7 appearance is a successful absorbing barrier for the
standalone drain calculation. -/
def SomeSeven (c : InputCfg n) : Prop :=
  StageEventSpec.someGE (n := n) 7 c

def phaseSixCarrier
    (n : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (c : InputCfg n) : Prop :=
  PhaseSixDrainReady n ell c ∨ SomeSeven c

open Classical in
/-- Potential used by the killed first-barrier chain.  It is zero once the
Phase-7 barrier has appeared. -/
def phaseSixBarrierPotential
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (c : InputCfg n) : ℕ :=
  if SomeSeven c then 0 else LatePotential.shallowLargePotential ell.val c

private theorem shallowLargePotential_le_card_pow
    (ell : ℕ) (c : InputCfg n) :
    LatePotential.shallowLargePotential ell c ≤ c.card * 128 ^ ell := by
  let f : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 → ℕ :=
    fun a => if a.role = .main then
      match a.bias with
      | .zero => 0
      | .dyadic _ j => if j.val < ell then 128 ^ (ell - j.val - 1) else 0
    else 0
  have hbound : ∀ a ∈ c, f a ≤ 128 ^ ell := by
    intro a ha
    by_cases hm : a.role = .main
    · cases hb : a.bias with
      | zero => simp [f, hm, hb]
      | dyadic sigma j =>
          by_cases hj : j.val < ell
          · have hexp : ell - j.val - 1 ≤ ell := by omega
            simpa only [f, if_pos hm, hb, if_pos hj] using
              (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 128) hexp)
          · simp [f, hm, hb, hj]
    · simp [f, hm]
  have hsum : ∀ d : InputCfg n, (∀ a ∈ d, f a ≤ 128 ^ ell) →
      (d.map f).sum ≤ d.card * 128 ^ ell := by
    intro d
    induction d using Multiset.induction_on with
    | empty => intro _; simp
    | cons a d ih =>
        intro hd
        have ha := hd a (Multiset.mem_cons_self a d)
        have ht := ih (fun b hb => hd b (Multiset.mem_cons_of_mem hb))
        calc
          ((a ::ₘ d).map f).sum = f a + (d.map f).sum := by simp
          _ ≤ 128 ^ ell + d.card * 128 ^ ell := Nat.add_le_add ha ht
          _ = (a ::ₘ d).card * 128 ^ ell := by
            simp only [Multiset.card_cons, Nat.succ_mul]
            omega
  change (c.map f).sum ≤ c.card * 128 ^ ell
  exact hsum c hbound

private theorem shallowLargePotential_integrable
    (ell : ℕ) (c : InputCfg n) (hcard : c.card = n) :
    Integrable
      (fun d : InputCfg n =>
        (LatePotential.shallowLargePotential ell d : ℝ))
      ((NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c) := by
  let B : ℝ := ((n * 128 ^ ell : ℕ) : ℝ)
  have hmeas : AEStronglyMeasurable
      (fun d : InputCfg n =>
        (LatePotential.shallowLargePotential ell d : ℝ))
      ((NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hconst : Integrable (fun _ : InputCfg n => B)
      ((NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c) :=
    integrable_const B
  refine hconst.mono' hmeas ?_
  have hcardAE : ∀ᵐ d ∂
      ((NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c),
      d.card = n := by
    rw [MeasureTheory.ae_iff]
    change
      ((NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).stepDistOrSelf c).toMeasure
        {d : InputCfg n | ¬ d.card = n} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff
      (p := (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).stepDistOrSelf c)
      (s := {d : InputCfg n | ¬ d.card = n})
      (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
    intro d hd hbad
    exact hbad
      ((Protocol.stepDistOrSelf_support_card_eq
        (NonuniformMajority
          (PhaseThreeModel.Numeric.hourIndex n) 256) c d hd).trans hcard)
  filter_upwards [hcardAE] with d hd
  have hnat := shallowLargePotential_le_card_pow ell d
  rw [hd] at hnat
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact Nat.cast_le.mpr hnat

/-- N17 in the ENNReal form required by `DriftSurvival`. -/
theorem nSeventeen_lintegral_drift
    (hn : 2 ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (c : InputCfg n) (hc : PhaseSixDrainReady n ell c) :
    (∫⁻ d, (LatePotential.shallowLargePotential ell.val d : ℝ≥0∞) ∂
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c) ≤
      phaseSixDrainRate n *
        (LatePotential.shallowLargePotential ell.val c : ℝ≥0∞) := by
  have hreal := LatePotential.shallow_large_potential_kernel_drift
    n hn ell hell c hc.win.1 hc.win.2 hc.ledger
  have hint := shallowLargePotential_integrable ell.val c hc.win.1
  have hnonneg : 0 ≤ᵐ[
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c]
      (fun d : InputCfg n =>
        (LatePotential.shallowLargePotential ell.val d : ℝ)) :=
    ae_of_all _ fun _ => Nat.cast_nonneg _
  have heq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg
  have heq' : (∫⁻ d, (LatePotential.shallowLargePotential ell.val d : ℝ≥0∞) ∂
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c) =
      ENNReal.ofReal (∫ d : InputCfg n,
        (LatePotential.shallowLargePotential ell.val d : ℝ) ∂
        (NonuniformMajority
          (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c) := by
    rw [heq]
    congr 1
    funext d
    rw [ENNReal.ofReal_natCast]
  rw [heq']
  have hrate0 := phaseSixDrainRateReal_nonneg hn
  have hright :
      ENNReal.ofReal
          (phaseSixDrainRateReal n *
            (LatePotential.shallowLargePotential ell.val c : ℝ)) =
        phaseSixDrainRate n *
          (LatePotential.shallowLargePotential ell.val c : ℝ≥0∞) := by
    unfold phaseSixDrainRate
    rw [ENNReal.ofReal_mul hrate0, ENNReal.ofReal_natCast]
  rw [← hright]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem someSeven_of_support
    (c d : InputCfg n) (hc : SomeSeven c)
    (hd : d ∈ ((NonuniformMajority
      (PhaseThreeModel.Numeric.hourIndex n) 256).stepDistOrSelf c).support) :
    SomeSeven d := by
  have hcpos : 0 < AdvanceEpidemics.geCount
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 7 c := by
    simpa [SomeSeven, AdvanceEpidemics.geCount, AdvanceEpidemics.geP] using
      (Multiset.countP_pos.mpr hc)
  have hmono := AdvanceEpidemics.geCount_ge_monotone
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    7 1 c d (by omega) hd
  have hdpos : 0 < AdvanceEpidemics.geCount
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 7 d := by omega
  simpa [SomeSeven, AdvanceEpidemics.geCount, AdvanceEpidemics.geP] using
    (Multiset.countP_pos.mp hdpos)

private theorem ready_of_support_of_not_seven
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (c d : InputCfg n) (hc : PhaseSixDrainReady n ell c)
    (hd : d ∈ ((NonuniformMajority
      (PhaseThreeModel.Numeric.hourIndex n) 256).stepDistOrSelf c).support)
    (hseven : ¬ SomeSeven d) :
    PhaseSixDrainReady n ell d := by
  let P := NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256
  have hcard : d.card = n :=
    (Protocol.stepDistOrSelf_support_card_eq P c d hd).trans hc.win.1
  have hreach := Protocol.stepDistOrSelf_support_reachable P c d hd
  have hlower := phase_lower_reachable 6 c d hreach
    (fun a ha => (hc.win.2 a ha).ge)
  have hphase : ∀ a ∈ d, a.phase.val = 6 := by
    intro a ha
    have hlo := hlower a ha
    have hhi : a.phase.val < 7 := by
      by_contra h
      exact hseven ⟨a, ha, by omega⟩
    omega
  have hzero :=
    Phase6FuelLedger.transitionKernel_not_twoLevelFuelLedger_eq_zero
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell hell (LatePotential.fuelFloor n) n c hc.win hc.ledger
  change (P.stepDistOrSelf c).toMeasure
      {x | ¬ Phase6FuelLedger.TwoLevelFuelLedger
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (LatePotential.fuelFloor n) x} = 0 at hzero
  rw [PMF.toMeasure_apply_eq_zero_iff
      (p := P.stepDistOrSelf c)
      (s := {x | ¬ Phase6FuelLedger.TwoLevelFuelLedger
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        ell (LatePotential.fuelFloor n) x})
      (DiscreteMeasurableSpace.forall_measurableSet _),
    Set.disjoint_left] at hzero
  have hledger : Phase6FuelLedger.TwoLevelFuelLedger
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (LatePotential.fuelFloor n) d := by
    by_contra hbad
    exact hzero hd hbad
  exact ⟨⟨hcard, hphase⟩, hledger⟩

/-- The carrier is genuinely closed: a step either stays in homogeneous
Phase 6 with the ledger, or has already crossed the Phase-7 barrier. -/
theorem phaseSixCarrier_escape_zero
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (c : InputCfg n) (hc : phaseSixCarrier n ell c) :
    (NonuniformMajority
      (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c
        {d | ¬ phaseSixCarrier n ell d} = 0 := by
  let P := NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256
  change (P.stepDistOrSelf c).toMeasure
      {d | ¬ phaseSixCarrier n ell d} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff
      (p := P.stepDistOrSelf c)
      (s := {d | ¬ phaseSixCarrier n ell d})
      (DiscreteMeasurableSpace.forall_measurableSet _),
    Set.disjoint_left]
  intro d hd hbad
  rcases hc with hready | hseven
  · by_cases hdseven : SomeSeven d
    · exact hbad (Or.inr hdseven)
    · exact hbad (Or.inl
        (ready_of_support_of_not_seven ell hell c d hready hd hdseven))
  · exact hbad (Or.inr (someSeven_of_support c d hseven hd))

private theorem transitionKernel_not_someSeven_eq_zero
    (c : InputCfg n) (hc : SomeSeven c) :
    (NonuniformMajority
      (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c
        {d | ¬ SomeSeven d} = 0 := by
  let P := NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256
  change (P.stepDistOrSelf c).toMeasure {d | ¬ SomeSeven d} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff
      (p := P.stepDistOrSelf c)
      (s := {d | ¬ SomeSeven d})
      (DiscreteMeasurableSpace.forall_measurableSet _),
    Set.disjoint_left]
  intro d hd hbad
  exact hbad (someSeven_of_support c d hc hd)

/-- Multiplicative drift on the closed first-barrier carrier. -/
theorem phaseSixCarrier_lintegral_drift
    (hn : 2 ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (c : InputCfg n) (hc : phaseSixCarrier n ell c) :
    (∫⁻ d, (phaseSixBarrierPotential ell d : ℝ≥0∞) ∂
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c) ≤
      phaseSixDrainRate n * (phaseSixBarrierPotential ell c : ℝ≥0∞) := by
  rcases hc with hready | hseven
  · have hnot : ¬ SomeSeven c := by
      rintro ⟨a, ha, hge⟩
      have heq := hready.win.2 a ha
      omega
    calc
      (∫⁻ d, (phaseSixBarrierPotential ell d : ℝ≥0∞) ∂
          (NonuniformMajority
            (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c) ≤
        ∫⁻ d, (LatePotential.shallowLargePotential ell.val d : ℝ≥0∞) ∂
          (NonuniformMajority
            (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c := by
          apply lintegral_mono
          intro d
          by_cases h : SomeSeven d <;> simp [phaseSixBarrierPotential, h]
      _ ≤ phaseSixDrainRate n *
          (LatePotential.shallowLargePotential ell.val c : ℝ≥0∞) :=
        nSeventeen_lintegral_drift hn ell hell c hready
      _ = phaseSixDrainRate n *
          (phaseSixBarrierPotential ell c : ℝ≥0∞) := by
        simp [phaseSixBarrierPotential, hnot]
  · have hzero := transitionKernel_not_someSeven_eq_zero c hseven
    have hae : ∀ᵐ d ∂
        (NonuniformMajority
          (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c,
        SomeSeven d := by
      rw [MeasureTheory.ae_iff]
      simpa only [Set.mem_setOf_eq] using hzero
    have hlhs :
        (∫⁻ d, (phaseSixBarrierPotential ell d : ℝ≥0∞) ∂
          (NonuniformMajority
            (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hae] with d hd
      simp [phaseSixBarrierPotential, hd]
    rw [hlhs]
    simp [phaseSixBarrierPotential, hseven]

/-- Fixed-start drain tail.  Phase-7 appearance is success, so no timer or
clock-depletion charge occurs in this theorem. -/
theorem phaseSix_fixed_start_drain_tail
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (c : InputCfg n) (hready : PhaseSixDrainReady n ell c)
    (hsharp :
      (LatePotential.shallowLargePotential ell.val c : ℝ) <
        (1 / 1000 : ℝ) * Real.rpow (n : ℝ) (114 / 100 : ℝ)) :
    ((NonuniformMajority
      (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel ^
        phaseSixDrainHorizon n) c
      {d | ¬ SomeSeven d ∧
        LatePotential.shallowLargePotential ell.val d ≠ 0} ≤
      phaseSixDrainBudget n := by
  let K := (NonuniformMajority
    (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel
  let Inv : InputCfg n → Prop := phaseSixCarrier n ell
  let Phi : InputCfg n → ℕ := phaseSixBarrierPotential ell
  have hnlarge : 2 ≤ n := by
    have := (time_population_bounds hn).2
    omega
  have hdrift : ∀ x, Inv x →
      ∫⁻ y, (Phi y : ℝ≥0∞) ∂K x ≤
        phaseSixDrainRate n * (Phi x : ℝ≥0∞) := by
    intro x hx
    exact phaseSixCarrier_lintegral_drift hnlarge ell hell x hx
  have hesc : ∀ x, Inv x → K x {y | ¬ Inv y} ≤ (0 : ℝ≥0∞) := by
    intro x hx
    exact le_of_eq (phaseSixCarrier_escape_zero ell hell x hx)
  have htail := DriftSurvival.real_tail_le_drift_plus_escape
    K Inv Phi (phaseSixDrainRate n) hdrift 0 hesc
    (phaseSixDrainHorizon n) c (Or.inl hready)
  have hnot : ¬ SomeSeven c := by
    rintro ⟨a, ha, hge⟩
    have heq := hready.win.2 a ha
    omega
  have hscalar := phaseSixDrain_scalar_ennreal hn hsharp
  calc
    (K ^ phaseSixDrainHorizon n) c
        {d | ¬ SomeSeven d ∧
          LatePotential.shallowLargePotential ell.val d ≠ 0} ≤
      (K ^ phaseSixDrainHorizon n) c
        {d | ¬ (Inv d ∧ Phi d = 0)} := by
          apply measure_mono
          rintro d ⟨hdseven, hdpos⟩ hpost
          apply hdpos
          simpa [Phi, phaseSixBarrierPotential, hdseven] using hpost.2
    _ ≤ phaseSixDrainRate n ^ phaseSixDrainHorizon n *
          (Phi c : ℝ≥0∞) +
        (phaseSixDrainHorizon n : ℝ≥0∞) * 0 := htail
    _ = phaseSixDrainRate n ^ phaseSixDrainHorizon n *
          (LatePotential.shallowLargePotential ell.val c : ℝ≥0∞) := by
        simp [Phi, phaseSixBarrierPotential, hnot]
    _ ≤ phaseSixDrainBudget n := hscalar

/-- The exact start predicate selected on the homogeneous-six stopping fibre. -/
structure PhaseSixSharpConfig
    (n : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (c : InputCfg n) : Prop where
  ready : PhaseSixDrainReady n ell c
  paper_bound :
    (LatePotential.shallowLargePotential ell.val c : ℝ) <
      (1 / 1000 : ℝ) * Real.rpow (n : ℝ) (114 / 100 : ℝ)

/-- `LateSharpInitialPotential` supplies the sharp field at the genuine homogeneous Phase-6 start. -/
theorem phaseSixSharpConfig_of_receipts
    (hn : 2 ≤ n)
    {init : InputCfg n} {omega : InputLog n}
    {allStart four completed homogeneous M C R : ℕ} {sigma : Sign}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hpath : LateF6OriginalLaw.Prefix
      init omega allStart four completed)
    (hmixed : LateMixedFuel.MixedFiveSixPrefix
      init omega completed homogeneous)
    (hread : LateStrengthening.LateSeedReadout
      init M ell.val sigma (trace init omega four))
    (hdensity : LateSamplingStrongSeedReceipt.StrongSeedDensity n M C R)
    (hready : PhaseSixDrainReady n ell
      (trace init omega homogeneous)) :
    PhaseSixSharpConfig n ell (trace init omega homogeneous) :=
  ⟨hready,
    LateSharpPotentialNumerics.homogeneous_largePotential_lt_paper_power
      hn hpath hmixed hread hdensity⟩

/-- Original-law drain failure at the genuine homogeneous-six stopping time. -/
def phaseSixDrainFailure
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    Set (InputLog n) :=
  {omega | ∃ homogeneous : ℕ,
    LateMixedFuel.homogeneousSixStart init omega =
      (homogeneous : WithTop ℕ) ∧
    PhaseSixSharpConfig n ell (trace init omega homogeneous) ∧
    ¬ SomeSeven
      (trace init omega (homogeneous + phaseSixDrainHorizon n)) ∧
    LatePotential.shallowLargePotential ell.val
      (trace init omega (homogeneous + phaseSixDrainHorizon n)) ≠ 0}

theorem phaseSixDrainFailure_measurable
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    MeasurableSet (phaseSixDrainFailure init ell hell) := by
  have heq : phaseSixDrainFailure init ell hell =
      ⋃ homogeneous : ℕ,
        {omega | LateMixedFuel.homogeneousSixStart init omega =
          (homogeneous : WithTop ℕ)} ∩
        ({omega | PhaseSixSharpConfig n ell
          (trace init omega homogeneous)} ∩
        {omega | ¬ SomeSeven
          (trace init omega (homogeneous + phaseSixDrainHorizon n)) ∧
          LatePotential.shallowLargePotential ell.val
            (trace init omega
              (homogeneous + phaseSixDrainHorizon n)) ≠ 0}) := by
    ext omega
    simp only [phaseSixDrainFailure, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_inter_iff]
  rw [heq]
  apply MeasurableSet.iUnion
  intro homogeneous
  have htime : MeasurableSet
      {omega | LateMixedFuel.homogeneousSixStart init omega =
        (homogeneous : WithTop ℕ)} :=
    (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).le
      homogeneous _ ((LateMixedFuel.homogeneousSixStart_past init) homogeneous)
  have hstart : MeasurableSet
      {omega | PhaseSixSharpConfig n ell
        (trace init omega homogeneous)} :=
    (Set.to_countable
      {c : InputCfg n | PhaseSixSharpConfig n ell c}).measurableSet.preimage
        ((measurable_pi_apply homogeneous).comp (measurable_trace init))
  have hend : MeasurableSet
      {omega | ¬ SomeSeven
          (trace init omega (homogeneous + phaseSixDrainHorizon n)) ∧
        LatePotential.shallowLargePotential ell.val
          (trace init omega
            (homogeneous + phaseSixDrainHorizon n)) ≠ 0} :=
    (Set.to_countable
      {c : InputCfg n | ¬ SomeSeven c ∧
        LatePotential.shallowLargePotential ell.val c ≠ 0}).measurableSet.preimage
      ((measurable_pi_apply
        (homogeneous + phaseSixDrainHorizon n)).comp
          (measurable_trace init))
  exact htime.inter (hstart.inter hend)

/-- Sum the fixed-start theorem over the genuine homogeneous-six fibres.
The sharp scalar estimate is already inside `PhaseSixSharpConfig`. -/
theorem law_phaseSixDrainFailure_tail
    (init : InputCfg n) (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    law init (phaseSixDrainFailure init ell hell) ≤
      phaseSixDrainBudget n := by
  let sigma := LateMixedFuel.homogeneousSixStart init
  let bad : Set (InputCfg n) :=
    {c | ¬ SomeSeven c ∧
      LatePotential.shallowLargePotential ell.val c ≠ 0}
  let epsilon : ℝ≥0∞ := phaseSixDrainBudget n
  apply PairLog.genuine_seed_splice
    (law init) sigma (phaseSixDrainFailure init ell hell) epsilon
    (phaseSixDrainFailure_measurable init ell hell)
    (fun homogeneous =>
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).le
        homogeneous _ ((LateMixedFuel.homogeneousSixStart_past init) homogeneous))
  · intro omega hbad
    rcases hbad with ⟨homogeneous, htime, _⟩
    show LateMixedFuel.homogeneousSixStart init omega ≠ ⊤
    rw [htime]
    exact WithTop.coe_ne_top
  · intro homogeneous
    have hsigma := (LateMixedFuel.homogeneousSixStart_past init) homogeneous
    rw [pairLogFiltration_eq_comap] at hsigma
    obtain ⟨Aσ, _, hAσ⟩ := hsigma
    let A : Set ((k : Finset.Iic homogeneous) →
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
      {p | p ∈ Aσ ∧
        PhaseSixSharpConfig n ell (prefixCfg init homogeneous p)}
    have hmem (omega : InputLog n) :
        frestrictLe (π := fun _ : ℕ =>
          Draw (PhaseThreeModel.Numeric.hourIndex n) 256)
          homogeneous omega ∈ Aσ ↔
        sigma omega = (homogeneous : WithTop ℕ) := by
      change omega ∈
          (frestrictLe (π := fun _ : ℕ =>
            Draw (PhaseThreeModel.Numeric.hourIndex n) 256)
            homogeneous) ⁻¹' Aσ ↔
        omega ∈ {omega | sigma omega = (homogeneous : WithTop ℕ)}
      rw [hAσ]
    have hlocal := PhaseTwoThresholds.recorded_prefix_endpoint_bound
      init homogeneous (phaseSixDrainHorizon n) A bad epsilon
      (fun p hp => by
        simpa [bad, epsilon] using
          (phaseSix_fixed_start_drain_tail hn ell hell
            (prefixCfg init homogeneous p) hp.2.ready hp.2.paper_bound))
    calc
      law init
          (phaseSixDrainFailure init ell hell ∩
            {omega | sigma omega = (homogeneous : WithTop ℕ)}) ≤
        law init
          {omega |
            frestrictLe (π := fun _ : ℕ =>
              Draw (PhaseThreeModel.Numeric.hourIndex n) 256)
              homogeneous omega ∈ A ∧
            trace init omega
              (homogeneous + phaseSixDrainHorizon n) ∈ bad} := by
          apply measure_mono
          rintro omega ⟨⟨start, hstart, hsharp, hseven, hpot⟩, htime⟩
          have hstartEq : start = homogeneous :=
            WithTop.coe_injective (hstart.symm.trans htime)
          subst start
          have hpast : frestrictLe (π := fun _ : ℕ =>
              Draw (PhaseThreeModel.Numeric.hourIndex n) 256)
              homogeneous omega ∈ Aσ :=
            (hmem omega).mpr htime
          change PhaseSixSharpConfig n ell
            (prefixCfg init homogeneous
              (frestrictLe (π := fun _ : ℕ =>
                Draw (PhaseThreeModel.Numeric.hourIndex n) 256)
                homogeneous omega)) at hsharp
          exact ⟨⟨hpast, hsharp⟩, hseven, hpot⟩
      _ ≤ epsilon *
          law init
            {omega | frestrictLe (π := fun _ : ℕ =>
              Draw (PhaseThreeModel.Numeric.hourIndex n) 256)
              homogeneous omega ∈ A} := hlocal
      _ ≤ epsilon *
          law init {omega | sigma omega =
            (homogeneous : WithTop ℕ)} := by
        refine mul_le_mul_left' (measure_mono ?_) epsilon
        intro omega0 homega
        exact (hmem omega0).mp homega.1

/-!
THEOREM LIST
* `PhaseSixDrainReady`, `phaseSixCarrier`, `phaseSixBarrierPotential`
* `nSeventeen_lintegral_drift`
* `phaseSixCarrier_escape_zero`, `phaseSixCarrier_lintegral_drift`
* `phaseSix_fixed_start_drain_tail`
* `PhaseSixSharpConfig`, `phaseSixSharpConfig_of_receipts`
* `phaseSixDrainFailure`, `law_phaseSixDrainFailure_tail`

CLOSES
* The generic fixed-start first-barrier argument, now with the paper's
  `23.4` horizon and the sharp initial potential of `LateSharpInitialPotential`.
* A standalone original-law `n^(-2.02)` drain charge.
* The stopping-time splice over genuine homogeneous Phase-6 fibres.
* Phase-7 appearance is treated as success, so timer failure is not hidden in
  the drain budget.

UNFINISHED
* Nothing mathematical in this file.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LatePhaseSixDrainFirstBarrierPaper

end

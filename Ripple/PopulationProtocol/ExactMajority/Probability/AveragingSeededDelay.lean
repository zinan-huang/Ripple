-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingSeededDelay.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingHourStops
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTerminalDebtDeadlines

/-!
# Adapted delays whose length is read at a recorded seed

The delay is evaluated from the actual seed configuration. It is not a fixed
constant on the whole path space. The guard seed <= start makes every finite
fibre measurable using only the past of that fibre, without a separate ordering
assumption. The canonical warmup and potential checkpoints use this construction.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.AveragingSeededDelay

open TimeTheorem PairLog PhaseOneDrain StageEventSpec PhaseThreeClockProducer
open AveragingHourStops AveragingTerminalDebtDeadlines AveragingNumerics

variable {L K n : ℕ}

/-- A finite start plus a nonnegative integer delay observed at a no-later seed. -/
def seededDelay (init : Cfg L K) (σ τ : Ω L K → WithTop ℕ)
    (D : Cfg L K → ℕ) (ω : Ω L K) : WithTop ℕ :=
  WithTop.recTopCoe (C := fun _ : WithTop ℕ => WithTop ℕ) ⊤
    (fun S =>
      WithTop.recTopCoe (C := fun _ : WithTop ℕ => WithTop ℕ) ⊤
        (fun r =>
          if S ≤ r then ((r + D (trace init ω S) : ℕ) : WithTop ℕ) else ⊤)
        (τ ω))
    (σ ω)

theorem seededDelay_eq_iff (init : Cfg L K) (σ τ : Ω L K → WithTop ℕ)
    (D : Cfg L K → ℕ) (ω : Ω L K) (t : ℕ) :
    seededDelay init σ τ D ω = (t : WithTop ℕ) ↔
      ∃ S r : ℕ, σ ω = (S : WithTop ℕ) ∧ τ ω = (r : WithTop ℕ) ∧
        S ≤ r ∧ r + D (trace init ω S) = t := by
  cases hs : σ ω with
  | top =>
      simp [seededDelay, hs]
  | coe S =>
      cases hr : τ ω with
      | top =>
          have hval : seededDelay init σ τ D ω = ⊤ := by
            unfold seededDelay
            rw [hs, hr]
            rfl
          simp [hval, hs, hr]
      | coe r =>
          have hval : seededDelay init σ τ D ω =
              if S ≤ r then ((r + D (trace init ω S) : ℕ) : WithTop ℕ) else ⊤ := by
            unfold seededDelay
            rw [hs, hr]
            rfl
          by_cases hSr : S ≤ r <;>
            simp [hval, hs, hr, hSr] <;> norm_cast

theorem seededDelay_eq_of_eq (init : Cfg L K) (σ τ : Ω L K → WithTop ℕ)
    (D : Cfg L K → ℕ) (ω : Ω L K) (S r : ℕ)
    (hseed : σ ω = (S : WithTop ℕ)) (hstart : τ ω = (r : WithTop ℕ))
    (hSr : S ≤ r) :
    seededDelay init σ τ D ω =
      ((r + D (trace init ω S) : ℕ) : WithTop ℕ) :=
  (seededDelay_eq_iff init σ τ D ω _).mpr
    ⟨S, r, hseed, hstart, hSr, rfl⟩

theorem seededDelay_pastTime (init : Cfg L K) (σ τ : Ω L K → WithTop ℕ)
    (hσ : PairLogPastTime σ) (hτ : PairLogPastTime τ) (D : Cfg L K → ℕ) :
    PairLogPastTime (seededDelay init σ τ D) := by
  intro t
  have hset :
      {ω | seededDelay init σ τ D ω = (t : WithTop ℕ)} =
      ⋃ S : ℕ, ⋃ r : ℕ,
        {ω | S ≤ r ∧ r ≤ t ∧ σ ω = (S : WithTop ℕ) ∧
          τ ω = (r : WithTop ℕ) ∧ r + D (trace init ω S) = t} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [seededDelay_eq_iff]
    constructor
    · rintro ⟨S, r, hs, hr, hSr, ht⟩
      exact ⟨S, r, hSr, by omega, hs, hr, ht⟩
    · rintro ⟨S, r, hSr, _, hs, hr, ht⟩
      exact ⟨S, r, hs, hr, hSr, ht⟩
  rw [hset]
  refine MeasurableSet.iUnion fun S => MeasurableSet.iUnion fun r => ?_
  by_cases hSr : S ≤ r
  · by_cases hrt : r ≤ t
    · have hSt : S ≤ t := hSr.trans hrt
      have hs := (pairLogFiltration L K).mono hSt _ (hσ S)
      have hr := (pairLogFiltration L K).mono hrt _ (hτ r)
      have hdelay : MeasurableSet[pairLogFiltration L K t]
          {ω | r + D (trace init ω S) = t} :=
        (show MeasurableSet {c : Cfg L K | r + D c = t} from
          (Set.to_countable _).measurableSet).preimage
            (measurable_trace_at_of_le init hSt)
      simpa only [hSr, hrt, true_and] using hs.inter (hr.inter hdelay)
    · simp only [hrt, false_and, and_false, Set.setOf_false, MeasurableSet.empty]
  · simp only [hSr, false_and, Set.setOf_false, MeasurableSet.empty]

theorem seededDelay_isStoppingTime (init : Cfg L K) (σ τ : Ω L K → WithTop ℕ)
    (hσ : PairLogPastTime σ) (hτ : PairLogPastTime τ) (D : Cfg L K → ℕ) :
    IsStoppingTime (pairLogFiltration L K) (seededDelay init σ τ D) :=
  isStoppingTime_of_measurableSet_eq (seededDelay_pastTime init σ τ hσ hτ D)

/-- The actual start of the old-potential work after its random-seed warmup. -/
def hourWarmStart (init : InputCfg n) (σ : InputLog n → WithTop ℕ)
    (h : ℕ) : InputLog n → WithTop ℕ :=
  seededDelay init σ (hourStart init σ h)
    (fun c => clockWarmup n (clockCount c))

/-- The actual potential checkpoint after the warmup and potential work. -/
def hourPotentialEnd (init : InputCfg n) (σ : InputLog n → WithTop ℕ)
    (h : ℕ) : InputLog n → WithTop ℕ :=
  seededDelay init σ (hourStart init σ h)
    (fun c => clockWarmup n (clockCount c) + potentialTrials n (timeMainCount c))

theorem hourWarmStart_pastTime (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) (h : ℕ) :
    PairLogPastTime (hourWarmStart init σ h) :=
  seededDelay_pastTime init σ (hourStart init σ h) hσ
    (hourStart_pastTime init σ hσ h) _

theorem hourPotentialEnd_pastTime (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) (h : ℕ) :
    PairLogPastTime (hourPotentialEnd init σ h) :=
  seededDelay_pastTime init σ (hourStart init σ h) hσ
    (hourStart_pastTime init σ hσ h) _

theorem hourWarmStart_clockHistory {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (hc : ClockHistory init ω S T ρ w)
    (σ : InputLog n → WithTop ℕ) (h : ℕ)
    (hseed : σ ω = (S : WithTop ℕ))
    (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
    hourWarmStart init σ h ω =
      ((w.start h + clockWarmup n (clockCount (trace init ω S)) : ℕ) : WithTop ℕ) := by
  have hs := hourStart_clockHistory hc σ h hseed hh
  have hSh : S ≤ w.start h :=
    ((hourStart_eq_iff_of_seed init σ h ω S (w.start h) hseed).mp hs).1
  exact seededDelay_eq_of_eq init σ (hourStart init σ h)
    (fun c => clockWarmup n (clockCount c)) ω S (w.start h) hseed hs hSh

theorem hourPotentialEnd_clockHistory {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (hc : ClockHistory init ω S T ρ w)
    (σ : InputLog n → WithTop ℕ) (h : ℕ)
    (hseed : σ ω = (S : WithTop ℕ))
    (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
    hourPotentialEnd init σ h ω =
      ((w.start h + clockWarmup n (clockCount (trace init ω S)) +
        potentialTrials n (timeMainCount (trace init ω S)) : ℕ) : WithTop ℕ) := by
  have hs := hourStart_clockHistory hc σ h hseed hh
  have hSh : S ≤ w.start h :=
    ((hourStart_eq_iff_of_seed init σ h ω S (w.start h) hseed).mp hs).1
  simpa only [Nat.add_assoc] using
    seededDelay_eq_of_eq init σ (hourStart init σ h)
      (fun c => clockWarmup n (clockCount c) + potentialTrials n (timeMainCount c))
      ω S (w.start h) hseed hs hSh

theorem hourWarmStart_phaseThreeSeed_pastTime (init : InputCfg n) (h : ℕ) :
    PairLogPastTime (hourWarmStart init (seedTime init 3) h) :=
  hourWarmStart_pastTime init (seedTime init 3) (seedTime_pastTime init 3) h

theorem hourPotentialEnd_phaseThreeSeed_pastTime (init : InputCfg n) (h : ℕ) :
    PairLogPastTime (hourPotentialEnd init (seedTime init 3) h) :=
  hourPotentialEnd_pastTime init (seedTime init 3) (seedTime_pastTime init 3) h

theorem hourWarmStart_phaseThreeSeed_clockHistory
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ} {w : ClockTimes init}
    (hc : ClockHistory init ω S T ρ w) (h : ℕ)
    (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
    hourWarmStart init (seedTime init 3) h ω =
      ((w.start h + clockWarmup n (clockCount (trace init ω S)) : ℕ) : WithTop ℕ) :=
  hourWarmStart_clockHistory hc (seedTime init 3) h
    ((seedTime_eq_iff init 3 ω S).mpr hc.entry.first_phase_seed) hh

theorem hourPotentialEnd_phaseThreeSeed_clockHistory
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ} {w : ClockTimes init}
    (hc : ClockHistory init ω S T ρ w) (h : ℕ)
    (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
    hourPotentialEnd init (seedTime init 3) h ω =
      ((w.start h + clockWarmup n (clockCount (trace init ω S)) +
        potentialTrials n (timeMainCount (trace init ω S)) : ℕ) : WithTop ℕ) :=
  hourPotentialEnd_clockHistory hc (seedTime init 3) h
    ((seedTime_eq_iff init 3 ω S).mpr hc.entry.first_phase_seed) hh

end Ripple.PopulationProtocol.ExactMajority.AveragingSeededDelay

end

-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockActivationRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRawLocalRow
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationRoleFloors
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMacroscopicActivation

/-!
# Activation and active-role Core rows on the seed fibre

AsyncEntry already supplies a finite full-activation time. Consequently
the genuine ninety-nine-percent first passage exists on that event with
zero additional error. This does not give the sharp early-mark deadline.

The Main and Clock activation floors follow deterministically from the
observed threshold and SeedProfile's role densities. They hold at every
later virtual time, so neither a cap deadline nor a future no-backup
condition is needed to derive these two Core fields.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationRows

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer
  PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockSeedTails
  PhaseThreeClockActivationSeed PhaseThreeClockRawLocalRow
  PhaseThreeClockActivationRoleFloors PhaseThreeClockMacroscopicActivation

variable {n : ℕ}

def ActivationFirstAt (init : InputCfg n) (ω : InputLog n) (s α : ℕ) : Prop :=
  firstAfter (fun v => Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤
    activeCountL init (virtualLabels init ω v)) s α

def ActiveMainRow (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (w : ClockTimes init) : Prop :=
  ∀ v, w.activation ≤ v → v ≤ w.cap + logWindow n 400 →
    47 * timeMainCount (virtualCfg init ω s) ≤
      48 * activeRoleCountL init (virtualLabels init ω s)
        (virtualLabels init ω v) .main

def ActiveClockRow (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (w : ClockTimes init) : Prop :=
  ∀ v, w.activation ≤ v → v ≤ w.cap + logWindow n 400 →
    23 * clockCount (virtualCfg init ω s) ≤
      24 * activeRoleCountL init (virtualLabels init ω s)
        (virtualLabels init ω v) .clock

theorem seed_role_density (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (hseed : ω ∈ seedPrefix init s) :
    12 * n ≤ 25 * timeMainCount (virtualCfg init ω s) ∧
      6 * n ≤ 25 * clockCount (virtualCfg init ω s) := by
  rw [virtualCfg_eq_trace_at_seedPrefix init ω s hseed]
  have hM := hseed.2.role_good.2.1
  have hC := hseed.2.role_good.2.2.2.1
  have hMR : (12 : ℝ) * (n : ℝ) ≤
      25 * (timeMainCount (trace init ω s) : ℝ) := by
    change (1 - (1 / 25 : ℝ)) * (n : ℝ) / 2 ≤
      (timeMainCount (trace init ω s) : ℝ) at hM
    linarith
  have hCR : (6 : ℝ) * (n : ℝ) ≤
      25 * (clockCount (trace init ω s) : ℝ) := by
    change (1 - (1 / 25 : ℝ)) * (n : ℝ) / 4 ≤
      (clockCount (trace init ω s) : ℝ) at hC
    linarith
  exact ⟨by exact_mod_cast hMR, by exact_mod_cast hCR⟩

/-- All current active-role inequalities are discharged from the seed
profile and the observed macro-activation threshold. -/
theorem active_role_floors_after_activationFirst (init : InputCfg n)
    (ω : InputLog n) (s α : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hα : ActivationFirstAt init ω s α) :
    ∀ v, α ≤ v →
      47 * timeMainCount (virtualCfg init ω s) ≤
        48 * activeRoleCountL init (virtualLabels init ω s)
          (virtualLabels init ω v) .main ∧
      23 * clockCount (virtualCfg init ω s) ≤
        24 * activeRoleCountL init (virtualLabels init ω s)
          (virtualLabels init ω v) .clock := by
  obtain ⟨hM, hC⟩ := seed_role_density init ω s hseed
  exact core_active_role_floors init ω s α
    (seedPrefix_card_eq init ω s hseed) hα.2.1 hM hC

theorem active_role_rows_of_activationFirst (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) (w : ClockTimes init)
    (hseed : ω ∈ seedPrefix init s)
    (hα : ActivationFirstAt init ω s w.activation) :
    ActiveMainRow init ω s w ∧ ActiveClockRow init ω s w := by
  have hfloors := active_role_floors_after_activationFirst init ω s w.activation hseed hα
  exact ⟨fun v hv _ => (hfloors v hv).1, fun v hv _ => (hfloors v hv).2⟩

theorem exists_activationFirst_of_asyncEntry (init : InputCfg n)
    (ω : InputLog n) (s T : ℕ) (hentry : AsyncEntry init ω s T) :
    ∃ α, α ≤ T ∧ ActivationFirstAt init ω s α := by
  obtain ⟨α, htime, hαT, -⟩ :=
    exists_macroscopic_firstAfter_of_asyncEntry init ω s T hentry
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 hentry.first_phase_seed, hentry.seed_profile⟩
  exact ⟨α, hαT, macroscopicTime_firstAfter_core_virtual init
    (seedPrefix_card_eq init ω s hseed) s α ω htime⟩

theorem activationFirst_of_virtualCore (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (hcore : VirtualClockCore init ω s T w) :
    ActivationFirstAt init ω s w.activation :=
  hcore.activation_first

theorem activeMainRow_of_virtualCore (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (hcore : VirtualClockCore init ω s T w) :
    ActiveMainRow init ω s w :=
  hcore.active_main_floor

theorem activeClockRow_of_virtualCore (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (hcore : VirtualClockCore init ω s T w) :
    ActiveClockRow init ω s w :=
  hcore.active_clock_floor

def activationFirstFailureAt (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧
    ∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧
      ¬ ∃ α, α ≤ T ∧ ActivationFirstAt init ω s α}

def activeMainFailureAt (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧
    ∃ T, ∃ w : ClockTimes init, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧
      ActivationFirstAt init ω s w.activation ∧ ¬ ActiveMainRow init ω s w}

def activeClockFailureAt (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧
    ∃ T, ∃ w : ClockTimes init, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧
      ActivationFirstAt init ω s w.activation ∧ ¬ ActiveClockRow init ω s w}

theorem activationFirstFailureAt_eq_empty (init : InputCfg n) (s : ℕ) :
    activationFirstFailureAt init s = ∅ := by
  ext ω
  constructor
  · rintro ⟨-, -, T, -, hentry, hbad⟩
    exact False.elim (hbad (exists_activationFirst_of_asyncEntry init ω s T hentry))
  · intro hω
    exact False.elim hω

theorem activeMainFailureAt_eq_empty (init : InputCfg n) (s : ℕ) :
    activeMainFailureAt init s = ∅ := by
  ext ω
  constructor
  · rintro ⟨hs, hsp, T, w, -, -, hα, hbad⟩
    exact False.elim
      (hbad (active_role_rows_of_activationFirst init ω s w ⟨hs, hsp⟩ hα).1)
  · intro hω
    exact False.elim hω

theorem activeClockFailureAt_eq_empty (init : InputCfg n) (s : ℕ) :
    activeClockFailureAt init s = ∅ := by
  ext ω
  constructor
  · rintro ⟨hs, hsp, T, w, -, -, hα, hbad⟩
    exact False.elim
      (hbad (active_role_rows_of_activationFirst init ω s w ⟨hs, hsp⟩ hα).2)
  · intro hω
    exact False.elim hω

theorem seed_activation_first_row_tail (init : InputCfg n) (s : ℕ) :
    law init (activationFirstFailureAt init s) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  simp only [activationFirstFailureAt_eq_empty, measure_empty, zero_mul, le_refl]

theorem seed_active_main_row_tail (init : InputCfg n) (s : ℕ) :
    law init (activeMainFailureAt init s) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  simp only [activeMainFailureAt_eq_empty, measure_empty, zero_mul, le_refl]

theorem seed_active_clock_row_tail (init : InputCfg n) (s : ℕ) :
    law init (activeClockFailureAt init s) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  simp only [activeClockFailureAt_eq_empty, measure_empty, zero_mul, le_refl]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationRows

end

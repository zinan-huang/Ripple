-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockCoreCounts.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCore
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationSeed

/-!
# Concrete counting bridges to the clock-history core

The active population and effective minute in ClockCore are the quantities
used by the new activation and front estimates. Its front count freezes
the physical Clock roles at the seed; equality with the current-role front
is therefore proved with an explicit roles-fixed premise.

On a genuine seedPrefix, the current phase upper bound supplies that
premise through the existing seed-role theorem. Physical Clock-contact
counts use only the seed mask and the recorded draws, so their bridge to
StageEventSpec requires seed agreement but no later phase bound.

No clock-history clause or hour-occupancy estimate is produced here.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCoreCounts

open TimeTheorem PairLog PhaseThreeClockCore PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockActivationLaw PhaseThreeClockActivationSeed
  PhaseThreeClockSeedTails

variable {n : ℕ}

theorem activeCountL_eq_activeCount (init : InputCfg n) (fv : Lab init) :
    activeCountL init fv = PhaseThreeClockActivationLaw.activeCount fv := by
  classical
  unfold activeCountL StageEventSpec.labelCount
    PhaseThreeClockActivationLaw.activeCount PhaseThreeClockActivationLaw.activeSet
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, activeL]

/-- Split the activity predicate explicitly: the core definition uses
classical decidability whereas effMinute uses the natural comparison. -/
theorem effectiveMinuteL_eq_effMinute (init : InputCfg n)
    (fv : Lab init) (i : Fin init.card) :
    effectiveMinuteL init fv i = effMinute (fv i) := by
  classical
  by_cases h : 3 ≤ (fv i).phase.val
  · simp only [effectiveMinuteL, activeL, effMinute, h, if_true]
  · simp only [effectiveMinuteL, activeL, effMinute, h, if_false]

theorem frontCountL_eq_frontCount (init : InputCfg n)
    (fS fv : Lab init) (ℓ : ℕ)
    (hroles : ∀ i, (fv i).role = (fS i).role) :
    frontCountL init fS fv ℓ = PhaseThreeClockGatedLaw.frontCount fv ℓ := by
  classical
  unfold frontCountL StageEventSpec.labelCount
    PhaseThreeClockGatedLaw.frontCount aboveSet
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, fixedRoleL,
    effectiveMinuteL_eq_effMinute, hroles i]

theorem frontCountL_self (init : InputCfg n) (fv : Lab init) (ℓ : ℕ) :
    frontCountL init fv fv ℓ = PhaseThreeClockGatedLaw.frontCount fv ℓ :=
  frontCountL_eq_frontCount init fv fv ℓ (fun _ => rfl)

/-- The core's recorded contact is precisely a contact in its frozen
physical Clock mask. Both recorded orientations remain present. -/
theorem clockContactL_iff_clockSet (init : InputCfg n)
    (fS : Lab init) (draws : Draws init) (k : ℕ) :
    clockContactL init fS draws k ↔
      ∃ i j, draws k = some (i, j) ∧ i ∈ clockSet fS ∧ j ∈ clockSet fS := by
  classical
  simp only [clockContactL, fixedRoleL, clockSet, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem frontCountL_actual_seed_virtual (init : InputCfg n) (ω : InputLog n)
    (S v ℓ : ℕ) (hseed : ω ∈ seedPrefix init S) (hSv : S ≤ v)
    (hcap : ∀ i, (virtualLabels init ω v i).phase.val ≤ 3) :
    frontCountL init (labelsAt init ω S) (virtualLabels init ω v) ℓ =
      PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω v) ℓ :=
  frontCountL_eq_frontCount init _ _ ℓ
    (virtual_roles_eq_seed_of_current_phase_cap init ω S v hseed hSv hcap)

/-- This is the frontCountL appearing in VirtualClockCore. Its explicit
roles-fixed requirement is discharged from the observed seed and a current
phase cap, without conditioning on a future no-exit event. -/
theorem frontCountL_virtual_seed (init : InputCfg n) (ω : InputLog n)
    (S v ℓ : ℕ) (hseed : ω ∈ seedPrefix init S) (hSv : S ≤ v)
    (hcap : ∀ i, (virtualLabels init ω v i).phase.val ≤ 3) :
    frontCountL init (virtualLabels init ω S) (virtualLabels init ω v) ℓ =
      PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω v) ℓ := by
  rw [virtual_eq_actual_at_seedPrefix init ω S hseed]
  exact frontCountL_actual_seed_virtual init ω S v ℓ hseed hSv hcap

theorem clockContactL_virtual_seed_iff (init : InputCfg n) (ω : InputLog n)
    (S k : ℕ) (hseed : ω ∈ seedPrefix init S) :
    clockContactL init (virtualLabels init ω S) (drawLabels init ω) k ↔
      StageEventSpec.clockContact init ω S k := by
  rw [virtual_eq_actual_at_seedPrefix init ω S hseed]
  rfl

/-- The contact intervals are the same Ioc intervals on the same recorded
draw log. Agreement at the seed identifies their frozen physical masks. -/
theorem clockContactsL_virtual_seed (init : InputCfg n) (ω : InputLog n)
    (S u v : ℕ) (hseed : ω ∈ seedPrefix init S) :
    clockContactsL init (virtualLabels init ω S) (drawLabels init ω) u v =
      StageEventSpec.clockContacts init ω S u v := by
  rw [virtual_eq_actual_at_seedPrefix init ω S hseed]
  exact (PhaseThreeClockCore.clockContacts_eq_L init ω S u v).symm

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCoreCounts

end

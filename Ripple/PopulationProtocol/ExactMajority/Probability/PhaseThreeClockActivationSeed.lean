-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockActivationSeed.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEmbeddingBridge
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockSeedTails

/-!
# Genuine first-seed initial conditions for virtual activation

These lemmas use only the observed seedPrefix: the true first Phase-3 seed
and its SeedProfile at that time. Virtual/actual agreement at the seed,
a positive activation count, the neutral non-Main carrier invariant, and
the phase-one lower bound are obtained without AsyncEntry or any future
success event.

At a later observed time, a phase upper bound discharges the roles-fixed
guard on the preceding interval. Full threshold activation then gives exact
homogeneous Phase 3. Producing that phase upper bound is separate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationSeed

open TimeTheorem PairLog PhaseThreeClockProducer PhaseThreeClockSeedTails
  PhaseThreeClockVirtual PhaseThreeClockActivationLaw PhaseThreeClockGatedLaw
  PhaseThreeClockEmbeddingBridge

variable {n : ℕ}

theorem virtual_eq_actual_at_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (hseed : ω ∈ seedPrefix init s) :
    virtualLabels init ω s = labelsAt init ω s := by
  have hfirst : firstPhaseSeed init 3 s ω :=
    (seedTime_eq_iff init 3 ω s).1 hseed.1
  apply virtualLabels_eq_labelsAt_of_phases_lt_four init ω s ?_ s le_rfl
  intro v hv i
  by_cases hvs : v < s
  · have hlt := hfirst.2 v hvs _ (labelsAt_mem_trace init ω v i)
    omega
  · have heq : v = s := by omega
    subst v
    have hp := (hseed.2.phase_range _ (labelsAt_mem_trace init ω s i)).2
    omega

theorem virtual_environment_at_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (hseed : ω ∈ seedPrefix init s) :
    ClockEnvironment (virtualLabels init ω s) := by
  rw [virtual_eq_actual_at_seedPrefix init ω s hseed]
  exact seedProfile_clockEnvironment init ω s hseed.2

theorem virtual_carrier_from_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (hseed : ω ∈ seedPrefix init s) :
    ∀ u, s ≤ u → ∀ i,
      nonMainCarrierSmallBiasZeroAgent (virtualLabels init ω u i) :=
  virtualLabels_carrier_of_time init ω s
    (virtual_environment_at_seedPrefix init ω s hseed).carrier

theorem virtual_phase_floor_from_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (s u : ℕ) (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u) :
    ∀ i, 1 ≤ (virtualLabels init ω u i).phase.val := by
  intro i
  exact ((virtual_environment_at_seedPrefix init ω s hseed).phase_range i).1.trans
    (virtualLabels_phase_mono init ω i hsu)

theorem positive_activation_at_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (hseed : ω ∈ seedPrefix init s) :
    1 ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω s) := by
  have hfirst : firstPhaseSeed init 3 s ω :=
    (seedTime_eq_iff init 3 ω s).1 hseed.1
  obtain ⟨a, ha, hp⟩ := hfirst.1
  have hamem : a ∈ labelCfg (labelsAt init ω s) := by
    rw [show labelCfg (labelsAt init ω s) = trace init ω s from labelsAt_config init ω s]
    exact ha
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hamem
  have hiA : i ∈ activeSet (virtualLabels init ω s) := by
    simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [virtual_eq_actual_at_seedPrefix init ω s hseed, hi, hp] using
      (le_refl (3 : ℕ))
  have hpos : 0 < PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω s) :=
    Finset.card_pos.mpr ⟨i, hiA⟩
  omega

theorem positive_activation_from_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (s u : ℕ) (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u) :
    1 ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) :=
  (positive_activation_at_seedPrefix init ω s hseed).trans
    (activeCount_virtualLabels_mono init ω hsu)

/-- A current phase upper bound suffices: phase monotonicity transports it
back across the finite observed interval from the seed. -/
theorem virtual_roles_eq_seed_of_current_phase_cap
    (init : InputCfg n) (ω : InputLog n) (s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u)
    (hcap : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3) :
    ∀ i, (virtualLabels init ω u i).role = (labelsAt init ω s i).role := by
  revert hcap
  induction u, hsu using Nat.le_induction with
  | base =>
      intro _ i
      rw [virtual_eq_actual_at_seedPrefix init ω s hseed]
  | succ u hsu ih =>
      intro hcap i
      have hcapu : ∀ j, (virtualLabels init ω u j).phase.val ≤ 3 :=
        fun j => (virtualLabels_phase_mono init ω j (Nat.le_succ u)).trans (hcap j)
      have hpre : ∀ j, 1 ≤ (virtualLabels init ω u j).phase.val ∧
          (virtualLabels init ω u j).phase.val ≤ 3 :=
        fun j => ⟨virtual_phase_floor_from_seedPrefix init ω s u hseed hsu j, hcapu j⟩
      exact (virtualLabels_roles_step_of_phase_range init ω u hpre hcap i).trans
        (ih hcapu i)

theorem virtual_clockSet_eq_seed_of_current_phase_cap
    (init : InputCfg n) (ω : InputLog n) (s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u)
    (hcap : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3) :
    clockSet (virtualLabels init ω u) = clockSet (labelsAt init ω s) := by
  classical
  ext i
  simp only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and,
    virtual_roles_eq_seed_of_current_phase_cap init ω s u hseed hsu hcap]

/-- The activation endpoint is a homogeneous clock start as soon as
its observed phase-cap guard is available. -/
theorem homogeneous_of_seedPrefix_full_activation
    (init : InputCfg n) (ω : InputLog n) (s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u)
    (hfull : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) = init.card)
    (hcap : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3) :
    (∀ i, (virtualLabels init ω u i).phase.val = 3) ∧
      ∀ i, nonMainCarrierSmallBiasZeroAgent (virtualLabels init ω u i) :=
  ⟨phase_three_of_activeCount_eq_card _ hfull hcap,
    virtual_carrier_from_seedPrefix init ω s hseed u hsu⟩


theorem clockCount_labelsAt_eq_trace (init : InputCfg n) (ω : InputLog n) (s : ℕ) :
    clockCount (labelsAt init ω s) =
      RoleSplitConcentration.clockCount (trace init ω s) := by
  rw [← labelsAt_config init ω s]
  exact (Multiset.countP_map (labelsAt init ω s) Finset.univ.val
    (fun a => a.role = .clock)).symm

theorem seedPrefix_card_eq (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (hseed : ω ∈ seedPrefix init s) :
    init.card = n := by
  have hcard : (trace init ω s).card = init.card := by
    rw [← labelsAt_config init ω s]
    exact labelCfg_card _
  exact hcard.symm.trans hseed.2.card_eq

theorem clock_density_at_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (hseed : ω ∈ seedPrefix init s) :
    6 * init.card ≤ 25 * clockCount (labelsAt init ω s) := by
  have hlow := hseed.2.role_good.2.2.2.1
  have hreal :
      6 * (n : ℝ) ≤ 25 * (RoleSplitConcentration.clockCount (trace init ω s) : ℝ) := by
    linarith
  rw [clockCount_labelsAt_eq_trace init ω s, seedPrefix_card_eq init ω s hseed]
  exact_mod_cast hreal

theorem clock_two_at_seedPrefix (init : InputCfg n) (hn : 9 ≤ n)
    (ω : InputLog n) (s : ℕ) (hseed : ω ∈ seedPrefix init s) :
    2 ≤ clockCount (labelsAt init ω s) := by
  rw [clockCount_labelsAt_eq_trace init ω s]
  exact RoleSplitConcentration.clockCount_ge_two_of_RoleSplitGood
    (by norm_num : (1 / 25 : ℝ) ≤ 1 / 25) hn hseed.2.role_good

theorem virtual_clockCount_eq_seed_of_current_phase_cap
    (init : InputCfg n) (ω : InputLog n) (s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u)
    (hcap : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3) :
    clockCount (virtualLabels init ω u) = clockCount (labelsAt init ω s) := by
  unfold clockCount
  rw [virtual_clockSet_eq_seed_of_current_phase_cap init ω s u hseed hsu hcap]

/-- These are precisely the state data used by the first-positive estimate.
The only additional path condition is the phase cap at the observed endpoint. -/
theorem dense_start_data_of_seedPrefix_full_activation
    (init : InputCfg n) (hn : 9 ≤ n) (ω : InputLog n) (s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u)
    (hfull : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) = init.card)
    (hcap : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3) :
    ((∀ i, (virtualLabels init ω u i).phase.val = 3) ∧
      ∀ i, nonMainCarrierSmallBiasZeroAgent (virtualLabels init ω u i)) ∧
      2 ≤ clockCount (virtualLabels init ω u) ∧
      6 * init.card ≤ 25 * clockCount (virtualLabels init ω u) := by
  refine ⟨homogeneous_of_seedPrefix_full_activation init ω s u hseed hsu hfull hcap, ?_⟩
  rw [virtual_clockCount_eq_seed_of_current_phase_cap init ω s u hseed hsu hcap]
  exact ⟨clock_two_at_seedPrefix init hn ω s hseed,
    clock_density_at_seedPrefix init ω s hseed⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationSeed

end

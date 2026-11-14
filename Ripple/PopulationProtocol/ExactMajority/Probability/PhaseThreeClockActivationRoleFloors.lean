-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockActivationRoleFloors.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCoreCounts
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationLaw

/-!
# Active-role floors after the observed ninety-nine-percent passage

These are the active_main_floor and active_clock_floor numerical clauses
of ClockCore, using its exact fixed-seed-role counting functions.

Any fixed mask R loses at most the total number of inactive labels.
At ninety-nine-percent activation, 100 times that loss is at most m.
The seed densities 12m <= 25M and 6m <= 25C consequently give the
47/48 Main and 23/24 Clock activation floors.

The argument uses only current activation and fixed observed masks.
Propagation along the virtual continuation uses actual phase monotonicity.
It does not assert hour occupancy or identify full activation with hour zero.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationRoleFloors

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockActivationLaw PhaseThreeClockCore PhaseThreeClockCoreCounts

variable {n : ℕ}

open Classical in
def fixedRoleMask (init : InputCfg n) (fS : Lab init) (r : Role) :
    Finset (Fin init.card) :=
  Finset.univ.filter (fixedRoleL init fS r)

theorem activeCountL_le_card (init : InputCfg n) (fv : Lab init) :
    activeCountL init fv ≤ init.card := by
  rw [activeCountL_eq_activeCount]
  exact activeCount_le_card fv

open Classical in
theorem activeRoleCountL_eq_filter_card (init : InputCfg n) (fS fv : Lab init)
    (r : Role) :
    activeRoleCountL init fS fv r =
      ((fixedRoleMask init fS r).filter (activeL init fv)).card := by
  classical
  unfold activeRoleCountL StageEventSpec.labelCount fixedRoleMask
  rw [Finset.filter_filter]
  congr

open Classical in
/-- A fixed observed mask loses no more than the global inactive population. -/
theorem fixed_mask_active_loss (init : InputCfg n) (fv : Lab init)
    (R : Finset (Fin init.card)) :
    R.card ≤ (R.filter (activeL init fv)).card +
      (init.card - activeCountL init fv) := by
  classical
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := R) (activeL init fv)
  have hinactive :
      (R.filter (fun i => ¬ activeL init fv i)).card ≤
        (dormantSet fv).card := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter] at hi
    simp only [dormantSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi.2
  rw [dormantSet_card, ← activeCountL_eq_activeCount init fv] at hinactive
  omega

theorem fixed_role_active_loss (init : InputCfg n) (fS fv : Lab init) (r : Role) :
    (fixedRoleMask init fS r).card ≤ activeRoleCountL init fS fv r +
      (init.card - activeCountL init fv) := by
  rw [activeRoleCountL_eq_filter_card]
  exact fixed_mask_active_loss init fv (fixedRoleMask init fS r)

/-- The ceil formulation used by ClockCore implies the exact integral
one-percent bound on the inactive population. -/
theorem inactive_one_percent (init : InputCfg n) (fv : Lab init)
    (hmacro : Nat.ceil ((99 : ℝ) * (init.card : ℝ) / 100) ≤ activeCountL init fv) :
    100 * (init.card - activeCountL init fv) ≤ init.card := by
  have hreal :
      (99 : ℝ) * (init.card : ℝ) / 100 ≤ (activeCountL init fv : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hmacro)
  have hscaled : 99 * init.card ≤ 100 * activeCountL init fv := by
    have hscaledR : (99 : ℝ) * (init.card : ℝ) ≤
        100 * (activeCountL init fv : ℝ) := by linarith
    exact_mod_cast hscaledR
  have hA := activeCountL_le_card init fv
  omega

theorem active_main_mask_floor (init : InputCfg n) (fS fv : Lab init)
    (hmacro : Nat.ceil ((99 : ℝ) * (init.card : ℝ) / 100) ≤ activeCountL init fv)
    (hdensity : 12 * init.card ≤ 25 * (fixedRoleMask init fS .main).card) :
    47 * (fixedRoleMask init fS .main).card ≤
      48 * activeRoleCountL init fS fv .main := by
  have hinactive := inactive_one_percent init fv hmacro
  have hloss := fixed_role_active_loss init fS fv .main
  have hrelative : 48 * (init.card - activeCountL init fv) ≤
      (fixedRoleMask init fS .main).card := by omega
  omega

theorem active_clock_mask_floor (init : InputCfg n) (fS fv : Lab init)
    (hmacro : Nat.ceil ((99 : ℝ) * (init.card : ℝ) / 100) ≤ activeCountL init fv)
    (hdensity : 6 * init.card ≤ 25 * (fixedRoleMask init fS .clock).card) :
    23 * (fixedRoleMask init fS .clock).card ≤
      24 * activeRoleCountL init fS fv .clock := by
  have hinactive := inactive_one_percent init fv hmacro
  have hloss := fixed_role_active_loss init fS fv .clock
  have hrelative : 24 * (init.card - activeCountL init fv) ≤
      (fixedRoleMask init fS .clock).card := by omega
  omega

theorem fixedRoleMask_card_eq_countP (init : InputCfg n) (fS : Lab init) (r : Role) :
    (fixedRoleMask init fS r).card =
      Multiset.countP (fun a => a.role = r) (labelCfg fS) := by
  classical
  unfold fixedRoleMask labelCfg
  rw [Multiset.countP_map, Finset.card, Finset.filter_val]
  congr

theorem main_mask_card (init : InputCfg n) (fS : Lab init) :
    (fixedRoleMask init fS .main).card = timeMainCount (labelCfg fS) :=
  fixedRoleMask_card_eq_countP init fS .main

theorem clock_mask_card (init : InputCfg n) (fS : Lab init) :
    (fixedRoleMask init fS .clock).card =
      RoleSplitConcentration.clockCount (labelCfg fS) :=
  fixedRoleMask_card_eq_countP init fS .clock

/-- The exact Main floor in ClockCore, on any two labellings. -/
theorem active_main_floor (init : InputCfg n) (fS fv : Lab init)
    (hmacro : Nat.ceil ((99 : ℝ) * (init.card : ℝ) / 100) ≤ activeCountL init fv)
    (hdensity : 12 * init.card ≤ 25 * timeMainCount (labelCfg fS)) :
    47 * timeMainCount (labelCfg fS) ≤ 48 * activeRoleCountL init fS fv .main := by
  have h := active_main_mask_floor init fS fv hmacro
    (by simpa only [main_mask_card] using hdensity)
  simpa only [main_mask_card] using h

/-- The exact Clock floor in ClockCore, on any two labellings. -/
theorem active_clock_floor (init : InputCfg n) (fS fv : Lab init)
    (hmacro : Nat.ceil ((99 : ℝ) * (init.card : ℝ) / 100) ≤ activeCountL init fv)
    (hdensity : 6 * init.card ≤ 25 * RoleSplitConcentration.clockCount (labelCfg fS)) :
    23 * RoleSplitConcentration.clockCount (labelCfg fS) ≤
      24 * activeRoleCountL init fS fv .clock := by
  have h := active_clock_mask_floor init fS fv hmacro
    (by simpa only [clock_mask_card] using hdensity)
  simpa only [clock_mask_card] using h

theorem activeCountL_virtual_mono (init : InputCfg n) (ω : InputLog n) :
    Monotone (fun v => activeCountL init (virtualLabels init ω v)) := by
  intro u v huv
  show activeCountL init (virtualLabels init ω u) ≤ activeCountL init (virtualLabels init ω v)
  rw [activeCountL_eq_activeCount, activeCountL_eq_activeCount]
  exact activeCount_virtualLabels_mono init ω huv

/-- Once observed, the macro-activation threshold and its role floors
persist at every later virtual time. No current-role stability assumption
is needed: activeRoleCountL uses the fixed seed mask by definition. -/
theorem virtual_active_role_floors (init : InputCfg n) (ω : InputLog n)
    (S α : ℕ)
    (hmacro : Nat.ceil ((99 : ℝ) * (init.card : ℝ) / 100) ≤
      activeCountL init (virtualLabels init ω α))
    (hmain : 12 * init.card ≤ 25 * timeMainCount (virtualCfg init ω S))
    (hclock : 6 * init.card ≤ 25 * RoleSplitConcentration.clockCount (virtualCfg init ω S)) :
    ∀ v, α ≤ v →
      47 * timeMainCount (virtualCfg init ω S) ≤
        48 * activeRoleCountL init (virtualLabels init ω S) (virtualLabels init ω v) .main ∧
      23 * RoleSplitConcentration.clockCount (virtualCfg init ω S) ≤
        24 * activeRoleCountL init (virtualLabels init ω S) (virtualLabels init ω v) .clock := by
  intro v hαv
  have hv := hmacro.trans (activeCountL_virtual_mono init ω hαv)
  exact ⟨active_main_floor init (virtualLabels init ω S) (virtualLabels init ω v) hv hmain,
    active_clock_floor init (virtualLabels init ω S) (virtualLabels init ω v) hv hclock⟩

/-- The parameters and inequalities are now exactly those of ClockCore.
The actual population-cardinality identity is kept explicit. -/
theorem core_active_role_floors (init : InputCfg n) (ω : InputLog n)
    (S α : ℕ) (hcard : init.card = n)
    (hmacro : Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤
      activeCountL init (virtualLabels init ω α))
    (hmain : 12 * n ≤ 25 * timeMainCount (virtualCfg init ω S))
    (hclock : 6 * n ≤ 25 * RoleSplitConcentration.clockCount (virtualCfg init ω S)) :
    ∀ v, α ≤ v →
      47 * timeMainCount (virtualCfg init ω S) ≤
        48 * activeRoleCountL init (virtualLabels init ω S) (virtualLabels init ω v) .main ∧
      23 * RoleSplitConcentration.clockCount (virtualCfg init ω S) ≤
        24 * activeRoleCountL init (virtualLabels init ω S) (virtualLabels init ω v) .clock := by
  exact virtual_active_role_floors init ω S α
    (by simpa only [hcard] using hmacro)
    (by simpa only [hcard] using hmain)
    (by simpa only [hcard] using hclock)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationRoleFloors

end

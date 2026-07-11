/-
Ripple.BoundedUniversality.BGP.ContractFlagAtomicMU
-------------------------------
M_U-specific atomic facts for the flag-only headline's discharge theorems.

These are concrete facts about the universal machine M_U at haltCoordU,
bgpParams38, and bgpSchedulePhys — the irreducible interface between the
generic ODE-dynamics proofs and the specific machine instance.

**Fact 1: encoding range** — `confEncU c haltCoordU ∈ {0, 1} ⊆ [0,1]`.
  Consumed by `contract_z_unit_trapping` (initial data for [0,1] trapping).

**Fact 2: running flag ∈ [0, 1/4]** — when `finHalted c = false`,
  `confEncU c haltCoordU = 0 ∈ [0, 1/4]`.
  Consumed by `contract_flag_low_below_from_quarter_trapping` (initial data).

**Fact 3: `bgpParams38_A_nonneg`** — `0 ≤ bgpParams38.A`.
  Consumed by all trapping/settling discharge theorems.

**Fact 4: `bgpSchedulePhys` regularity** — Domain, window nonnegativity:
  - `∀ t, 0 ≤ t → t ∈ bgpSchedulePhys.domain`
  - `∀ j t, t ∈ bgpSchedulePhys.zActiveWindow j → 0 ≤ t`
  - `∀ j t, t ∈ ... → Set.Icc 0 t ⊆ bgpSchedulePhys.domain`

These 4 atomic facts, together with the carried field-range hypotheses
(which require unfolding the polynomial indicator at haltCoordU), are
sufficient to discharge all 3 remaining Reach premises of
`contract_flag_only_headline_MU`.

No sorry/admit/native_decide/axiom.
-/

import Ripple.BoundedUniversality.BGP.ContractFlagLowFromTrapping
import Ripple.BoundedUniversality.BGP.ContractFlagMarginBound
import Ripple.BoundedUniversality.BGP.ContractTrappingInvariant
import Ripple.BoundedUniversality.BGP.WarmedHeadlinePhys
import Ripple.BoundedUniversality.BGP.FlagIndicatorPolyMU

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open MachineInstance UniversalMachine
open Real Set

noncomputable section

/-! ## Fact 1: Halt flag encoding in [0,1] -/

/-- The halt flag coordinate of the universal encoding is `0` or `1`. -/
theorem haltFlagU_eq_zero_or_one (c : UConf) :
    haltFlagU c = 0 ∨ haltFlagU c = 1 := by
  unfold haltFlagU
  split <;> simp

/-- `confEncU c haltCoordU` is rational and in `[0, 1]`. -/
theorem confEncU_halt_mem_unit (c : UConf) :
    (confEncU c haltCoordU : ℝ) ∈ Icc (0 : ℝ) 1 := by
  rw [confEncU_halt]
  cases haltFlagU_eq_zero_or_one c with
  | inl h => simp [h]
  | inr h => simp [h]

/-- `stackMachineEncodingU.enc c haltCoordU ∈ [0,1]` — the real-valued form
consumed by trapping theorems. -/
theorem enc_haltCoordU_mem_unit (c : UConf) :
    stackMachineEncodingU.enc c haltCoordU ∈ Icc (0 : ℝ) 1 := by
  change (confEncU c haltCoordU : ℝ) ∈ Icc 0 1
  exact confEncU_halt_mem_unit c

/-! ## Fact 2: Halt flag in [0, 1/4] for running configs -/

/-- When a config is not halted, its flag encoding is `0`. -/
theorem haltFlagU_running (c : UConf) (h : finHalted c = false) :
    haltFlagU c = 0 := by
  simp [haltFlagU, h]

/-- `confEncU c haltCoordU ∈ [0, 1/4]` when `c` is a running (non-halted)
config. -/
theorem confEncU_halt_running_mem_quarter (c : UConf)
    (h : finHalted c = false) :
    (confEncU c haltCoordU : ℝ) ∈ Icc (0 : ℝ) (1 / 4) := by
  rw [confEncU_halt, haltFlagU_running c h]
  norm_num

/-- `stackMachineEncodingU.enc c haltCoordU ∈ [0, 1/4]` for running
configs. -/
theorem enc_haltCoordU_running_mem_quarter (c : UConf)
    (h : finHalted c = false) :
    stackMachineEncodingU.enc c haltCoordU ∈ Icc (0 : ℝ) (1 / 4) := by
  change (confEncU c haltCoordU : ℝ) ∈ Icc 0 (1 / 4)
  exact confEncU_halt_running_mem_quarter c h

/-! ## Fact 3: bgpParams38 regularity -/

/-- `bgpParams38.A = 1 ≥ 0`. -/
theorem bgpParams38_A_nonneg : (0 : ℝ) ≤ bgpParams38.A := by
  norm_num [bgpParams38]

/-- `bgpParams38.cμ = 1 ≥ 0`. -/
theorem bgpParams38_cmu_nonneg : (0 : ℝ) ≤ bgpParams38.cμ := by
  norm_num [bgpParams38]

/-- `bgpParams38.cα = 3/8 ≥ 0`. -/
theorem bgpParams38_calpha_nonneg : (0 : ℝ) ≤ bgpParams38.cα := by
  norm_num [bgpParams38]

/-! ## Fact 4: bgpSchedulePhys regularity -/

/-- Every `t ≥ 0` is in `bgpSchedulePhys.domain`. -/
theorem bgpSchedulePhys_domain_of_nonneg :
    ∀ t : ℝ, 0 ≤ t → t ∈ bgpSchedulePhys.domain :=
  fun _t ht => ht

/-- Times in any z-active window of `bgpSchedulePhys` are nonneg. -/
theorem bgpSchedulePhys_zActive_nonneg :
    ∀ j : ℕ, ∀ t : ℝ, t ∈ bgpSchedulePhys.zActiveWindow j → 0 ≤ t := by
  intro j t ht
  -- Unfold the definition: zActiveWindow j = Icc (2πj + 5π/6) (2πj + 7π/6)
  simp only [bgpSchedulePhys, Set.mem_Icc] at ht
  have hπ := Real.pi_pos
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith [ht.1]

/-- The interval `[0, t]` is contained in `bgpSchedulePhys.domain` for any
`t ≥ 0`. -/
theorem bgpSchedulePhys_Icc_domain :
    ∀ t : ℝ, 0 ≤ t → Icc (0 : ℝ) t ⊆ bgpSchedulePhys.domain :=
  fun _t _ht τ hτ => hτ.1

/-- Combined: window membership implies the interval [0, t] is in the
domain. -/
theorem bgpSchedulePhys_zActive_Icc_domain :
    ∀ j : ℕ, ∀ t : ℝ, t ∈ bgpSchedulePhys.zActiveWindow j →
      Icc (0 : ℝ) t ⊆ bgpSchedulePhys.domain :=
  fun j t ht =>
    bgpSchedulePhys_Icc_domain t (bgpSchedulePhys_zActive_nonneg j t ht)

/-! ## Assembly: flag domain [0,1] discharge

Combines Fact 1 (encoding range) + Fact 3/4 (regularity) + the generic
`contract_z_coord_trapping_on_zActiveWindow_of_F` to produce `hflag_domain`
for `contract_flag_only_headline_MU`.

The field-range hypothesis `hw_unit` (that `S.F(μ,u) haltCoordU ∈ [0,1]`)
is carried because discharging it requires unfolding the polynomial
indicator at `haltCoordU` — that is the M_U field package's business. -/

theorem flag_domain_MU
    (S : RobustStepContract
      UniversalMachine.undecidableMachine.toDiscreteMachine
      stackMachineEncodingU)
    (sol : DynContractIteratorSol (Fin d_U) bgpParams38 bgpSchedulePhys S.F)
    (hαcont : Continuous sol.α) (hμcont : Continuous sol.μ)
    (hαinit : 0 ≤ sol.init_α)
    (hz0 : sol.z 0 haltCoordU ∈ Icc (0 : ℝ) 1)
    -- Carried: the field maps into [0,1] at the flag coordinate
    (hw_unit : ∀ j : ℕ, ∀ t : ℝ,
      t ∈ bgpSchedulePhys.zActiveWindow j →
        ∀ τ ∈ Icc (0 : ℝ) t,
          S.F (sol.μ τ) (sol.u τ) haltCoordU ∈ Icc (0 : ℝ) 1) :
    ∀ j : ℕ, ∀ t : ℝ, t ∈ bgpSchedulePhys.zActiveWindow j →
      sol.z t haltCoordU ∈ Icc (0 : ℝ) 1 :=
  contract_z_coord_trapping_on_zActiveWindow_of_F sol haltCoordU
    bgpSchedulePhys_zActive_nonneg
    bgpSchedulePhys_zActive_Icc_domain
    bgpParams38_A_nonneg hαcont hμcont
    (fun τ hτ => by
      rw [contractSol_alpha_eq sol bgpSchedulePhys_domain_of_nonneg
        (bgpSchedulePhys_domain_nonneg τ hτ)]
      exact mul_nonneg hαinit (exp_pos _).le)
    hw_unit hz0

/-! ## Assembly: flag indicator low for j < j0

Combines Fact 2 (encoding range for running) + Fact 3/4 (regularity) +
the generic `contract_flag_low_below_from_quarter_trapping`.

The field-range hypothesis `hw_quarter` (that
`sol.w τ haltCoordU ∈ [0, 1/4]`) is carried. -/

theorem flag_low_below_MU
    (S : RobustStepContract
      UniversalMachine.undecidableMachine.toDiscreteMachine
      stackMachineEncodingU)
    (sol : DynContractIteratorSol (Fin d_U) bgpParams38 bgpSchedulePhys S.F)
    (j₀ : ℕ)
    (hαcont : Continuous sol.α) (hμcont : Continuous sol.μ)
    (hαinit : 0 ≤ sol.init_α)
    (hz0 : sol.z 0 haltCoordU ∈ Icc (0 : ℝ) (1 / 4))
    -- Carried: the field maps into [0, 1/4] at the flag coordinate
    (hw_quarter : ∀ τ : ℝ, 0 ≤ τ → τ ∈ bgpSchedulePhys.domain →
        sol.w τ haltCoordU ∈ Icc (0 : ℝ) (1 / 4)) :
    ∀ j, j < j₀ → ∀ t ∈ bgpSchedulePhys.zActiveWindow j,
      contractFlagIndicatorPackageU_ramp.Hval (sol.z t) ≤
        contractFlagIndicatorPackageU_ramp.eta :=
  contract_flag_low_below_from_quarter_trapping sol haltCoordU
    contractFlagIndicatorPackageU_ramp j₀
    (zRate_continuous sol hαcont hμcont)
    bgpParams38_A_nonneg
    (fun τ hτ => by
      rw [contractSol_alpha_eq sol bgpSchedulePhys_domain_of_nonneg hτ]
      exact mul_nonneg hαinit (exp_pos _).le)
    bgpSchedulePhys_domain_of_nonneg
    bgpSchedulePhys_zActive_nonneg
    hz0 hw_quarter

/-! ## Assembly: flag margin bound

Combines Fact 3/4 with the generic `contract_flag_margin_bound_general`
to produce `∃ j₁, ∀ j ≥ j₁, ρ_flag j ≤ haltFlagPackageU.flagMargin`.

The sequence-level hypotheses (`Λ → ∞`, `δw → 0`, `ρ_flag ≤ budget`)
are carried because they depend on the concrete gate-mass and epsF
bounds. -/

theorem flag_margin_MU
    {ρ_flag Λ δw : ℕ → ℝ} {Bz : ℝ} {j₀ : ℕ}
    (hΛ : Filter.Tendsto Λ Filter.atTop Filter.atTop)
    (hδw : Filter.Tendsto δw Filter.atTop (nhds 0))
    (hρ_nonneg : ∀ j, j₀ ≤ j → 0 ≤ ρ_flag j)
    (hρ_budget : ∀ j, j₀ ≤ j →
      ρ_flag j ≤ exp (-(Λ j)) * Bz + δw j) :
    ∃ j₁, ∀ j, j₁ ≤ j → ρ_flag j ≤ haltFlagPackageU.flagMargin :=
  contract_flag_margin_bound_general hΛ hδw haltFlagPackageU.margin_pos
    hρ_nonneg hρ_budget

#print axioms haltFlagU_eq_zero_or_one
#print axioms confEncU_halt_mem_unit
#print axioms enc_haltCoordU_mem_unit
#print axioms haltFlagU_running
#print axioms confEncU_halt_running_mem_quarter
#print axioms enc_haltCoordU_running_mem_quarter
#print axioms bgpParams38_A_nonneg
#print axioms bgpParams38_cmu_nonneg
#print axioms bgpParams38_calpha_nonneg
#print axioms bgpSchedulePhys_domain_of_nonneg
#print axioms bgpSchedulePhys_zActive_nonneg
#print axioms bgpSchedulePhys_Icc_domain
#print axioms bgpSchedulePhys_zActive_Icc_domain
#print axioms flag_domain_MU
#print axioms flag_low_below_MU
#print axioms flag_margin_MU

end

end Ripple.BoundedUniversality.BGP

/-
Ripple.BoundedUniversality.BGP.FlagIndicatorPolyMU
------------------------------
A **continuous polynomial** halt-flag indicator for the universal machine's
contract latch, replacing the hard-step `contractFlagIndicatorPackageU`.

§3.3 motivation.  The hard-step indicator
`Hval x = if x haltCoordU < 1/2 then 0 else 1` makes `Hval ∘ sol.z` a Heaviside
function of the *continuous* coordinate `sol.z t haltCoordU`; on a halting
trajectory the flag coordinate relaxes continuously from `0` to `1`, crossing
`1/2`, so `Hval ∘ sol.z` is DISCONTINUOUS — `hLatchHcont` is unsatisfiable.
Moreover the field package requires the flag readout `HP` to be a *polynomial*
with `eval₂(z)(HP) = Hval z`, which no step function admits.

The faithful fix is a polynomial Bernstein indicator via the existing
`finiteCoordinateAtoms` separator: a rational polynomial in the halt coordinate,
high (`≥ 1 - η`) on the `1/4`-tube around the halted code `1`, low (`≤ η`) on the
`1/4`-tube around the running code `0`, and in `[0,1]` on the slab `|x_halt| ≤ 2`.
`hLatchHcont` becomes polynomial continuity; the readout identity becomes `rfl`;
the margin proofs reuse `on_tube`/`off_tube`; `η = 1/16 < 1/8` keeps every
downstream `eta < 1/8` constraint.  No `eta = 0` is used anywhere downstream.
-/

import Ripple.BoundedUniversality.BGP.SelectorAtoms
import Ripple.BoundedUniversality.BGP.MachineInstance
import Ripple.BoundedUniversality.BGP.ContractMain
import Ripple.BoundedUniversality.BGP.ContractTracking

namespace Ripple.BoundedUniversality.BGP

namespace MachineInstance

noncomputable section

/-- Boolean code for the halt flag: `false ↦ 0` (running), `true ↦ 1` (halted). -/
def haltBoolCode : Bool → ℝ
  | false => 0
  | true => 1

private theorem haltBoolCode_gap :
    ∀ a b : Bool, a ≠ b → (1 : ℝ) ≤ |haltBoolCode a - haltBoolCode b| := by
  intro a b h
  cases a <;> cases b <;> simp [haltBoolCode] at h ⊢

private theorem haltBoolCode_bound :
    ∀ a : Bool, |haltBoolCode a| + 1 ≤ ((2 : ℚ) : ℝ) := by
  intro a
  cases a <;> norm_num [haltBoolCode]

/-- The rational Bernstein/slab separator atom for the halt coordinate. -/
noncomputable def haltFlagIndicatorAtomU
    (eta : ℚ) (heta : 0 < eta) :
    SlabAtomicSelectorData d_U Bool :=
  finiteCoordinateAtoms
    (coord := haltCoordU)
    (code := haltBoolCode)
    haltBoolCode_gap
    (C := (2 : ℚ))
    (hC := by norm_num)
    haltBoolCode_bound
    (rho := (1 / 4 : ℚ))
    eta
    (hrho := by norm_num)
    (hrho4 := by norm_num)
    heta

/-- The halt-flag readout polynomial `HP`: the separator atom at the halted code. -/
noncomputable def haltFlagIndicatorPolyU
    (eta : ℚ) (heta : 0 < eta) : MvPolynomial (Fin d_U) ℚ :=
  (haltFlagIndicatorAtomU eta heta).poly true

/-- **Continuous polynomial replacement** for the hard-step
`contractFlagIndicatorPackageU`.  `Hval` is polynomial evaluation of the halted
separator atom, so it is continuous and exactly realized by
`haltFlagIndicatorPolyU`.  The margins follow from the atom's `on_tube`/`off_tube`
(`rho = 1/4`, codes `0`/`1`). -/
noncomputable def contractFlagIndicatorPackageU_poly
    (eta : ℚ) (heta : 0 < eta) (heta_lt : (eta : ℝ) < 1 / 8) :
    ContractFlagIndicatorPackage haltCoordU where
  Hval := fun x => evalPoly4 x (haltFlagIndicatorPolyU eta heta)
  eta := (eta : ℝ)
  eta_nonneg := by exact_mod_cast le_of_lt heta
  eta_lt := heta_lt
  in_unit := by
    intro x hx
    have hslab : |x haltCoordU| ≤ ((2 : ℚ) : ℝ) := by
      rw [abs_of_nonneg hx.1]
      have := hx.2; norm_num; linarith
    simpa [haltFlagIndicatorPolyU] using
      (haltFlagIndicatorAtomU eta heta).range_on_slab true x hslab
  on_flag_one := by
    intro x _hx hclose
    have hclose' : |x haltCoordU - haltBoolCode true| ≤ ((1 / 4 : ℚ) : ℝ) := by
      simpa [haltBoolCode] using hclose
    simpa [haltFlagIndicatorPolyU] using
      (haltFlagIndicatorAtomU eta heta).on_tube true x hclose'
  on_flag_zero := by
    intro x _hx hclose
    have hneq : (true : Bool) ≠ false := by decide
    have hclose' : |x haltCoordU - haltBoolCode false| ≤ ((1 / 4 : ℚ) : ℝ) := by
      simpa [haltBoolCode] using hclose
    simpa [haltFlagIndicatorPolyU] using
      (haltFlagIndicatorAtomU eta heta).off_tube true false x hneq hclose'

/-- Concrete choice `η = 1/16`. -/
noncomputable def contractFlagIndicatorPackageU_ramp :
    ContractFlagIndicatorPackage haltCoordU :=
  contractFlagIndicatorPackageU_poly (eta := (1 / 16 : ℚ)) (by norm_num) (by norm_num)

/-- The polynomial `HP` paired with `contractFlagIndicatorPackageU_ramp`. -/
noncomputable def haltFlagIndicatorPolyU_ramp : MvPolynomial (Fin d_U) ℚ :=
  haltFlagIndicatorPolyU (eta := (1 / 16 : ℚ)) (by norm_num)

/-- The field-package indicator identity is definitional: `Hval` is exactly the
evaluation of `haltFlagIndicatorPolyU_ramp`. -/
theorem haltFlagIndicatorPolyU_ramp_eval (x : Fin d_U → ℝ) :
    evalPoly4 x haltFlagIndicatorPolyU_ramp =
      contractFlagIndicatorPackageU_ramp.Hval x := rfl

/-- The concrete ramp indicator is `[0,1]` on the natural halt-coordinate slab
`|x_halt| ≤ 2`.  This is weaker and more satisfiable than asking
`x_halt ∈ [0,1]`. -/
theorem contractFlagIndicatorPackageU_ramp_in_unit_of_abs_le_two
    (x : Fin d_U → ℝ) (hslab : |x haltCoordU| ≤ (2 : ℝ)) :
    0 ≤ contractFlagIndicatorPackageU_ramp.Hval x ∧
      contractFlagIndicatorPackageU_ramp.Hval x ≤ 1 := by
  simpa [contractFlagIndicatorPackageU_ramp, contractFlagIndicatorPackageU_poly,
    haltFlagIndicatorPolyU_ramp, haltFlagIndicatorPolyU, haltFlagIndicatorAtomU,
    finiteCoordinateAtoms] using
    (haltFlagIndicatorAtomU (eta := (1 / 16 : ℚ)) (by norm_num)).range_on_slab
      true x hslab

/-- The ramp indicator is high on the `1/4`-tube around the halted code, without
requiring the coordinate to be in `[0,1]`. -/
theorem contractFlagIndicatorPackageU_ramp_on_flag_one_of_close
    (x : Fin d_U → ℝ) (hclose : |x haltCoordU - 1| ≤ (1 / 4 : ℝ)) :
    1 - contractFlagIndicatorPackageU_ramp.eta ≤
      contractFlagIndicatorPackageU_ramp.Hval x := by
  have hclose' : |x haltCoordU - haltBoolCode true| ≤ ((1 / 4 : ℚ) : ℝ) := by
    simpa [haltBoolCode] using hclose
  simpa [contractFlagIndicatorPackageU_ramp, contractFlagIndicatorPackageU_poly,
    haltFlagIndicatorPolyU_ramp, haltFlagIndicatorPolyU, haltFlagIndicatorAtomU,
    finiteCoordinateAtoms] using
    (haltFlagIndicatorAtomU (eta := (1 / 16 : ℚ)) (by norm_num)).on_tube
      true x hclose'

/-- The ramp indicator is low on the `1/4`-tube around the running code, without
requiring the coordinate to be in `[0,1]`. -/
theorem contractFlagIndicatorPackageU_ramp_on_flag_zero_of_close
    (x : Fin d_U → ℝ) (hclose : |x haltCoordU - 0| ≤ (1 / 4 : ℝ)) :
    contractFlagIndicatorPackageU_ramp.Hval x ≤
      contractFlagIndicatorPackageU_ramp.eta := by
  have hneq : (true : Bool) ≠ false := by decide
  have hclose' : |x haltCoordU - haltBoolCode false| ≤ ((1 / 4 : ℚ) : ℝ) := by
    simpa [haltBoolCode] using hclose
  simpa [contractFlagIndicatorPackageU_ramp, contractFlagIndicatorPackageU_poly,
    haltFlagIndicatorPolyU_ramp, haltFlagIndicatorPolyU, haltFlagIndicatorAtomU,
    finiteCoordinateAtoms] using
    (haltFlagIndicatorAtomU (eta := (1 / 16 : ℚ)) (by norm_num)).off_tube
      true false x hneq hclose'

/-- **Replacement for the impossible `hLatchHcont`.**  `Hval ∘ sol.z` is
continuous: a rational multivariate polynomial evaluates continuously, composed
with the continuous `z` trajectory. -/
theorem contractFlagIndicatorPackageU_ramp_Hcont
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d_U → ℝ) → Fin d_U → ℝ}
    (sol : DynContractIteratorSol (Fin d_U) p sched F) :
    Continuous fun t => contractFlagIndicatorPackageU_ramp.Hval (sol.z t) := by
  have hz : Continuous fun t => sol.z t := continuous_pi sol.cont_z
  show Continuous fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) haltFlagIndicatorPolyU_ramp
  convert (MvPolynomial.continuous_eval
      (p := MvPolynomial.map (algebraMap ℚ ℝ) haltFlagIndicatorPolyU_ramp)).comp hz using 1
  ext t
  exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (sol.z t) haltFlagIndicatorPolyU_ramp

end

end MachineInstance

end Ripple.BoundedUniversality.BGP

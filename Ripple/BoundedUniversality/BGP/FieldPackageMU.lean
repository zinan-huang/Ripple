/-
Ripple.BoundedUniversality.BGP.FieldPackageMU
-------------------------
The concrete polynomial field realization `FP_MU_N` for the universal machine's
contract step `selectorContractF_N_U`, plus its `field_eval_identity`.

`selectorContractF_N_U branch atoms = fun _mu x i => evalPoly4 x (selectorTotalPolyN_U branch atoms i)`
(definitionally, `selectorContractF_N_U_eval`), and `evalPoly4 = MvPolynomial.eval₂ (algebraMap ℚ ℝ)`.
So the contract polynomial field is the existing six-coordinate selector polynomial
`selectorTotalPolyN_U` renamed into the contract `u`-block coordinates via `contractU`
(`contractRenameU`, the u-mirror of the existing `contractRenameZ`).  The
`field_eval_identity` then collapses by `eval₂_rename` + `contractTupleTraj_u`.
-/

import Ripple.BoundedUniversality.BGP.ContractMain
import Ripple.BoundedUniversality.BGP.ContractField
import Ripple.BoundedUniversality.BGP.MachineInstance

namespace Ripple.BoundedUniversality.BGP

open MachineInstance

noncomputable section

/-- Rename a `Fin d`-poly into the contract coordinates' `u`-block (mirror of
`contractRenameZ`). -/
def contractRenameU {d : ℕ} (p : MvPolynomial (Fin d) ℚ) :
    MvPolynomial (Fin (contractDim d)) ℚ :=
  MvPolynomial.rename (contractU (d := d)) p

/-- Evaluating a `contractRenameU`-lifted poly on the contract tuple trajectory
equals evaluating the original poly on the `u`-register (mirror of
`eval_contractRenameZ_tuple`). -/
lemma eval_contractRenameU_tuple {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ)
    (q : MvPolynomial (Fin d) ℚ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
        (contractRenameU q) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.u t) q := by
  rw [contractRenameU, MvPolynomial.eval₂_rename]
  exact MvPolynomial.eval₂_congr
    (f := algebraMap ℚ ℝ) (p := q)
    (g₁ := contractTupleTraj sol La t ∘ contractU) (g₂ := sol.u t)
    (fun {i} {_c} _hi _hc => contractTupleTraj_u sol La t i)

/-- The concrete contract polynomial field for `M_U`: the existing six-coordinate
N-atom selector polynomial, renamed into the contract `u`-block. -/
def FP_MU_N (eta : ℚ) (heta : 0 < eta) :
    Fin d_U → MvPolynomial (Fin (contractDim d_U)) ℚ :=
  fun i =>
    contractRenameU
      (selectorTotalPolyN_U branchU
        (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) i)

/-- **`field_eval_identity` for `FP_MU_N`.**  Evaluating `FP_MU_N` on the contract
tuple trajectory equals the contract step `selectorContractF_N_U` on the
`u`-register — by `eval_contractRenameU_tuple` + `selectorContractF_N_U_eval`
(`evalPoly4 = eval₂`). -/
theorem FP_MU_N_field_eval (eta : ℚ) (heta : 0 < eta)
    {p : DynGateParams} {sched : PhaseSchedule}
    (sol : DynContractIteratorSol (Fin d_U) p sched
      (selectorContractF_N_U branchU
        (gateSelectorAtomsCoordN (universalGateAtoms eta heta))))
    {flagCoord : Fin d_U} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ) (i : Fin d_U) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
        (FP_MU_N eta heta i) =
      selectorContractF_N_U branchU
        (gateSelectorAtomsCoordN (universalGateAtoms eta heta))
        (sol.μ t) (sol.u t) i := by
  simp only [FP_MU_N]
  rw [eval_contractRenameU_tuple, selectorContractF_N_U_eval]
  rfl

/-- **`hSupplyFieldEval` core for `M_U`.**  For an *arbitrary* trajectory `y`,
evaluating `FP_MU_N` equals the concrete contract step `selectorContractF_N_U` on
the `u`-block — a pure `eval₂_rename` identity (and `evalPoly4 = eval₂`).  At the
`bgp_unconditional_expEps_N` use-site, the assembled step's `.F` is
`selectorContractF_N_U branchU atoms` definitionally (through
`bgpStepContractN_assembled` / `robustStepContractN_U`), so this discharges the
`hSupplyFieldEval` hypothesis by defeq.  Stated against the concrete step (not the
`.F` wrapper) to avoid importing `FinalAssembly` (and the resulting import cycle
with the warmed headline). -/
theorem hSupplyFieldEval_MU (eta : ℚ) (heta : 0 < eta)
    (y : ℝ → Fin (contractDim d_U) → ℝ) (t : ℝ) (i : Fin d_U) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP_MU_N eta heta i) =
      selectorContractF_N_U branchU
        (gateSelectorAtomsCoordN (universalGateAtoms eta heta))
        (y t (contractMu d_U)) (fun k => y t (contractU k)) i := by
  simp only [FP_MU_N, contractRenameU, MvPolynomial.eval₂_rename,
    selectorContractF_N_U_eval]
  rfl

end

end Ripple.BoundedUniversality.BGP

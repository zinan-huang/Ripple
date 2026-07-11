import Ripple.BoundedUniversality.BGP.SelectorCorrectHaltEndToEnd

/-!
Ripple.BoundedUniversality.BGP.SelectorCorrectedAssembly
------------------------------------
Downstream wiring from the corrected next-config selector endpoint to the
`EventualThresholdSimulation` headline.

This file intentionally keeps the selector solution family abstract.  It does
not instantiate the concrete `solMU` term.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MachineInstance

/-- **M_U selector headline through the corrected next-config endpoint.**  The per-cycle
analytic premises are the satisfiable full-tile hypotheses consumed by
`selector_correct_halt_endtoend` / `selector_correct_nonhalt_endtoend`.  The final PIVP
packaging uses the same compactified selector field as `bgp_unconditional_selector_MU`,
but the chart readout is attached directly to the embedded `z[haltCoordU]` coordinate,
not to the auxiliary halt latch. -/
theorem bgp_unconditional_selector_MU_corrected
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ) (R : ℕ)
    (h_HP :
      ∀ (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ),
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
          MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (init : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℚ)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R)
        (i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * selectorTupleTraj sol La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 k ^ 2) + 1))
    (sol : ℕ → SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hHcont : ∀ w, Continuous fun t =>
      MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t))
    (rho deltaMix : ℕ → ℕ → ℝ)
    (hdom : ∀ (w j : ℕ), ∀ t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
        t ∈ selectorSchedule.domain)
    (hg_cont : ∀ w,
      Continuous (fun t => bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t))
    (hg0 : ∀ (w j : ℕ), ∀ t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t)
    (hmix : ∀ (w j : ℕ), ∀ t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |selectorMixTarget MachineInstance.branchU (sol w).u (sol w).lam t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j + 1] (MachineInstance.M_U.init w))
          MachineInstance.haltCoordU| ≤ deltaMix w j)
    (hstart : ∀ (w j : ℕ),
      |(sol w).z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j + 1] (MachineInstance.M_U.init w))
          MachineInstance.haltCoordU| ≤ rho w j)
    (hsmall : ∀ w j, rho w j + deltaMix w j ≤ 1 / 4)
    (hbox_hi : ∀ w t, (sol w).z t MachineInstance.haltCoordU ≤ 1)
    (hbox_lo : ∀ w t, 0 ≤ (sol w).z t MachineInstance.haltCoordU) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) := by
  classical
  let fieldPkg :=
    muSelectorFieldPackage eta heta M κ₀ g₀ HP
      MachineInstance.contractFlagIndicatorPackageU.Hval
      MachineInstance.K_U R (1 : ℚ) (by norm_num [MachineInstance.K_U]) h_HP
      init init_presented init_zero init_succ
  refine main_assembled_dyn_selector_zreadout
    UniversalMachine.undecidableMachine
    bgpParams38 selectorSchedule MachineInstance.branchU
    fieldPkg sol hHcont
    MachineInstance.haltCoordU
    (selZ MachineInstance.UniversalLocalView MachineInstance.haltCoordU)
    ?_ ?_ ?_
  · intro w s La t
    simp [fieldPkg, muSelectorFieldPackage, selectorPolynomialFieldPackage]
  · intro w hw
    have hwMU : MachineInstance.M_U.haltsOn w := by
      simpa [MachineInstance.M_U, UniversalMachine.undecidableMachine] using hw
    exact selector_correct_halt_endtoend (sol w) w hwMU
      (fun j => MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w))
      (fun j => rfl) (rho w) (deltaMix w)
      (hdom w) (hg_cont w) (hg0 w) (hmix w) (hstart w) (hsmall w) (hbox_hi w)
  · intro w hw
    have hwMU : ¬ MachineInstance.M_U.haltsOn w := by
      intro h
      exact hw (by simpa [MachineInstance.M_U, UniversalMachine.undecidableMachine] using h)
    exact selector_correct_nonhalt_endtoend (sol w) w hwMU
      (fun j => MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w))
      (fun j => rfl) (rho w) (deltaMix w)
      (hdom w) (hg_cont w) (hg0 w) (hmix w) (hstart w) (hsmall w) (hbox_lo w)

#print axioms bgp_unconditional_selector_MU_corrected

/-- **M_U selector headline through the corrected next-config endpoint, with no
halt-latch continuity premise.**  The compactified package uses a dummy zero
`a`-coordinate (`Hval := 0`, `K := 0`) and reads directly from
`z[haltCoordU]`. -/
theorem bgp_unconditional_selector_MU_corrected_nolatch
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ) (R : ℕ)
    (init : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℚ)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol (fun _ : (Fin MachineInstance.d_U → ℝ) => (0 : ℝ)) 0 R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol (fun _ : (Fin MachineInstance.d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * selectorTupleTraj sol La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 k ^ 2) + 1))
    (sol : ℕ → SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (rho deltaMix : ℕ → ℕ → ℝ)
    (hdom : ∀ (w j : ℕ), ∀ t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
        t ∈ selectorSchedule.domain)
    (hg_cont : ∀ w,
      Continuous (fun t => bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t))
    (hg0 : ∀ (w j : ℕ), ∀ t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t)
    (hmix : ∀ (w j : ℕ), ∀ t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |selectorMixTarget MachineInstance.branchU (sol w).u (sol w).lam t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j + 1] (MachineInstance.M_U.init w))
          MachineInstance.haltCoordU| ≤ deltaMix w j)
    (hstart : ∀ (w j : ℕ),
      |(sol w).z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j + 1] (MachineInstance.M_U.init w))
          MachineInstance.haltCoordU| ≤ rho w j)
    (hsmall : ∀ w j, rho w j + deltaMix w j ≤ 1 / 4)
    (hbox_hi : ∀ w t, (sol w).z t MachineInstance.haltCoordU ≤ 1)
    (hbox_lo : ∀ w t, 0 ≤ (sol w).z t MachineInstance.haltCoordU) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) := by
  classical
  let fieldPkg :=
    muSelectorFieldPackage eta heta M κ₀ g₀
      (0 : MvPolynomial (Fin MachineInstance.d_U) ℚ)
      (fun _ : (Fin MachineInstance.d_U → ℝ) => (0 : ℝ))
      0 R 0 (by norm_num)
      (by
        intro sol La t
        simp)
      init init_presented init_zero init_succ
  refine main_assembled_dyn_selector_zreadout_nolatch
    UniversalMachine.undecidableMachine
    bgpParams38 selectorSchedule MachineInstance.branchU
    fieldPkg sol
    MachineInstance.haltCoordU
    (selZ MachineInstance.UniversalLocalView MachineInstance.haltCoordU)
    ?_ ?_ ?_
  · intro w s La t
    simp [fieldPkg, muSelectorFieldPackage, selectorPolynomialFieldPackage]
  · intro w hw
    have hwMU : MachineInstance.M_U.haltsOn w := by
      simpa [MachineInstance.M_U, UniversalMachine.undecidableMachine] using hw
    exact selector_correct_halt_endtoend (sol w) w hwMU
      (fun j => MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w))
      (fun j => rfl) (rho w) (deltaMix w)
      (hdom w) (hg_cont w) (hg0 w) (hmix w) (hstart w) (hsmall w) (hbox_hi w)
  · intro w hw
    have hwMU : ¬ MachineInstance.M_U.haltsOn w := by
      intro h
      exact hw (by simpa [MachineInstance.M_U, UniversalMachine.undecidableMachine] using h)
    exact selector_correct_nonhalt_endtoend (sol w) w hwMU
      (fun j => MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w))
      (fun j => rfl) (rho w) (deltaMix w)
      (hdom w) (hg_cont w) (hg0 w) (hmix w) (hstart w) (hsmall w) (hbox_lo w)

#print axioms bgp_unconditional_selector_MU_corrected_nolatch

end Ripple.BoundedUniversality.BGP

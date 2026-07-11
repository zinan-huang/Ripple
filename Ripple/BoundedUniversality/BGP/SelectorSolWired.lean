import Ripple.BoundedUniversality.BGP.SelectorFinalAssembly
import Ripple.BoundedUniversality.BGP.SelectorAprioriBound38

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MachineInstance
open Set

noncomputable def solMU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin MachineInstance.d_U → ℚ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ)) (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ MachineInstance.UniversalLocalView HP)| ≤ Rbd) :
    ℕ → SelectorDynSol MachineInstance.d_U MachineInstance.B_U
        MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
        MachineInstance.branchU
        (fun t => ((1 + Real.cos t) / 2) ^ M)
        (fun t => ((1 + Real.sin t) / 2) ^ M)
        (fun _ => (κ₀ : ℝ))
        (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
        (universalPval eta heta) :=
  fun w =>
    (selector_sol_exists_MU38_clean eta heta M κ₀ g₀ HP Kq R x₀ w
      hκ0 hg0 hKq0 (hytcont w) (hRen w)).choose

theorem solMU_def
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin MachineInstance.d_U → ℚ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ)) (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ MachineInstance.UniversalLocalView HP)| ≤ Rbd)
    (w : ℕ) :
    solMU eta heta M κ₀ g₀ HP Kq R x₀ hκ0 hg0 hKq0 hytcont hRen w =
      (selector_sol_exists_MU38_clean eta heta M κ₀ g₀ HP Kq R x₀ w
        hκ0 hg0 hKq0 (hytcont w) (hRen w)).choose := rfl

attribute [irreducible] solMU

#print axioms solMU_def

theorem bgp_unconditional_selector_MU_solfree
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ) (R : ℕ)
    (h_HP :
      ∀ (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M)
          (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ),
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
          MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (init :
      ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℚ)
    (init_presented :
      ∃ f :
          ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) →
            ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M)
          (fun t => ((1 + Real.sin t) / 2) ^ M)
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
          (fun t => ((1 + Real.cos t) / 2) ^ M)
          (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R)
        (i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * selectorTupleTraj sol La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 k ^ 2) + 1))
    (Kq : ℚ)
    (x₀ : ℕ → Fin MachineInstance.d_U → ℚ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ)) (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ MachineInstance.UniversalLocalView HP)| ≤ Rbd)
    (hHcont : ∀ w, Continuous fun t =>
      MachineInstance.contractFlagIndicatorPackageU.Hval
        (((solMU eta heta M κ₀ g₀ HP Kq R x₀ hκ0 hg0 hKq0 hytcont hRen) w).z t))
    (hhigh : ∀ (w : ℕ)
        (La : SelectorHaltLatchSol
          ((solMU eta heta M κ₀ g₀ HP Kq R x₀ hκ0 hg0 hKq0 hytcont hRen) w)
          MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
      (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ selectorSchedule.zActiveWindow j,
        1 - MachineInstance.contractFlagIndicatorPackageU.eta ≤
          MachineInstance.contractFlagIndicatorPackageU.Hval
            (((solMU eta heta M κ₀ g₀ HP Kq R x₀ hκ0 hg0 hKq0 hytcont hRen) w).z t)) →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow : ∀ (w : ℕ)
        (La : SelectorHaltLatchSol
          ((solMU eta heta M κ₀ g₀ HP Kq R x₀ hκ0 hg0 hKq0 hytcont hRen) w)
          MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
      (∀ j : ℕ, ∀ t ∈ selectorSchedule.zActiveWindow j,
        MachineInstance.contractFlagIndicatorPackageU.Hval
          (((solMU eta heta M κ₀ g₀ HP Kq R x₀ hκ0 hg0 hKq0 hytcont hRen) w).z t) ≤
          MachineInstance.contractFlagIndicatorPackageU.eta) →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)
    (hflag_read : ∀ w j t, t ∈ selectorSchedule.zActiveWindow j →
      |((solMU eta heta M κ₀ g₀ HP Kq R x₀ hκ0 hg0 hKq0 hytcont hRen) w).z t
          MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc
            (UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
            MachineInstance.haltCoordU| ≤ 1 / 4)
    (hflag_dom : ∀ w j t, t ∈ selectorSchedule.zActiveWindow j →
      ((solMU eta heta M κ₀ g₀ HP Kq R x₀ hκ0 hg0 hKq0 hytcont hRen) w).z t
          MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) := by
  exact bgp_unconditional_selector_MU eta heta M κ₀ g₀ HP R h_HP
    init init_presented init_zero init_succ
    (solMU eta heta M κ₀ g₀ HP Kq R x₀ hκ0 hg0 hKq0 hytcont hRen)
    hHcont hhigh hlow hflag_read hflag_dom

end Ripple.BoundedUniversality.BGP

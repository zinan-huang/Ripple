import Ripple.BoundedUniversality.BGP.SelectorLocalViewSharp
import Ripple.BoundedUniversality.BGP.SelectorStackFaithful

/-!
Ripple.BoundedUniversality.BGP.SelectorGateSharpAssembly
------------------------------------

Assembly from the five read-coordinate tubes to the per-fixed-input gate-sharp
headline.  The halt coordinate and full `UTube` are deliberately not used here.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Turing.PartrecToTM2

/-- Thin assembly entry point for the five local-view read coordinates. -/
theorem selector_gate_sharp_of_coord_tubes
    (eta : ℚ) (heta : 0 < eta)
    {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
    (hctrl :
      |x MachineInstance.ctrlCoordU -
          (MachineInstance.confEncU c MachineInstance.ctrlCoordU : ℝ)| ≤
        MachineInstance.r_LE_U)
    (hmain :
      |x MachineInstance.mainStackCoordU -
          (MachineInstance.confEncU c MachineInstance.mainStackCoordU : ℝ)| ≤
        MachineInstance.r_LE_U)
    (hrev :
      |x MachineInstance.revStackCoordU -
          (MachineInstance.confEncU c MachineInstance.revStackCoordU : ℝ)| ≤
        MachineInstance.r_LE_U)
    (haux :
      |x MachineInstance.auxStackCoordU -
          (MachineInstance.confEncU c MachineInstance.auxStackCoordU : ℝ)| ≤
        MachineInstance.r_LE_U)
    (hdata :
      |x MachineInstance.dataStackCoordU -
          (MachineInstance.confEncU c MachineInstance.dataStackCoordU : ℝ)| ≤
        MachineInstance.r_LE_U) :
    GateAtomSharpnessN MachineInstance.universalViewSpecN
      (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
      x (MachineInstance.localViewU c) := by
  exact MachineInstance.universalGateAtoms_sharpness_of_localViewTube
    eta heta hctrl hmain hrev haux hdata

/-- The concrete selector stack code is exactly the configuration encoding at that stack coordinate. -/
theorem selectorStackCodeU_eq_confEnc (w : Nat) (s : Fin 4) (j : Nat) :
    selectorStackCodeU w s j =
      (MachineInstance.confEncU (selectorCfgU w j) (selectorStackCoordU s) : ℝ) := by
  unfold selectorStackCodeU selectorStackCoordU
  rw [← MachineInstance.stackMachineEncodingU_enc_eq]
  fin_cases s <;> rfl

/-- Divide the faithful read bound by the positive concrete `B_U^2` factor. -/
theorem selectorStackError_le_of_scaled_read
    {e rho : ℝ}
    (hread : (MachineInstance.B_U : ℝ) ^ (2 : Int) * e ≤ rho)
    (hrho :
      rho ≤ MachineInstance.r_LE_U * (MachineInstance.B_U : ℝ) ^ (2 : Int)) :
    e ≤ MachineInstance.r_LE_U := by
  have hBpos : 0 < (MachineInstance.B_U : ℝ) ^ (2 : Int) := by
    norm_num [MachineInstance.B_U]
  have hmul :
      (MachineInstance.B_U : ℝ) ^ (2 : Int) * e ≤
        (MachineInstance.B_U : ℝ) ^ (2 : Int) * MachineInstance.r_LE_U := by
    calc
      (MachineInstance.B_U : ℝ) ^ (2 : Int) * e ≤ rho := hread
      _ ≤ MachineInstance.r_LE_U * (MachineInstance.B_U : ℝ) ^ (2 : Int) := hrho
      _ = (MachineInstance.B_U : ℝ) ^ (2 : Int) * MachineInstance.r_LE_U := by ring
  nlinarith [hBpos, hmul]

/--
Faithful stack read, budgeted by `r_LE_U * B_U^2`, gives the coordinate tube
shape required by the local-view sharpness theorem.
-/
theorem stackError_le_of_faithful_read
    (w : Nat) (s : Fin 4) (x : Nat → ℝ) {rho : ℝ} (j : Nat)
    (hread :
      (MachineInstance.B_U : ℝ) ^ (2 : Int) *
          selectorStackErrorU w s x j ≤ rho)
    (hrho :
      rho ≤ MachineInstance.r_LE_U * (MachineInstance.B_U : ℝ) ^ (2 : Int)) :
    |x j - (MachineInstance.confEncU (selectorCfgU w j) (selectorStackCoordU s) : ℝ)| ≤
      MachineInstance.r_LE_U := by
  have herr : selectorStackErrorU w s x j ≤ MachineInstance.r_LE_U :=
    selectorStackError_le_of_scaled_read hread hrho
  simpa [selectorStackErrorU, selectorStackCodeU_eq_confEnc] using herr

/-- Exposure-weighted stack tube specialized through `selector_stack_faithful_read_of_tube`. -/
theorem stackError_le_of_faithful_tube
    (w : Nat) (s : Fin 4) (x : Nat → ℝ) {rho : ℝ} (j : Nat)
    (htube :
      ∀ n,
        expWeight (MachineInstance.B_U : ℝ) (selectorStackDepthU w s)
          (selectorStackErrorU w s x) n ≤ rho)
    (hrho :
      rho ≤ MachineInstance.r_LE_U * (MachineInstance.B_U : ℝ) ^ (2 : Int)) :
    |x j - (MachineInstance.confEncU (selectorCfgU w j) (selectorStackCoordU s) : ℝ)| ≤
      MachineInstance.r_LE_U := by
  exact stackError_le_of_faithful_read w s x j
    (selector_stack_faithful_read_of_tube w s x htube j) hrho

/--
Per-fixed-input gate sharpness from the four landed faithful stack tubes and a
carried control-coordinate tube.
-/
theorem selector_gate_sharp_of_stackTubes_and_control
    (eta : ℚ) (heta : 0 < eta) {w j : Nat}
    {u : Nat → Fin MachineInstance.d_U → ℝ} {rho : ℝ}
    (hrho :
      rho ≤ MachineInstance.r_LE_U * (MachineInstance.B_U : ℝ) ^ (2 : Int))
    (hctrl :
      |u j MachineInstance.ctrlCoordU -
          (MachineInstance.confEncU (selectorCfgU w j) MachineInstance.ctrlCoordU : ℝ)| ≤
        MachineInstance.r_LE_U)
    (hmain :
      ∀ n,
        expWeight (MachineInstance.B_U : ℝ)
          (selectorStackDepthU w (MachineInstance.stackIndexU K'.main))
          (selectorStackErrorU w (MachineInstance.stackIndexU K'.main)
            (fun m => u m MachineInstance.mainStackCoordU)) n ≤ rho)
    (hrev :
      ∀ n,
        expWeight (MachineInstance.B_U : ℝ)
          (selectorStackDepthU w (MachineInstance.stackIndexU K'.rev))
          (selectorStackErrorU w (MachineInstance.stackIndexU K'.rev)
            (fun m => u m MachineInstance.revStackCoordU)) n ≤ rho)
    (haux :
      ∀ n,
        expWeight (MachineInstance.B_U : ℝ)
          (selectorStackDepthU w (MachineInstance.stackIndexU K'.aux))
          (selectorStackErrorU w (MachineInstance.stackIndexU K'.aux)
            (fun m => u m MachineInstance.auxStackCoordU)) n ≤ rho)
    (hdata :
      ∀ n,
        expWeight (MachineInstance.B_U : ℝ)
          (selectorStackDepthU w (MachineInstance.stackIndexU K'.stack))
          (selectorStackErrorU w (MachineInstance.stackIndexU K'.stack)
            (fun m => u m MachineInstance.dataStackCoordU)) n ≤ rho) :
    GateAtomSharpnessN MachineInstance.universalViewSpecN
      (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
      (u j) (MachineInstance.localViewU (selectorCfgU w j)) := by
  refine selector_gate_sharp_of_coord_tubes eta heta hctrl ?_ ?_ ?_ ?_
  · simpa [selectorStackCoordU, MachineInstance.stackCoordFinU,
      MachineInstance.stackIndexU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU] using
      stackError_le_of_faithful_tube w (MachineInstance.stackIndexU K'.main)
        (fun m => u m MachineInstance.mainStackCoordU) j hmain hrho
  · simpa [selectorStackCoordU, MachineInstance.stackCoordFinU,
      MachineInstance.stackIndexU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU] using
      stackError_le_of_faithful_tube w (MachineInstance.stackIndexU K'.rev)
        (fun m => u m MachineInstance.revStackCoordU) j hrev hrho
  · simpa [selectorStackCoordU, MachineInstance.stackCoordFinU,
      MachineInstance.stackIndexU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU] using
      stackError_le_of_faithful_tube w (MachineInstance.stackIndexU K'.aux)
        (fun m => u m MachineInstance.auxStackCoordU) j haux hrho
  · simpa [selectorStackCoordU, MachineInstance.stackCoordFinU,
      MachineInstance.stackIndexU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU] using
      stackError_le_of_faithful_tube w (MachineInstance.stackIndexU K'.stack)
        (fun m => u m MachineInstance.dataStackCoordU) j hdata hrho

end Ripple.BoundedUniversality.BGP

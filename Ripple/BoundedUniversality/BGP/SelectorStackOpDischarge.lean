import Ripple.BoundedUniversality.BGP.SelectorStackFaithful

/-!
Ripple.BoundedUniversality.BGP.SelectorStackOpDischarge
------------------------------------

Discharge of the branch-action part of `SelectorStackOpClassification` for the
concrete universal-machine selector.

The remaining hypothesis is the public semantic bridge from the concrete
private stack-move classifier in `MachineInstance` to direct list-depth
bookkeeping.  It is stated at the machine-step level, not as the classification
record itself.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

/-- Coordinate vector that replaces exactly the selected stack coordinate by the analog value. -/
def selectorStackAnalogStateU (w : Nat) (s : Fin 4) (x : Nat → Real) (j : Nat) :
    Fin MachineInstance.d_U → Real :=
  fun i => if i = selectorStackCoordU s then x j
    else MachineInstance.stackMachineEncodingU.enc (selectorCfgU w j) i

/-- The exact encoding of a selected concrete stack coordinate is its stack code. -/
theorem selectorStackEnc_eq (w : Nat) (s : Fin 4) (j : Nat) :
    MachineInstance.stackMachineEncodingU.enc (selectorCfgU w j) (selectorStackCoordU s) =
      selectorStackCodeU w s j := by
  unfold selectorStackCodeU selectorStackCoordU
  rw [MachineInstance.stackMachineEncodingU_enc_eq]
  fin_cases s <;> rfl

@[simp] theorem selectorStackAnalogStateU_self
    (w : Nat) (s : Fin 4) (x : Nat → Real) (j : Nat) :
    selectorStackAnalogStateU w s x j (selectorStackCoordU s) = x j := by
  simp [selectorStackAnalogStateU]

/-- Error of the selected coordinate in the single-coordinate analog vector. -/
theorem selectorStackAnalogStateU_error
    (w : Nat) (s : Fin 4) (x : Nat → Real) (j : Nat) :
    |selectorStackAnalogStateU w s x j (selectorStackCoordU s) -
        MachineInstance.stackMachineEncodingU.enc (selectorCfgU w j) (selectorStackCoordU s)| =
      selectorStackErrorU w s x j := by
  simp [selectorStackAnalogStateU, selectorStackErrorU, selectorStackEnc_eq]

/-- The symbolic affine stack operation selected by the concrete universal-machine branch. -/
def selectorStackOpTargetU (w : Nat) (s : Fin 4) (x : Nat → Real) : Nat → Real :=
  fun j =>
    BranchData.evalBranch
      (MachineInstance.branchU (MachineInstance.localViewU (selectorCfgU w j)))
      (selectorStackAnalogStateU w s x j) (selectorStackCoordU s)

/--
Public semantic bridge still needed for direct list-depth bookkeeping.

`MachineInstance.moveTypeStackU` is public, but the list classifier it unfolds to
is private to `MachineInstance`; this hypothesis is the exact machine-step
statement needed to turn `coordDelta` into the depth field of
`SelectorStackOpClassification`.
-/
def SelectorStackDepthStepSemanticsU : Prop :=
  ∀ c : MachineInstance.UConf, ∀ s : Fin 4,
    ((MachineInstance.indexedStackU (MachineInstance.M_U.step c) s).length : Int) =
      ((MachineInstance.indexedStackU c s).length : Int) -
        MachineInstance.stackMachineEncodingU.coordDelta c (selectorStackCoordU s)

/-- The concrete universal-machine iterator advances by one `M_U.step`. -/
theorem selectorCfgU_succ (w j : Nat) :
    selectorCfgU w (j + 1) = MachineInstance.M_U.step (selectorCfgU w j) := by
  simp [selectorCfgU, Function.iterate_succ_apply']

/-- Direct stack depth recurrence along the orbit, from the public semantic bridge. -/
theorem selectorStackDepthU_step_of_semantics
    (hdepth : SelectorStackDepthStepSemanticsU)
    (w : Nat) (s : Fin 4) (j : Nat) :
    selectorStackDepthU w s (j + 1) =
      selectorStackDepthU w s j -
        MachineInstance.stackMachineEncodingU.coordDelta
          (selectorCfgU w j) (selectorStackCoordU s) := by
  have h := hdepth (selectorCfgU w j) s
  rw [← selectorCfgU_succ w j] at h
  unfold selectorStackDepthU selectorStackCoordU
  rw [MachineInstance.depthU_stack, MachineInstance.depthU_stack]
  exact h

/-- The selected branch action gives the exposure-weighted operation error. -/
theorem selectorStackOpTargetU_error
    (hdepth : SelectorStackDepthStepSemanticsU)
    (w : Nat) (s : Fin 4) (x : Nat → Real) (j : Nat) :
    |selectorStackOpTargetU w s x j - selectorStackCodeU w s (j + 1)| <=
      (MachineInstance.B_U : Real) ^
          (selectorStackDepthU w s j - selectorStackDepthU w s (j + 1)) *
        selectorStackErrorU w s x j := by
  let c := selectorCfgU w j
  let i := selectorStackCoordU s
  let Z := selectorStackAnalogStateU w s x j
  have hcontract := MachineInstance.branchU_branchContractClause c
  have hdiag := BranchContractClause.zpow_diagonal hcontract Z i
  have hnext : selectorCfgU w (j + 1) = MachineInstance.M_U.step c := by
    simpa [c] using selectorCfgU_succ w j
  have hcode_next :
      MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i =
        selectorStackCodeU w s (j + 1) := by
    rw [← hnext]
    simpa [i] using selectorStackEnc_eq w s (j + 1)
  have hdelta :
      MachineInstance.stackMachineEncodingU.coordDelta c i =
        selectorStackDepthU w s j - selectorStackDepthU w s (j + 1) := by
    have hd := selectorStackDepthU_step_of_semantics hdepth w s j
    rw [hd]
    ring
  have hZerr :
      |Z i - MachineInstance.stackMachineEncodingU.enc c i| =
        selectorStackErrorU w s x j := by
    simpa [Z, c, i] using selectorStackAnalogStateU_error w s x j
  rw [hcode_next, hdelta, hZerr] at hdiag
  simpa [selectorStackOpTargetU, c, i, Z, MachineInstance.stackMachineEncodingU] using hdiag

/--
Discharge of `SelectorStackOpClassification` modulo the direct stack-depth
semantic bridge.
-/
theorem selectorStackOpClassificationU
    (hdepth : SelectorStackDepthStepSemanticsU)
    (w : Nat) (s : Fin 4) (x : Nat → Real) :
    ∀ j, SelectorStackOpClassification w s x (selectorStackOpTargetU w s x) j := by
  intro j
  exact {
    next_cfg := selectorCfgU_succ w j
    depth_step := selectorStackDepthU_step_of_semantics hdepth w s j
    op_error := selectorStackOpTargetU_error hdepth w s x j
  }

#print axioms selectorStackOpClassificationU

end Ripple.BoundedUniversality.BGP

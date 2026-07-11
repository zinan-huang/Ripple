import Ripple.BoundedUniversality.BGP.SelectorDepthBound
import Ripple.BoundedUniversality.BGP.WarmIndexMU

/-!
Ripple.BoundedUniversality.BGP.SelectorDepthLinear
------------------------------
I4 (depth side): the linear depth bound `H(j+1) ≤ Nw + j` from the stack-depth
step semantics. `Nw := maxInitialStackDepth + 1` absorbs the `H 1 ≤ |w|+1`
off-by-one so the hypothesis matches the warm-reserve `hHpre` shape exactly.

The growth-only height bounds are unconditional: they use the concrete
list-length theorem `M_U_stack_growth_le_one`, routed through
`SelectorDepthBound`.  The old `SelectorStackDepthStepSemanticsU`-parameterized
theorems remain as compatibility wrappers for callers that still carry exact
push/pop depth semantics.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance

/-- Maximum initial stack depth over the four stack coordinates (a `w`-dependent ℕ; for the concrete
`M_U.init` it is essentially `|w|` on the main stack and `0` elsewhere). -/
def maxInitialStackDepthU (w : ℕ) : ℤ :=
  max (max (selectorStackDepthU w 0 0) (selectorStackDepthU w 1 0))
      (max (selectorStackDepthU w 2 0) (selectorStackDepthU w 3 0))

/-- The warm-up depth parameter `Nw = maxInitialStackDepth + 1` (the `+1` absorbs the `H 1 ≤ |w|+1`
off-by-one so `H(j+1) ≤ Nw + j` holds from cycle 0). -/
def warmupDepthN_U (w : ℕ) : ℤ :=
  maxInitialStackDepthU w + 1

theorem selectorStackDepthU_le_max_initial (w : ℕ) (s : Fin 4) :
    selectorStackDepthU w s 0 ≤ maxInitialStackDepthU w := by
  unfold maxInitialStackDepthU
  fin_cases s
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- **The corrected linear depth bound.** From the true `C=1` growth,
`H(j) ≤ H(0) + j`, hence `H(j+1) ≤ Nw + j` with
`Nw = maxInitialStackDepth + 1`.
This is the warm-reserve hypothesis shape. -/
theorem selectorStackDepthU_le_initial_add
    (_hsem : SelectorStackDepthStepSemanticsU) (w : ℕ) (s : Fin 4) :
    ∀ j, selectorStackDepthU w s j ≤ selectorStackDepthU w s 0 + (j : ℤ) :=
  selectorStackDepthU_le_initial_add_unconditional w s

theorem selectorStackDepthU_succ_le_warmupN_unconditional (w : ℕ) (s : Fin 4) :
    ∀ j, selectorStackDepthU w s (j + 1) ≤ warmupDepthN_U w + (j : ℤ) := by
  intro j
  have h := selectorStackDepthU_le_initial_add_unconditional w s (j + 1)
  have h0 := selectorStackDepthU_le_max_initial w s
  unfold warmupDepthN_U
  push_cast at h ⊢
  omega

theorem selectorStackDepthU_succ_le_warmupN
    (_hsem : SelectorStackDepthStepSemanticsU) (w : ℕ) (s : Fin 4) :
    ∀ j, selectorStackDepthU w s (j + 1) ≤ warmupDepthN_U w + (j : ℤ) :=
  selectorStackDepthU_succ_le_warmupN_unconditional w s

/-- The initial selected stack depth is bounded by the global input-depth
maximum used by the warm-reserve index. -/
theorem selectorStackDepthU_initial_le_inputDepthU (w : ℕ) (s : Fin 4) :
    selectorStackDepthU w s 0 ≤ (MachineInstance.inputDepthU w : ℤ) := by
  have hnonneg : 0 ≤ selectorStackDepthU w s 0 :=
    selectorStackDepthU_nonneg w s 0
  have hnat :
      Int.toNat (selectorStackDepthU w s 0) ≤ MachineInstance.inputDepthU w := by
    have hsup :=
      Finset.le_sup
        (s := Finset.univ)
        (f := fun i : Fin d_U => MachineInstance.depthHeightU w 0 i)
        (Finset.mem_univ (selectorStackCoordU s))
    simpa [MachineInstance.inputDepthU, MachineInstance.depthHeightU,
      selectorStackDepthU, selectorCfgU, MachineInstance.cU] using hsup
  have hcast :
      ((Int.toNat (selectorStackDepthU w s 0) : ℕ) : ℤ) =
        selectorStackDepthU w s 0 :=
    Int.toNat_of_nonneg hnonneg
  exact hcast ▸ (by exact_mod_cast hnat)

/-- The `+1` input-length buffer dominates the old `warmupDepthN_U` bound. -/
theorem warmupDepthN_U_le_inputLenU_one (w : ℕ) :
    warmupDepthN_U w ≤ (MachineInstance.inputLenU 1 w : ℤ) := by
  have h0 := selectorStackDepthU_initial_le_inputDepthU w 0
  have h1 := selectorStackDepthU_initial_le_inputDepthU w 1
  have h2 := selectorStackDepthU_initial_le_inputDepthU w 2
  have h3 := selectorStackDepthU_initial_le_inputDepthU w 3
  have hmax :
      maxInitialStackDepthU w ≤ (MachineInstance.inputDepthU w : ℤ) := by
    unfold maxInitialStackDepthU
    exact max_le (max_le h0 h1) (max_le h2 h3)
  unfold warmupDepthN_U MachineInstance.inputLenU
  omega

/-- Any input-length buffer at least one dominates the old `warmupDepthN_U`
bound. -/
theorem warmupDepthN_U_le_inputLenU {C_U : ℕ} (hC : 1 ≤ C_U) (w : ℕ) :
    warmupDepthN_U w ≤ (MachineInstance.inputLenU C_U w : ℤ) := by
  have h1 := warmupDepthN_U_le_inputLenU_one w
  unfold MachineInstance.inputLenU at h1 ⊢
  omega

/-- Stack-coordinate height bound in the exact warm-reserve `hHpre` shape. -/
theorem selectorStackDepthU_succ_le_inputLenU_unconditional
    {C_U : ℕ} (hC : 1 ≤ C_U) (w : ℕ) (s : Fin 4) :
    ∀ j, (selectorStackDepthU w s (j + 1) : ℝ)
      ≤ (MachineInstance.inputLenU C_U w : ℝ) + (j : ℝ) := by
  intro j
  have hdepth := selectorStackDepthU_succ_le_warmupN_unconditional w s j
  have hN := warmupDepthN_U_le_inputLenU hC w
  have hint :
      selectorStackDepthU w s (j + 1)
        ≤ (MachineInstance.inputLenU C_U w : ℤ) + (j : ℤ) := by
    omega
  exact_mod_cast hint

/-- Compatibility wrapper for callers that still carry exact depth semantics. -/
theorem selectorStackDepthU_succ_le_inputLenU
    (_hsem : SelectorStackDepthStepSemanticsU)
    {C_U : ℕ} (hC : 1 ≤ C_U) (w : ℕ) (s : Fin 4) :
    ∀ j, (selectorStackDepthU w s (j + 1) : ℝ)
      ≤ (MachineInstance.inputLenU C_U w : ℝ) + (j : ℝ) :=
  selectorStackDepthU_succ_le_inputLenU_unconditional hC w s

/-- Universal-coordinate height bound in the exact warm-reserve `hHpre` shape. -/
theorem depthU_cU_succ_le_inputLenU_unconditional
    {C_U : ℕ} (hC : 1 ≤ C_U) (w : ℕ) (i : Fin d_U) :
    ∀ j, (MachineInstance.depthU (MachineInstance.cU w) (j + 1) i : ℝ)
      ≤ (MachineInstance.inputLenU C_U w : ℝ) + (j : ℝ) := by
  intro j
  fin_cases i
  · simpa [MachineInstance.cU, selectorCfgU, selectorStackDepthU,
      selectorStackCoordU, MachineInstance.stackMachineEncodingU,
      MachineInstance.stackCoordFinU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU, MachineInstance.mainStackCoordU] using
      selectorStackDepthU_succ_le_inputLenU_unconditional hC w 0 j
  · simpa [MachineInstance.cU, selectorCfgU, selectorStackDepthU,
      selectorStackCoordU, MachineInstance.stackMachineEncodingU,
      MachineInstance.stackCoordFinU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU, MachineInstance.revStackCoordU] using
      selectorStackDepthU_succ_le_inputLenU_unconditional hC w 1 j
  · simpa [MachineInstance.cU, selectorCfgU, selectorStackDepthU,
      selectorStackCoordU, MachineInstance.stackMachineEncodingU,
      MachineInstance.stackCoordFinU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU, MachineInstance.auxStackCoordU] using
      selectorStackDepthU_succ_le_inputLenU_unconditional hC w 2 j
  · simpa [MachineInstance.cU, selectorCfgU, selectorStackDepthU,
      selectorStackCoordU, MachineInstance.stackMachineEncodingU,
      MachineInstance.stackCoordFinU, MachineInstance.stackKindOfIndexU,
      MachineInstance.stackCoordU, MachineInstance.dataStackCoordU] using
      selectorStackDepthU_succ_le_inputLenU_unconditional hC w 3 j
  · have hidx :
        stackMachineEncodingU.coordStackIndex ctrlCoordU = none := by
      simp [stackMachineEncodingU]
    change (MachineInstance.depthU (MachineInstance.cU w) (j + 1) ctrlCoordU : ℝ)
      ≤ (MachineInstance.inputLenU C_U w : ℝ) + (j : ℝ)
    rw [MachineInstance.depthU_reset (MachineInstance.cU w) (j + 1) ctrlCoordU hidx]
    have hN : (0 : ℝ) ≤ (MachineInstance.inputLenU C_U w : ℝ) := by
      exact_mod_cast Nat.zero_le (MachineInstance.inputLenU C_U w)
    have hj : (0 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast Nat.zero_le j
    simpa using add_nonneg hN hj
  · have hidx :
        stackMachineEncodingU.coordStackIndex haltCoordU = none := by
      simp [stackMachineEncodingU]
    change (MachineInstance.depthU (MachineInstance.cU w) (j + 1) haltCoordU : ℝ)
      ≤ (MachineInstance.inputLenU C_U w : ℝ) + (j : ℝ)
    rw [MachineInstance.depthU_reset (MachineInstance.cU w) (j + 1) haltCoordU hidx]
    have hN : (0 : ℝ) ≤ (MachineInstance.inputLenU C_U w : ℝ) := by
      exact_mod_cast Nat.zero_le (MachineInstance.inputLenU C_U w)
    have hj : (0 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast Nat.zero_le j
    simpa using add_nonneg hN hj

/-- Compatibility wrapper for callers that still carry exact depth semantics. -/
theorem depthU_cU_succ_le_inputLenU
    (_hsem : SelectorStackDepthStepSemanticsU)
    {C_U : ℕ} (hC : 1 ≤ C_U) (w : ℕ) (i : Fin d_U) :
    ∀ j, (MachineInstance.depthU (MachineInstance.cU w) (j + 1) i : ℝ)
      ≤ (MachineInstance.inputLenU C_U w : ℝ) + (j : ℝ) :=
  depthU_cU_succ_le_inputLenU_unconditional hC w i

#print axioms selectorStackDepthU_initial_le_inputDepthU
#print axioms warmupDepthN_U_le_inputLenU_one
#print axioms warmupDepthN_U_le_inputLenU
#print axioms selectorStackDepthU_succ_le_warmupN_unconditional
#print axioms selectorStackDepthU_succ_le_inputLenU_unconditional
#print axioms selectorStackDepthU_succ_le_inputLenU
#print axioms depthU_cU_succ_le_inputLenU_unconditional
#print axioms depthU_cU_succ_le_inputLenU

end Ripple.BoundedUniversality.BGP

import Ripple.BoundedUniversality.BGP.MachineInstance

/-!
Ripple.BoundedUniversality.BGP.SelectorLocalViewSharp
----------------------------------

Gate sharpness from exactly the local-view coordinates read by the universal
gate selector.  This avoids requiring a full six-coordinate `UTube`: the halt
coordinate is not part of `localViewU`, and it is not used here.
-/

namespace Ripple.BoundedUniversality.BGP.MachineInstance

open UniversalMachine
open Turing.PartrecToTM2

noncomputable section

private theorem ctrl_tube_close_of_coord {c : UConf} {x : Fin d_U → ℝ}
    (hctrl : |x ctrlCoordU - (confEncU c ctrlCoordU : ℝ)| ≤ r_LE_U) :
    |x ctrlCoordU - (ctrlVarCodeU c.1 c.2.1 : ℝ)| ≤ (1 / 4 : ℝ) := by
  have h := hctrl
  rw [confEncU_ctrl] at h
  have hr : r_LE_U ≤ (1 / 4 : ℝ) := by norm_num [r_LE_U]
  have hx :
      |x ctrlCoordU - (ctrlVarCodeU c.1 c.2.1 : ℝ)| ≤ r_LE_U := by
    have hcast :
        (((ctrlVarCodeU c.1 c.2.1 : ℤ) : ℚ) : ℝ) =
          (ctrlVarCodeU c.1 c.2.1 : ℝ) := by
      push_cast
      ring
    rwa [hcast] at h
  linarith

private theorem stackTop_tube_widened_of_coord {c : UConf} {x : Fin d_U → ℝ}
    {coord : Fin d_U} {L : List Γ'}
    (hcoordTube : |x coord - (confEncU c coord : ℝ)| ≤ r_LE_U)
    (hcoord : confEncU c coord = (stackCodeU B_U gammaDigit L : ℚ)) :
    topLoU (stackTopU L) - r_LE_U ≤ x coord ∧
      x coord ≤ topHiU (stackTopU L) + r_LE_U := by
  have h := hcoordTube
  rw [hcoord] at h
  have hmem := stackCodeU_mem_topInterval L
  have habs := abs_le.mp h
  exact ⟨by linarith [hmem.1, habs.1], by linarith [hmem.2, habs.2]⟩

private theorem mainPair_tube_widened_of_coord {c : UConf} {x : Fin d_U → ℝ}
    (hmain : |x mainStackCoordU - (confEncU c mainStackCoordU : ℝ)| ≤ r_LE_U) :
    (mainPairLoQ (stackTopU (mainStackU c), stackSecondU (mainStackU c)) : ℝ) - r_LE_U ≤
        x mainStackCoordU ∧
      x mainStackCoordU ≤
        (mainPairHiQ (stackTopU (mainStackU c), stackSecondU (mainStackU c)) : ℝ) + r_LE_U := by
  have h := hmain
  rw [confEncU_main] at h
  have hmem := stackCodeU_mem_mainPairInterval (mainStackU c)
  have habs := abs_le.mp h
  exact ⟨by linarith [hmem.1, habs.1], by linarith [hmem.2, habs.2]⟩

theorem universalGateAtoms_inWorkingDomain_of_localViewTube
    (eta : ℚ) (heta : 0 < eta) {c : UConf} {x : Fin d_U → ℝ}
    (hctrl : |x ctrlCoordU - (confEncU c ctrlCoordU : ℝ)| ≤ r_LE_U)
    (hmain : |x mainStackCoordU - (confEncU c mainStackCoordU : ℝ)| ≤ r_LE_U)
    (hrev : |x revStackCoordU - (confEncU c revStackCoordU : ℝ)| ≤ r_LE_U)
    (haux : |x auxStackCoordU - (confEncU c auxStackCoordU : ℝ)| ≤ r_LE_U)
    (hdata : |x dataStackCoordU - (confEncU c dataStackCoordU : ℝ)| ≤ r_LE_U) :
    (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).inWorkingDomain x := by
  have hstack : ∀ (coord : Fin d_U) (L : List Γ'),
      confEncU c coord = (stackCodeU B_U gammaDigit L : ℚ) →
        |x coord - (confEncU c coord : ℝ)| ≤ r_LE_U →
          |x coord| ≤ ((1 : ℚ) : ℝ) := by
    intro coord L hcoord hcoordTube
    have h := hcoordTube
    rw [hcoord] at h
    have hg := stackCodeU_mem_gap_range L
    have hle : ((stackCodeU B_U gammaDigit L : ℚ) : ℝ) ≤ 2 / 3 := by
      have hh := hg.2.1
      have h23 : ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℝ) = 2 / 3 := by
        norm_num [bot, B_U]
      calc ((stackCodeU B_U gammaDigit L : ℚ) : ℝ)
          ≤ ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℝ) := by exact_mod_cast hh
        _ = 2 / 3 := h23
    have hpos : (0 : ℝ) ≤ ((stackCodeU B_U gammaDigit L : ℚ) : ℝ) := by
      exact_mod_cast hg.1.le
    have hrle : r_LE_U ≤ 1 / 3 := by norm_num [r_LE_U]
    obtain ⟨habs1, habs2⟩ := abs_le.mp h
    rw [abs_le]
    push_cast
    constructor <;> linarith
  intro k
  fin_cases k
  · show |x ctrlCoordU| ≤
        ((2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ')) + 1 : ℚ) : ℝ)
    have h := hctrl
    rw [confEncU_ctrl] at h
    have hidx :
        ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (c.1, c.2.1)).val <
          Fintype.card (Option (SuppLabel c_f) × Option Γ') :=
      (Fintype.equivFin (Option (SuppLabel c_f) × Option Γ') (c.1, c.2.1)).isLt
    have hcle : (ctrlVarCodeU c.1 c.2.1 : ℝ) ≤
        2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) := by
      unfold ctrlVarCodeU
      push_cast
      have hidxle :
          (((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (c.1, c.2.1)).val : ℝ) ≤
            (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) := by
        exact_mod_cast hidx.le
      have hmul :
          (2 : ℝ) *
              (((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (c.1, c.2.1)).val : ℝ) ≤
            2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) :=
        mul_le_mul_of_nonneg_left hidxle (by norm_num)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hcnn : (0 : ℝ) ≤ (ctrlVarCodeU c.1 c.2.1 : ℝ) := by
      unfold ctrlVarCodeU
      positivity
    have hrle : r_LE_U ≤ 1 := by norm_num [r_LE_U]
    obtain ⟨habs1, habs2⟩ := abs_le.mp h
    rw [abs_le]
    push_cast
    push_cast at habs1 habs2
    constructor <;> linarith
  · exact hstack mainStackCoordU (mainStackU c) (confEncU_main c) hmain
  · exact hstack revStackCoordU (revStackU c) (confEncU_rev c) hrev
  · exact hstack auxStackCoordU (auxStackU c) (confEncU_aux c) haux
  · exact hstack dataStackCoordU (dataStackU c) (confEncU_data c) hdata

theorem universalGateAtoms_sharpness_of_localViewTube
    (eta : ℚ) (heta : 0 < eta) {c : UConf} {x : Fin d_U → ℝ}
    (hctrl : |x ctrlCoordU - (confEncU c ctrlCoordU : ℝ)| ≤ r_LE_U)
    (hmain : |x mainStackCoordU - (confEncU c mainStackCoordU : ℝ)| ≤ r_LE_U)
    (hrev : |x revStackCoordU - (confEncU c revStackCoordU : ℝ)| ≤ r_LE_U)
    (haux : |x auxStackCoordU - (confEncU c auxStackCoordU : ℝ)| ≤ r_LE_U)
    (hdata : |x dataStackCoordU - (confEncU c dataStackCoordU : ℝ)| ≤ r_LE_U) :
    GateAtomSharpnessN universalViewSpecN
      (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) x (localViewU c) := by
  apply gateAtomSharpnessN_of_coord_atoms
  · exact universalGateAtoms_inWorkingDomain_of_localViewTube
      eta heta hctrl hmain hrev haux hdata
  · intro k
    fin_cases k
    · refine ⟨(c.1, c.2.1), ?_, ?_⟩
      · rfl
      · simpa [SlabAtomicSelectorData.toCoordAtomData, controlAtomSlab,
          finiteCoordinateAtoms] using ctrl_tube_close_of_coord hctrl
    · refine ⟨(stackTopU (mainStackU c), stackSecondU (mainStackU c)), ?_, ?_⟩
      · rfl
      · exact mainPair_tube_widened_of_coord hmain
    · refine ⟨stackTopU (revStackU c), ?_, ?_⟩
      · rfl
      · exact stackTop_tube_widened_of_coord hrev (confEncU_rev c)
    · refine ⟨stackTopU (auxStackU c), ?_, ?_⟩
      · rfl
      · exact stackTop_tube_widened_of_coord haux (confEncU_aux c)
    · refine ⟨stackTopU (dataStackU c), ?_, ?_⟩
      · rfl
      · exact stackTop_tube_widened_of_coord hdata (confEncU_data c)

end

end Ripple.BoundedUniversality.BGP.MachineInstance

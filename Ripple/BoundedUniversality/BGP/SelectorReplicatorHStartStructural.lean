import Ripple.BoundedUniversality.BGP.SelectorReplicatorHStart
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorHStartStructural
----------------------------------------------
Structural/positivity producers for the replicator `hstart` path.

This file discharges the non-inductive inputs for the concrete selector write
window.  The analytic continuity inputs for the gate clocks come directly from
`SelectorReplicatorDynSol`: `α` and `μ` are coordinates of the assembled
trajectory.
-/

noncomputable section

open scoped BigOperators Topology

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance

namespace StackMachineEncoding

variable {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}

theorem stackMultiplier_nonneg (E : StackMachineEncoding d nS M) (c : Conf) (s : Fin nS) :
    0 ≤ E.stackMultiplier c s := by
  unfold stackMultiplier
  exact zpow_nonneg (Nat.cast_nonneg E.k) _

theorem coordMultiplier_nonneg (E : StackMachineEncoding d nS M) (c : Conf) (i : Fin d) :
    0 ≤ E.coordMultiplier c i := by
  unfold coordMultiplier
  cases h : E.coordStackIndex i with
  | none =>
      simp [h]
  | some s =>
      simpa [h] using E.stackMultiplier_nonneg c s

theorem stackMultiplier_le_base (E : StackMachineEncoding d nS M) (c : Conf) (s : Fin nS) :
    E.stackMultiplier c s ≤ (E.k : ℝ) := by
  have hk1 : (1 : ℝ) < (E.k : ℝ) := E.one_lt_base_real
  cases hmove : E.moveType c s with
  | pop =>
      simp [stackMultiplier, stackDelta, StackMove.delta, hmove]
  | push =>
      have hinv : ((E.k : ℝ)⁻¹ : ℝ) ≤ 1 := inv_le_one_of_one_le₀ hk1.le
      have hle : ((E.k : ℝ)⁻¹ : ℝ) ≤ (E.k : ℝ) := hinv.trans hk1.le
      simpa [stackMultiplier, stackDelta, StackMove.delta, hmove] using hle
  | stay =>
      simpa [stackMultiplier, stackDelta, StackMove.delta, hmove] using hk1.le

theorem coordMultiplier_le_base (E : StackMachineEncoding d nS M) (c : Conf) (i : Fin d) :
    E.coordMultiplier c i ≤ (E.k : ℝ) := by
  unfold coordMultiplier
  cases h : E.coordStackIndex i with
  | none =>
      simpa [h] using (Nat.cast_nonneg E.k : (0 : ℝ) ≤ (E.k : ℝ))
  | some s =>
      simpa [h] using E.stackMultiplier_le_base c s

end StackMachineEncoding

theorem bGateZ_comp_continuous {L : ℕ} {μ : ℝ → ℝ} (hμ : Continuous μ) :
    Continuous fun t : ℝ => bGateZ L (μ t) t := by
  unfold bGateZ
  exact Real.continuous_exp.comp ((hμ.mul (rPulse_continuous L)).neg)

theorem selector_replicator_gateZ_integrand_continuous
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch
      chiReset chiGate kappa gain readoutP) :
    Continuous fun t : ℝ => p.A * sol.α t * bGateZ p.L (sol.μ t) t := by
  have hgate : Continuous fun t : ℝ => bGateZ p.L (sol.μ t) t :=
    bGateZ_comp_continuous sol.cont_μ
  simpa [mul_assoc] using (continuous_const.mul sol.cont_α).mul hgate

theorem selector_replicator_gateZ_integrand_nonneg
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch
      chiReset chiGate kappa gain readoutP)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain) (hA : 0 ≤ p.A)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t := by
  have hα : sol.α t = Real.exp (p.cα * t) := sol.alpha_eq_exp hdom ht
  rw [hα]
  exact mul_nonneg (mul_nonneg hA (Real.exp_pos _).le)
    (bGateZ_pos p.L (sol.μ t) t).le

/-- The concrete z-write start used by the structural `hstart` producer. -/
def selectorMUWriteStartTime (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * (j : ℝ) + Real.pi / 6

/-- The frozen write target time in the selector gate window: `2πj + π/2`. -/
def selectorMUWriteHoldTime (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * (j : ℝ) + Real.pi / 2

theorem selectorMUWriteStartTime_nonneg (j : ℕ) :
    0 ≤ selectorMUWriteStartTime j := by
  unfold selectorMUWriteStartTime
  positivity

theorem selectorMUWriteStart_le_hold (j : ℕ) :
    selectorMUWriteStartTime j ≤ selectorMUWriteHoldTime j := by
  unfold selectorMUWriteStartTime selectorMUWriteHoldTime
  linarith [Real.pi_pos]

theorem selectorMUWriteHold_le_read (j : ℕ) :
    selectorMUWriteHoldTime j ≤ selectorMUWriteReadTime j := by
  unfold selectorMUWriteHoldTime selectorMUWriteReadTime
  linarith [Real.pi_pos]

theorem selectorMUWriteStart_le_read (j : ℕ) :
    selectorMUWriteStartTime j ≤ selectorMUWriteReadTime j := by
  exact le_trans (selectorMUWriteStart_le_hold j) (selectorMUWriteHold_le_read j)

theorem selectorSchedule_domain_of_nonneg_structural :
    ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain := by
  intro t ht
  simpa [selectorSchedule] using ht

theorem selectorMU_hdom_writeStart :
    ∀ (w : ℕ) (j : ℕ), ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      t ∈ selectorSchedule.domain := by
  intro w j t ht
  have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j) ht.1
  exact selectorSchedule_domain_of_nonneg_structural t ht0

theorem selectorMU_hdom_writeHold :
    ∀ (w : ℕ) (j : ℕ), ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      t ∈ selectorSchedule.domain := by
  intro w j t ht
  exact selectorMU_hdom_writeStart w j t
    ⟨ht.1, le_trans ht.2 (selectorMUWriteHold_le_read j)⟩

def selectorMUHStartMult : ℝ :=
  (MachineInstance.stackMachineEncodingU.k : ℝ)

theorem selectorMUHStartMult_eq_B_U :
    selectorMUHStartMult = (MachineInstance.B_U : ℝ) := by
  rfl

theorem selectorMUHStartMult_nonneg : 0 ≤ selectorMUHStartMult := by
  unfold selectorMUHStartMult
  exact Nat.cast_nonneg _

theorem selectorMU_coordMultiplier_le_hstartMult (c : MachineInstance.UConf) (i : Fin d_U) :
    MachineInstance.stackMachineEncodingU.coordMultiplier c i ≤ selectorMUHStartMult := by
  unfold selectorMUHStartMult
  exact MachineInstance.stackMachineEncodingU.coordMultiplier_le_base c i

structure SelectorReplHStartStructuralInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : ℕ → SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (a : ℕ → ℕ → ℝ) (mult : ℝ) where
  hgZ_cont : ∀ w, Continuous fun t : ℝ =>
    bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
  hgZ0 : ∀ w j, ∀ t ∈ Icc (a w j) (selectorMUWriteReadTime j),
    0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
  hdom_write : ∀ w j, ∀ t ∈ Icc (a w j) (selectorMUWriteReadTime j),
    t ∈ selectorSchedule.domain
  hmult0 : 0 ≤ mult
  hmultbound : ∀ w j, ∀ i,
    stackMachineEncodingU.coordMultiplier (M_U.step^[j] (M_U.init w)) i ≤ mult
  hwrite_le : ∀ w j, a w j ≤ selectorMUWriteReadTime j

theorem selector_replicator_hstart_structural_inputs_writeStart
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : ℕ → SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta)) :
    SelectorReplHStartStructuralInputs sol
      (fun _w j => selectorMUWriteStartTime j) selectorMUHStartMult := by
  refine
    { hgZ_cont := ?_
      hgZ0 := ?_
      hdom_write := ?_
      hmult0 := selectorMUHStartMult_nonneg
      hmultbound := ?_
      hwrite_le := ?_ }
  · intro w
    exact selector_replicator_gateZ_integrand_continuous (sol w)
  · intro w j t ht
    have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j) ht.1
    exact selector_replicator_gateZ_integrand_nonneg (sol w)
      selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) ht0
  · exact selectorMU_hdom_writeStart
  · intro w j i
    exact selectorMU_coordMultiplier_le_hstartMult (M_U.step^[j] (M_U.init w)) i
  · intro w j
    exact selectorMUWriteStart_le_read j

theorem solMURepl_hstart_structural_inputs_writeStart
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w g₀))
    (hgateZ : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView Mcy) =
              ((1 + Real.cos t) / 2) ^ Mcy)
    (h_chiGate : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView Mcy) =
              ((1 + Real.sin t) / 2) ^ Mcy)
    (h_kappa : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit selectorInitX0 w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta Mcy κ₀ g₀ HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i))) :
    SelectorReplHStartStructuralInputs
      (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P)
      (fun _w j => selectorMUWriteStartTime j) selectorMUHStartMult :=
  selector_replicator_hstart_structural_inputs_writeStart
    (solMURepl eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0 hfin hgateZ hgateU
      h_chiReset h_chiGate h_kappa h_gain h_P)

#print axioms StackMachineEncoding.stackMultiplier_nonneg
#print axioms StackMachineEncoding.coordMultiplier_nonneg
#print axioms StackMachineEncoding.stackMultiplier_le_base
#print axioms StackMachineEncoding.coordMultiplier_le_base
#print axioms bGateZ_comp_continuous
#print axioms selector_replicator_gateZ_integrand_continuous
#print axioms selector_replicator_gateZ_integrand_nonneg
#print axioms selectorMUWriteStartTime_nonneg
#print axioms selectorMUWriteStart_le_hold
#print axioms selectorMUWriteHold_le_read
#print axioms selectorMUWriteStart_le_read
#print axioms selectorSchedule_domain_of_nonneg_structural
#print axioms selectorMU_hdom_writeStart
#print axioms selectorMU_hdom_writeHold
#print axioms selectorMUHStartMult_eq_B_U
#print axioms selectorMUHStartMult_nonneg
#print axioms selectorMU_coordMultiplier_le_hstartMult
#print axioms selector_replicator_hstart_structural_inputs_writeStart
#print axioms solMURepl_hstart_structural_inputs_writeStart

end Ripple.BoundedUniversality.BGP

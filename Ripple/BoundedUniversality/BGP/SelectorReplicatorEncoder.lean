import Ripple.BoundedUniversality.BGP.SelectorReplicatorAprioriBound

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorEncoder
------------------------------------
Stereographic encoder facts for the selector-replicator initial vector.

The t=0 identities below are the init-only part of the encoder discharge:
once the Euclidean tuple at time 0 is the rational vector
`selectorReplicatorEuclInitQ`, the rational sphere initializer is exactly its
stereographic compactification.

The headline path below uses the constructed `solMUReplRealized` family, whose
ODE existence witness fixes the full Euclidean initial tuple at time zero.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance
open scoped BigOperators Topology
open MvPolynomial

theorem selector_replicator_init_zero_of_initial_values
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    {Pv : V → (Fin d → ℝ) → ℝ}
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (g₀ : ℚ)
    (s : SelectorReplicatorDynSol d B V p sched branch
      chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol s Hval K R)
    (hz0 : ∀ i : Fin d, s.z 0 i = ((x₀ w i : ℚ) : ℝ))
    (hu0 : ∀ i : Fin d, s.u 0 i = ((x₀ w i : ℚ) : ℝ))
    (hlam0 : ∀ v : V, s.lam v 0 = ((1 / (Fintype.card V : ℚ)) : ℝ))
    (hG0 : s.G 0 = 0) :
      ((selectorReplicatorSphereInitQ d V x₀ w g₀ 0 : ℚ) : ℝ) =
        ((∑ i : Fin (selectorDim d V),
            selectorReplicatorTupleTraj s La (g₀ : ℝ) 0 i ^ 2) - 1) /
          ((∑ i : Fin (selectorDim d V),
            selectorReplicatorTupleTraj s La (g₀ : ℝ) 0 i ^ 2) + 1) := by
  have htuple :
      selectorReplicatorTupleTraj s La (g₀ : ℝ) 0 =
        fun i => ((selectorReplicatorEuclInitQ d V x₀ w g₀ i : ℚ) : ℝ) :=
    selectorReplicatorTupleTraj_zero_eq_selectorReplicatorEuclInitQ
      (d := d) (B := B) (V := V) (p := p) (sched := sched) (branch := branch)
      (chiResetF := chiResetF) (chiGateF := chiGateF) (kappaF := kappaF)
      (gainF := gainF) (Pv := Pv) x₀ w g₀ s La s.μ_at_zero s.α_at_zero
      hz0 hu0 hlam0 hG0 La.init_a
  rw [htuple]
  simp [selectorReplicatorSphereInitQ, map_sum, map_pow, map_sub, map_add, map_one, map_div₀]

theorem selector_replicator_init_succ_of_initial_values
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    {Pv : V → (Fin d → ℝ) → ℝ}
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (g₀ : ℚ)
    (s : SelectorReplicatorDynSol d B V p sched branch
      chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol s Hval K R)
    (hz0 : ∀ i : Fin d, s.z 0 i = ((x₀ w i : ℚ) : ℝ))
    (hu0 : ∀ i : Fin d, s.u 0 i = ((x₀ w i : ℚ) : ℝ))
    (hlam0 : ∀ v : V, s.lam v 0 = ((1 / (Fintype.card V : ℚ)) : ℝ))
    (hG0 : s.G 0 = 0) (i : Fin (selectorDim d V)) :
      ((selectorReplicatorSphereInitQ d V x₀ w g₀ i.succ : ℚ) : ℝ) =
        2 * selectorReplicatorTupleTraj s La (g₀ : ℝ) 0 i /
          ((∑ k : Fin (selectorDim d V),
            selectorReplicatorTupleTraj s La (g₀ : ℝ) 0 k ^ 2) + 1) := by
  have htuple :
      selectorReplicatorTupleTraj s La (g₀ : ℝ) 0 =
        fun i => ((selectorReplicatorEuclInitQ d V x₀ w g₀ i : ℚ) : ℝ) :=
    selectorReplicatorTupleTraj_zero_eq_selectorReplicatorEuclInitQ
      (d := d) (B := B) (V := V) (p := p) (sched := sched) (branch := branch)
      (chiResetF := chiResetF) (chiGateF := chiGateF) (kappaF := kappaF)
      (gainF := gainF) (Pv := Pv) x₀ w g₀ s La s.μ_at_zero s.α_at_zero
      hz0 hu0 hlam0 hG0 La.init_a
  rw [htuple]
  simp [selectorReplicatorSphereInitQ, map_sum, map_pow, map_mul, map_add, map_one, map_div₀]

open MachineInstance in
theorem solMUReplRealized_initial_values
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w g₀))
    (w : ℕ) :
      (∀ i : Fin d_U,
        (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w).z 0 i =
          ((selectorInitX0 w i : ℚ) : ℝ)) ∧
      (∀ i : Fin d_U,
        (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w).u 0 i =
          ((selectorInitX0 w i : ℚ) : ℝ)) ∧
      (∀ v : UniversalLocalView,
        (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w).lam v 0 =
          ((1 / (Fintype.card UniversalLocalView : ℚ)) : ℝ)) ∧
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w).G 0 = 0 := by
  classical
  let ex :=
    selector_replicator_sol_exists_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0 w
      (hfin w)
      (selector_replicator_hgateZ_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0 w)
      (selector_replicator_hgateU_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0 w)
      (selector_replicator_h_chiReset_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0 w)
      (selector_replicator_h_chiGate_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0 w)
      (selector_replicator_h_kappa_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0 w)
      (selector_replicator_h_gain_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0 w)
      (selector_replicator_h_P_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0 w)
  have hspec := ex.choose_spec
  have hsol :
      solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w = ex.choose := by
    dsimp [ex]
    unfold solMUReplRealized
    rw [solMURepl_def]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [hsol]
    exact hspec.2.2.1 i
  · intro i
    rw [hsol]
    simpa [selectorReplicatorEuclInitQ, selU, selOfContract, contractU, contractTailU]
      using hspec.2.2.2.1 i
  · intro v
    rw [hsol]
    exact hspec.2.2.2.2.1 v
  · rw [hsol]
    exact hspec.2.2.2.2.2.1

open MachineInstance in
theorem solMUReplRealized_init_zero
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w g₀))
    (w : ℕ)
    (La : SelectorReplicatorHaltLatchSol
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
      (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R) :
      ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ 0 : ℚ) : ℝ) =
        ((∑ i : Fin (selectorDim d_U UniversalLocalView),
            selectorReplicatorTupleTraj
              (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w) La (g₀ : ℝ) 0 i ^ 2) - 1) /
          ((∑ i : Fin (selectorDim d_U UniversalLocalView),
            selectorReplicatorTupleTraj
              (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w) La (g₀ : ℝ) 0 i ^ 2) + 1) := by
  classical
  obtain ⟨hz0, hu0, hlam0, hG0⟩ :=
    solMUReplRealized_initial_values eta heta M κ₀ g₀ HP Kq R hfin w
  exact selector_replicator_init_zero_of_initial_values selectorInitX0 w g₀
    (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w) La
    hz0 hu0 hlam0 hG0

open MachineInstance in
theorem solMUReplRealized_init_succ
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w g₀))
    (w : ℕ)
    (La : SelectorReplicatorHaltLatchSol
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
      (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
    (i : Fin (selectorDim d_U UniversalLocalView)) :
      ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i.succ : ℚ) : ℝ) =
        2 * selectorReplicatorTupleTraj
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w) La (g₀ : ℝ) 0 i /
          ((∑ k : Fin (selectorDim d_U UniversalLocalView),
            selectorReplicatorTupleTraj
              (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w) La (g₀ : ℝ) 0 k ^ 2) + 1) := by
  classical
  obtain ⟨hz0, hu0, hlam0, hG0⟩ :=
    solMUReplRealized_initial_values eta heta M κ₀ g₀ HP Kq R hfin w
  exact selector_replicator_init_succ_of_initial_values selectorInitX0 w g₀
    (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w) La
    hz0 hu0 hlam0 hG0 i

open MachineInstance in
theorem bgp_MU_replicator_settled_realized_hfin_init_discharged_halt
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (boxInputs : MUReplicatorBoxInputs eta heta M κ₀ g₀
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
        (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
          selectorInitX0 w hκ0 hg0 hKq0)))
    (settled : MUReplicatorSettledHaltFacts
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
        (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
          selectorInitX0 w hκ0 hg0 hKq0))) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) := by
  let hfin := fun w =>
    selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
      selectorInitX0 w hκ0 hg0 hKq0
  exact bgp_MU_replicator_settled_realized_hfin_halt eta heta M κ₀ g₀ HP Kq R
    hκ0 hg0 hKq0 init_presented
    (fun w La => solMUReplRealized_init_zero eta heta M κ₀ g₀ HP Kq R hfin w La)
    (fun w La i => solMUReplRealized_init_succ eta heta M κ₀ g₀ HP Kq R hfin w La i)
    boxInputs settled

open MachineInstance in
theorem bgp_MU_replicator_settled_realized_hfin_init_discharged_late_start
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (boxInputs : MUReplicatorBoxInputs eta heta M κ₀ g₀
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
        (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
          selectorInitX0 w hκ0 hg0 hKq0)))
    (late : MUReplicatorLateStartHaltFacts
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
        (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
          selectorInitX0 w hκ0 hg0 hKq0))) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) := by
  let hfin := fun w =>
    selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
      selectorInitX0 w hκ0 hg0 hKq0
  exact bgp_MU_replicator_settled_realized_hfin_late_start eta heta M κ₀ g₀ HP Kq R
    hκ0 hg0 hKq0 init_presented
    (fun w La => solMUReplRealized_init_zero eta heta M κ₀ g₀ HP Kq R hfin w La)
    (fun w La i => solMUReplRealized_init_succ eta heta M κ₀ g₀ HP Kq R hfin w La i)
    boxInputs late

open MachineInstance in
theorem bgp_MU_replicator_settled_realized_hfin_init_discharged
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (boxInputs : MUReplicatorBoxInputs eta heta M κ₀ g₀
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
        (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
          selectorInitX0 w hκ0 hg0 hKq0)))
    (settled : MUReplicatorSettledFacts
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
        (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
          selectorInitX0 w hκ0 hg0 hKq0))) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_discharged_halt
    eta heta M κ₀ g₀ HP Kq R hκ0 hg0 hKq0 init_presented boxInputs
    settled.toHaltFacts

#print axioms selector_replicator_init_zero_of_initial_values
#print axioms selector_replicator_init_succ_of_initial_values
#print axioms solMUReplRealized_initial_values
#print axioms solMUReplRealized_init_zero
#print axioms solMUReplRealized_init_succ
#print axioms bgp_MU_replicator_settled_realized_hfin_init_discharged_halt
#print axioms bgp_MU_replicator_settled_realized_hfin_init_discharged_late_start
#print axioms bgp_MU_replicator_settled_realized_hfin_init_discharged

end Ripple.BoundedUniversality.BGP

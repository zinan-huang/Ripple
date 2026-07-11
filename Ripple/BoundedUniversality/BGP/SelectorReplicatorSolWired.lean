import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledFinal
import Ripple.BoundedUniversality.BGP.BGPParams38

set_option maxHeartbeats 800000

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance
open scoped BigOperators
open MvPolynomial

variable {d B : ℕ} {V : Type} [Fintype V]
  (branch : V → BranchData d B)
  (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
  (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
  (HP : MvPolynomial (Fin d) ℚ)
  (Aq Kq cμq cαq : ℚ) (L R : ℕ)
  (y : Fin (selectorDim d V) → ℝ)

theorem replAprioriField_mu_eq :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractMu d)) = (cμq : ℝ) := by
  unfold selectorReplicatorAssembledVectorField
  rw [show selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
        PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractMu d)) = C cμq from by
    simp [selectorReplicatorAssembledField, selOfContract, contractMu, contractS]]
  simp

theorem replAprioriField_alpha_eq :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractAlpha d)) =
      (cαq : ℝ) * y (selOfContract V (contractAlpha d)) := by
  unfold selectorReplicatorAssembledVectorField
  rw [show selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
        PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractAlpha d)) =
        C cαq * X (selOfContract V (contractAlpha d)) from by
    simp [selectorReplicatorAssembledField, selOfContract, contractAlpha, contractS]]
  simp

theorem replAprioriField_s_eq :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractS d)) = y (selOfContract V (contractC d)) := by
  unfold selectorReplicatorAssembledVectorField
  rw [show selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
        PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractS d)) =
        X (selOfContract V (contractC d)) from by
    simp [selectorReplicatorAssembledField, selOfContract, contractS]]
  simp

theorem replAprioriField_c_eq :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractC d)) = -y (selOfContract V (contractS d)) := by
  unfold selectorReplicatorAssembledVectorField
  rw [show selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
        PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractC d)) =
        -X (selOfContract V (contractS d)) from by
    simp [selectorReplicatorAssembledField, selOfContract, contractC, contractS]]
  simp

theorem replAprioriField_gateZ_eq :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractGateZ d)) =
      -((cμq : ℝ) * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selRP d V L)
        + y (selOfContract V (contractMu d))
          * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selRPderiv d V L))
        * y (selOfContract V (contractGateZ d)) := by
  unfold selectorReplicatorAssembledVectorField
  rw [show selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
        PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractGateZ d)) =
        -((C cμq * selRP d V L
          + X (selOfContract V (contractMu d)) * selRPderiv d V L) *
          X (selOfContract V (contractGateZ d))) from by
    simp [selectorReplicatorAssembledField, selOfContract, contractGateZ]]
  simp only [eval₂_neg, eval₂_mul, eval₂_add, eval₂_C, eval₂_X, eq_ratCast]
  ring

theorem replAprioriField_gateU_eq :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractGateU d)) =
      -((cμq : ℝ) * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selQP d V L)
        + y (selOfContract V (contractMu d))
          * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selQPderiv d V L))
        * y (selOfContract V (contractGateU d)) := by
  unfold selectorReplicatorAssembledVectorField
  rw [show selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
        PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractGateU d)) =
        -((C cμq * selQP d V L
          + X (selOfContract V (contractMu d)) * selQPderiv d V L) *
          X (selOfContract V (contractGateU d))) from by
    simp [selectorReplicatorAssembledField, selOfContract, contractGateU]]
  simp only [eval₂_neg, eval₂_mul, eval₂_add, eval₂_C, eval₂_X, eq_ratCast]
  ring

theorem replAprioriField_warmGain_eq :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selWarmGainCoord d V) = 0 := by
  unfold selectorReplicatorAssembledVectorField
  rw [show selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
        PpolyP HP Aq Kq cμq cαq L R (selWarmGainCoord d V) = 0 from by
    simp [selectorReplicatorAssembledField, selWarmGainCoord, Fin.append, Fin.addCases]]
  simp

theorem repl_mu_coord_affine
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T,
      yt t (selOfContract V (contractMu d))
        = yt 0 (selOfContract V (contractMu d)) + (cμq : ℝ) * t := by
  have h := affine_of_const_deriv (T := T) (c := (cμq : ℝ))
    (fun s => yt s (selOfContract V (contractMu d))) ?_
  · exact h
  · intro t ht
    have hpi := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractMu d))
    rw [replAprioriField_mu_eq] at hpi
    exact hpi

theorem repl_alpha_coord_eq
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T,
      yt t (selOfContract V (contractAlpha d))
        = yt 0 (selOfContract V (contractAlpha d)) * Real.exp ((cαq : ℝ) * t) := by
  have h := scalar_linear_ode_eq (T := T) (c := (cαq : ℝ))
    (fun s => yt s (selOfContract V (contractAlpha d))) ?_
  · exact h
  · intro t ht
    have hpi := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractAlpha d))
    rw [replAprioriField_alpha_eq] at hpi
    exact hpi

theorem repl_warmGain_coord_eq
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T,
      yt t (selWarmGainCoord d V) = yt 0 (selWarmGainCoord d V) := by
  intro t ht
  have h0T : (0 : ℝ) ≤ t := ht.1
  have hdiff : DifferentiableOn ℝ (fun s => yt s (selWarmGainCoord d V)) (Set.Icc 0 t) := by
    intro x hx
    have hxIco : x ∈ Ico (0 : ℝ) T := ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩
    exact ((hasDerivAt_pi.mp (hderiv x hxIco)) (selWarmGainCoord d V)).differentiableAt.differentiableWithinAt
  have hderivW : ∀ x ∈ Set.Ico (0 : ℝ) t,
      derivWithin (fun s => yt s (selWarmGainCoord d V)) (Set.Icc 0 t) x = 0 := by
    intro x hx
    have hxIco : x ∈ Ico (0 : ℝ) T := ⟨hx.1, lt_trans hx.2 ht.2⟩
    have huniq : UniqueDiffWithinAt ℝ (Set.Icc 0 t) x :=
      (uniqueDiffOn_Icc (lt_of_le_of_lt hx.1 hx.2)) x (Set.Ico_subset_Icc_self hx)
    have hpi := (hasDerivAt_pi.mp (hderiv x hxIco)) (selWarmGainCoord d V)
    rw [replAprioriField_warmGain_eq] at hpi
    exact hpi.hasDerivWithinAt.derivWithin huniq
  exact constant_of_derivWithin_zero hdiff hderivW t (Set.right_mem_Icc.mpr h0T)

theorem repl_sc_realize
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hs0 : yt 0 (selOfContract V (contractS d)) = 0)
    (hc0 : yt 0 (selOfContract V (contractC d)) = 1) :
    ∀ t ∈ Ico (0 : ℝ) T,
      yt t (selOfContract V (contractS d)) = Real.sin t
        ∧ yt t (selOfContract V (contractC d)) = Real.cos t := by
  have hE : ∀ t ∈ Ico (0 : ℝ) T,
      (yt t (selOfContract V (contractS d)) - Real.sin t) ^ 2
        + (yt t (selOfContract V (contractC d)) - Real.cos t) ^ 2 = 0 := by
    have key := affine_of_const_deriv (T := T) (c := (0 : ℝ))
      (fun r => (yt r (selOfContract V (contractS d)) - Real.sin r) ^ 2
        + (yt r (selOfContract V (contractC d)) - Real.cos r) ^ 2) ?_
    · intro t ht
      have h := key t ht
      simp only [mul_zero, add_zero] at h
      rw [h, hs0, hc0]
      norm_num
    · intro t ht
      have hsd := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractS d))
      have hcd := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractC d))
      rw [replAprioriField_s_eq] at hsd
      rw [replAprioriField_c_eq] at hcd
      have e1 : HasDerivAt (fun r => (yt r (selOfContract V (contractS d)) - Real.sin r) ^ 2)
          (2 * (yt t (selOfContract V (contractS d)) - Real.sin t)
            * (yt t (selOfContract V (contractC d)) - Real.cos t)) t := by
        simpa using (hsd.sub (Real.hasDerivAt_sin t)).pow 2
      have e2 : HasDerivAt (fun r => (yt r (selOfContract V (contractC d)) - Real.cos r) ^ 2)
          (2 * (yt t (selOfContract V (contractC d)) - Real.cos t)
            * (-(yt t (selOfContract V (contractS d))) + Real.sin t)) t := by
        simpa using (hcd.sub (Real.hasDerivAt_cos t)).pow 2
      have hsum0 := e1.add e2
      have hval : 2 * (yt t (selOfContract V (contractS d)) - Real.sin t)
            * (yt t (selOfContract V (contractC d)) - Real.cos t)
          + 2 * (yt t (selOfContract V (contractC d)) - Real.cos t)
            * (-(yt t (selOfContract V (contractS d))) + Real.sin t) = 0 := by
        ring
      rw [hval] at hsum0
      exact hsum0
  intro t ht
  have h := hE t ht
  have hs2 : (yt t (selOfContract V (contractS d)) - Real.sin t) ^ 2 = 0 := by
    nlinarith [sq_nonneg (yt t (selOfContract V (contractS d)) - Real.sin t),
      sq_nonneg (yt t (selOfContract V (contractC d)) - Real.cos t)]
  have hc2 : (yt t (selOfContract V (contractC d)) - Real.cos t) ^ 2 = 0 := by
    nlinarith [sq_nonneg (yt t (selOfContract V (contractS d)) - Real.sin t),
      sq_nonneg (yt t (selOfContract V (contractC d)) - Real.cos t)]
  refine ⟨?_, ?_⟩
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs2
    linarith
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc2
    linarith

theorem repl_chiReset_eval_yt
    (M : ℕ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        (yt t)) t)
    (hs0 : yt 0 (selOfContract V (contractS d)) = 0)
    (hc0 : yt 0 (selOfContract V (contractC d)) = 1) :
    ∀ t ∈ Ico (0 : ℝ) T,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
          (selChiResetPoly d V M) =
        ((1 + Real.cos t) / 2) ^ M := by
  intro t ht
  have hsc := repl_sc_realize branch chiResetP chiGateP kappaP gainP PpolyP HP
    Aq Kq cμq cαq L R yt hderiv hs0 hc0 t ht
  simp only [selChiResetPoly, eval₂_pow, eval₂_mul, eval₂_add,
    eval₂_C, eval₂_X, eval₂_one, map_div₀, map_one, map_ofNat]
  rw [hsc.2]
  ring_nf

theorem repl_chiGate_eval_yt
    (M : ℕ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        (yt t)) t)
    (hs0 : yt 0 (selOfContract V (contractS d)) = 0)
    (hc0 : yt 0 (selOfContract V (contractC d)) = 1) :
    ∀ t ∈ Ico (0 : ℝ) T,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
          (selChiGatePoly d V M) =
        ((1 + Real.sin t) / 2) ^ M := by
  intro t ht
  have hsc := repl_sc_realize branch chiResetP chiGateP kappaP gainP PpolyP HP
    Aq Kq cμq cαq L R yt hderiv hs0 hc0 t ht
  simp only [selChiGatePoly, eval₂_pow, eval₂_mul, eval₂_add,
    eval₂_C, eval₂_X, eval₂_one, map_div₀, map_one, map_ofNat]
  rw [hsc.1]
  ring_nf

theorem repl_gate_exp_unique {n : ℕ}
    (y : ℝ → Fin n → ℝ) (gate μ : Fin n) (cμ : ℝ) (pulse pulseDeriv : ℝ → ℝ)
    (hgate0 : y 0 gate = 1) (hμ0 : y 0 μ = 0)
    (hgate : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun τ => y τ gate)
        (-(cμ * pulse s + y s μ * pulseDeriv s) * y s gate) s)
    (hμ : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun τ => y τ μ) cμ s)
    (hpulse : ∀ s : ℝ, HasDerivAt pulse (pulseDeriv s) s) :
    ∀ t : ℝ, 0 ≤ t →
      y t gate = Real.exp (-(y t μ * pulse t)) := by
  intro t ht
  let G : ℝ → ℝ := fun s => y s gate * Real.exp (y s μ * pulse s)
  have hGconst := affine_of_const_deriv (T := t + 1) (c := (0 : ℝ)) G ?_
    t ⟨ht, by linarith⟩
  have hG0 : G 0 = 1 := by
    simp [G, hgate0, hμ0]
  have hGt : G t = 1 := by
    simpa [hG0] using hGconst
  have hEne : Real.exp (y t μ * pulse t) ≠ 0 := (Real.exp_pos _).ne'
  have hmul :
      y t gate * Real.exp (y t μ * pulse t) =
        Real.exp (-(y t μ * pulse t)) * Real.exp (y t μ * pulse t) := by
    calc
      y t gate * Real.exp (y t μ * pulse t) = 1 := by simpa [G] using hGt
      _ = Real.exp (-(y t μ * pulse t)) * Real.exp (y t μ * pulse t) := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    y t gate = (y t gate * Real.exp (y t μ * pulse t)) /
        Real.exp (y t μ * pulse t) := by field_simp [hEne]
    _ = (Real.exp (-(y t μ * pulse t)) * Real.exp (y t μ * pulse t)) /
        Real.exp (y t μ * pulse t) := by rw [hmul]
    _ = Real.exp (-(y t μ * pulse t)) := by field_simp [hEne]
  · intro s hs
    have hg := hgate s hs.1
    have hprod := (hμ s hs.1).mul (hpulse s)
    have hexp := hprod.exp
    have hG := hg.mul hexp
    convert hG using 1 <;> ring

open MachineInstance in
theorem selector_replicator_gateZ_realize
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ)
    (y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ)
    (hy0 : y 0 = selectorMUReplicatorInit x₀ w g₀)
    (hyode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) :
    ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
        bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t := by
  let gate := selOfContract UniversalLocalView (contractGateZ d_U)
  let μ := selOfContract UniversalLocalView (contractMu d_U)
  have hgate0 : y 0 gate = 1 := by
    rw [hy0]
    simp [gate, selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract,
      contractGateZ]
  have hμ0 : y 0 μ = 0 := by
    rw [hy0]
    simp [μ, selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract,
      contractMu]
  have hμder : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun τ => y τ μ) (1000 : ℝ) s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) μ
    simp only [selectorMUReplicatorField] at hpi
    rw [replAprioriField_mu_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := (300 : ℚ))
      (L := 1) (R := R)] at hpi
    simpa [μ] using hpi
  have hpulse : ∀ s : ℝ, HasDerivAt (rPulse 1) (-(Real.cos s / 2)) s := by
    intro s
    unfold rPulse
    have hb : HasDerivAt (fun τ : ℝ => (1 - Real.sin τ) / 2)
        (-(Real.cos s / 2)) s := by
      convert ((hasDerivAt_const (x := s) (c := (1 : ℝ))).sub
        (Real.hasDerivAt_sin s)).div_const 2 using 1 <;> ring
    simpa using hb.pow 1
  have hgateDer : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun τ => y τ gate)
        (-((1000 : ℝ) * rPulse 1 s + y s μ * (-(Real.cos s / 2))) *
          y s gate) s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) gate
    simp only [selectorMUReplicatorField] at hpi
    rw [replAprioriField_gateZ_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := (300 : ℚ))
      (L := 1) (R := R)] at hpi
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractC]
    have hsc := repl_sc_realize (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := (300 : ℚ))
      (L := 1) (R := R) (yt := y) (T := s + 1)
      (fun r hr => hyode r hr.1) hs0 hc0 s ⟨hs, by linarith⟩
    have hrp : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selRP d_U UniversalLocalView 1) = rPulse 1 s := by
      simp [selRP, rPulse, hsc.1]
      ring
    have hrpd : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selRPderiv d_U UniversalLocalView 1) = -(Real.cos s / 2) := by
      simp [selRPderiv, hsc.1, hsc.2]
      ring
    rw [hrp, hrpd] at hpi
    convert hpi using 1 <;> simp [gate, μ] <;> ring
  intro t ht
  simpa [gate, μ, bGateZ] using
    repl_gate_exp_unique y gate μ (1000 : ℝ) (rPulse 1) (fun s => -(Real.cos s / 2))
      hgate0 hμ0 hgateDer hμder hpulse t ht

open MachineInstance in
theorem selector_replicator_gateU_realize
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ)
    (y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ)
    (hy0 : y 0 = selectorMUReplicatorInit x₀ w g₀)
    (hyode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) :
    ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract UniversalLocalView (contractGateU d_U)) =
        bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t := by
  let gate := selOfContract UniversalLocalView (contractGateU d_U)
  let μ := selOfContract UniversalLocalView (contractMu d_U)
  have hgate0 : y 0 gate = 1 := by
    rw [hy0]
    simp [gate, selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract,
      contractGateU]
  have hμ0 : y 0 μ = 0 := by
    rw [hy0]
    simp [μ, selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract,
      contractMu]
  have hμder : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun τ => y τ μ) (1000 : ℝ) s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) μ
    simp only [selectorMUReplicatorField] at hpi
    rw [replAprioriField_mu_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := (300 : ℚ))
      (L := 1) (R := R)] at hpi
    simpa [μ] using hpi
  have hpulse : ∀ s : ℝ, HasDerivAt (qPulse 1) (Real.cos s / 2) s := by
    intro s
    unfold qPulse
    have hb : HasDerivAt (fun τ : ℝ => (1 + Real.sin τ) / 2)
        (Real.cos s / 2) s := by
      convert ((hasDerivAt_const (x := s) (c := (1 : ℝ))).add
        (Real.hasDerivAt_sin s)).div_const 2 using 1 <;> ring
    simpa using hb.pow 1
  have hgateDer : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun τ => y τ gate)
        (-((1000 : ℝ) * qPulse 1 s + y s μ * (Real.cos s / 2)) *
          y s gate) s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) gate
    simp only [selectorMUReplicatorField] at hpi
    rw [replAprioriField_gateU_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := (300 : ℚ))
      (L := 1) (R := R)] at hpi
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractC]
    have hsc := repl_sc_realize (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := (300 : ℚ))
      (L := 1) (R := R) (yt := y) (T := s + 1)
      (fun r hr => hyode r hr.1) hs0 hc0 s ⟨hs, by linarith⟩
    have hqp : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selQP d_U UniversalLocalView 1) = qPulse 1 s := by
      simp [selQP, qPulse, hsc.1]
      ring
    have hqpd : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selQPderiv d_U UniversalLocalView 1) = Real.cos s / 2 := by
      simp [selQPderiv, hsc.1, hsc.2]
      ring
    rw [hqp, hqpd] at hpi
    convert hpi using 1 <;> simp [gate, μ] <;> ring
  intro t ht
  simpa [gate, μ, bGateU] using
    repl_gate_exp_unique y gate μ (1000 : ℝ) (qPulse 1) (fun s => Real.cos s / 2)
      hgate0 hμ0 hgateDer hμder hpulse t ht

open MachineInstance in
theorem selector_replicator_sol_exists_MU_realized
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ)
    (hfin :
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit x₀ w g₀)) :
    ∃ sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
        branchU
        (fun t => ((1 + Real.cos t) / 2) ^ M)
        (fun t => ((1 + Real.sin t) / 2) ^ M)
        (fun _ => (κ₀ : ℝ))
        (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
        (universalPval eta heta),
      sol.z 0 = sol.init_z ∧ sol.u 0 = sol.init_u ∧
        (∀ i,
          sol.u 0 i =
            ((selectorReplicatorEuclInitQ d_U UniversalLocalView x₀ w g₀
              (selU UniversalLocalView i) : ℚ) : ℝ)) ∧
        sol.ZUFiniteCoordBound := by
  have hgz :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t := by
    intro y hy0 hyode
    exact selector_replicator_gateZ_realize eta heta M κ₀ g₀ HP Kq R x₀ w y hy0 hyode
  have hgu :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t := by
    intro y hy0 hyode
    exact selector_replicator_gateU_realize eta heta M κ₀ g₀ HP Kq R x₀ w y hy0 hyode
  have hcr :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M := by
    intro y hy0 hyode t ht
    have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractC]
    exact repl_chiReset_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := (300 : ℚ)) (L := 1) (R := R) (M := M)
      (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) hs0 hc0 t htIco
  have hcg :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M := by
    intro y hy0 hyode t ht
    have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractC]
    exact repl_chiGate_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := (300 : ℚ)) (L := 1) (R := R) (M := M)
      (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) hs0 hc0 t htIco
  have hk :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ) := by
    intro y _hy0 _hyode t _ht
    exact kappa_eval_yt (d := d_U) (V := UniversalLocalView) κ₀ y t
  have hgn :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              (g₀ : ℝ) * Real.exp (bgpParams38.cα * t) := by
    intro y hy0 hyode t ht
    have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hα0 : y 0 (selOfContract UniversalLocalView (contractAlpha d_U)) = 1 := by
      rw [hy0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract,
        contractAlpha]
    rw [gain_eval_yt (d := d_U) (V := UniversalLocalView) y t]
    rw [repl_alpha_coord_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := (300 : ℚ)) (L := 1) (R := R)
      (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) t htIco]
    rw [hα0]
    have hwg : y t (selWarmGainCoord d_U UniversalLocalView) = ↑g₀ := by
      have hconst := repl_warmGain_coord_eq (branch := branchU)
        (chiResetP := selChiResetPoly d_U UniversalLocalView M)
        (chiGateP := selChiGatePoly d_U UniversalLocalView M)
        (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
        (gainP := selGainPoly d_U UniversalLocalView)
        (PpolyP := muReadoutPoly eta heta) (HP := HP)
        (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
        (cαq := (300 : ℚ)) (L := 1) (R := R)
        (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) t htIco
      rw [hconst, hy0]
      simp only [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selWarmGainCoord,
        Fin.append_right]
    rw [hwg]
    norm_num [bgpParams38]
  have hp :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)) := by
    intro y _hy0 _hyode v t _ht
    exact muReadoutPoly_eval_yt eta heta v y t
  obtain ⟨sol, hz0, hu0, _hzx, hue, _hlam, _hG, hbox⟩ :=
    selector_replicator_sol_exists_MU eta heta M κ₀ g₀ HP Kq R x₀ w hfin
      hgz hgu hcr hcg hk hgn hp
  exact ⟨sol, hz0, hu0, hue, hbox⟩

open MachineInstance in
theorem selector_replicator_hgateZ_MU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) :
    ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t :=
  fun w y hy0 hyode =>
    selector_replicator_gateZ_realize eta heta M κ₀ g₀ HP Kq R x₀ w y hy0 hyode

open MachineInstance in
theorem selector_replicator_hgateU_MU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) :
    ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t :=
  fun w y hy0 hyode =>
    selector_replicator_gateU_realize eta heta M κ₀ g₀ HP Kq R x₀ w y hy0 hyode

open MachineInstance in
theorem selector_replicator_h_chiReset_MU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) :
    ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M := by
  intro w y hy0 hyode t ht
  have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
    rw [hy0]
    simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractS]
  have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
    rw [hy0]
    simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractC]
  exact repl_chiReset_eval_yt (branch := branchU)
    (chiResetP := selChiResetPoly d_U UniversalLocalView M)
    (chiGateP := selChiGatePoly d_U UniversalLocalView M)
    (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
    (gainP := selGainPoly d_U UniversalLocalView)
    (PpolyP := muReadoutPoly eta heta) (HP := HP)
    (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
    (cαq := (300 : ℚ)) (L := 1) (R := R) (M := M)
    (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) hs0 hc0 t htIco

open MachineInstance in
theorem selector_replicator_h_chiGate_MU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) :
    ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M := by
  intro w y hy0 hyode t ht
  have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
    rw [hy0]
    simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractS]
  have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
    rw [hy0]
    simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractC]
  exact repl_chiGate_eval_yt (branch := branchU)
    (chiResetP := selChiResetPoly d_U UniversalLocalView M)
    (chiGateP := selChiGatePoly d_U UniversalLocalView M)
    (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
    (gainP := selGainPoly d_U UniversalLocalView)
    (PpolyP := muReadoutPoly eta heta) (HP := HP)
    (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
    (cαq := (300 : ℚ)) (L := 1) (R := R) (M := M)
    (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) hs0 hc0 t htIco

open MachineInstance in
theorem selector_replicator_h_kappa_MU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) :
    ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ) := by
  intro _w y _hy0 _hyode t _ht
  exact kappa_eval_yt (d := d_U) (V := UniversalLocalView) κ₀ y t

open MachineInstance in
theorem selector_replicator_h_gain_MU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) :
    ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              (g₀ : ℝ) * Real.exp (bgpParams38.cα * t) := by
  intro _w y hy0 hyode t ht
  have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have hα0 : y 0 (selOfContract UniversalLocalView (contractAlpha d_U)) = 1 := by
    rw [hy0]
    simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractAlpha]
  rw [gain_eval_yt (d := d_U) (V := UniversalLocalView) y t]
  rw [repl_alpha_coord_eq (branch := branchU)
    (chiResetP := selChiResetPoly d_U UniversalLocalView M)
    (chiGateP := selChiGatePoly d_U UniversalLocalView M)
    (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
    (gainP := selGainPoly d_U UniversalLocalView)
    (PpolyP := muReadoutPoly eta heta) (HP := HP)
    (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
    (cαq := (300 : ℚ)) (L := 1) (R := R)
    (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) t htIco]
  rw [hα0]
  have hwg : y t (selWarmGainCoord d_U UniversalLocalView) = ↑g₀ := by
    have hconst := repl_warmGain_coord_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := (300 : ℚ)) (L := 1) (R := R)
      (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) t htIco
    rw [hconst, hy0]
    simp only [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selWarmGainCoord,
      Fin.append_right]
  rw [hwg]
  norm_num [bgpParams38]

open MachineInstance in
theorem selector_replicator_h_P_MU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) :
    ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)) := by
  intro _w y _hy0 _hyode v t _ht
  exact muReadoutPoly_eval_yt eta heta v y t

open MachineInstance in
noncomputable def solMUReplRealized
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit x₀ w g₀)) :
    ℕ → SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
        branchU
        (fun t => ((1 + Real.cos t) / 2) ^ M)
        (fun t => ((1 + Real.sin t) / 2) ^ M)
        (fun _ => (κ₀ : ℝ))
        (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
        (universalPval eta heta) :=
  solMURepl eta heta M κ₀ g₀ HP Kq R x₀ hfin
    (selector_replicator_hgateZ_MU eta heta M κ₀ g₀ HP Kq R x₀)
    (selector_replicator_hgateU_MU eta heta M κ₀ g₀ HP Kq R x₀)
    (selector_replicator_h_chiReset_MU eta heta M κ₀ g₀ HP Kq R x₀)
    (selector_replicator_h_chiGate_MU eta heta M κ₀ g₀ HP Kq R x₀)
    (selector_replicator_h_kappa_MU eta heta M κ₀ g₀ HP Kq R x₀)
    (selector_replicator_h_gain_MU eta heta M κ₀ g₀ HP Kq R x₀)
    (selector_replicator_h_P_MU eta heta M κ₀ g₀ HP Kq R x₀)

open MachineInstance in
theorem bgp_MU_replicator_settled_realized_halt
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w g₀))
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
                  La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
                  La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj
              (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
              La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
                  La (g₀ : ℝ) 0 k ^ 2) + 1))
    (boxInputs : MUReplicatorBoxInputs eta heta M κ₀ g₀
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin))
    (settled : MUReplicatorSettledHaltFacts
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) := by
  unfold solMUReplRealized at boxInputs settled
  exact bgp_MU_replicator_settled eta heta M κ₀ g₀ HP Kq R hfin
    (selector_replicator_hgateZ_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_hgateU_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_h_chiReset_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_h_chiGate_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_h_kappa_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_h_gain_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_h_P_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    init_presented
    (fun w La => by simpa [solMUReplRealized] using init_zero w La)
    (fun w La i => by simpa [solMUReplRealized] using init_succ w La i)
    boxInputs settled

open MachineInstance in
theorem bgp_MU_replicator_settled_realized_late_start
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w g₀))
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
                  La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
                  La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj
              (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
              La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
                  La (g₀ : ℝ) 0 k ^ 2) + 1))
    (boxInputs : MUReplicatorBoxInputs eta heta M κ₀ g₀
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin))
    (late : MUReplicatorLateStartHaltFacts
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) := by
  unfold solMUReplRealized at boxInputs late
  exact bgp_MU_replicator_settled_late_start eta heta M κ₀ g₀ HP Kq R hfin
    (selector_replicator_hgateZ_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_hgateU_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_h_chiReset_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_h_chiGate_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_h_kappa_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_h_gain_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    (selector_replicator_h_P_MU eta heta M κ₀ g₀ HP Kq R selectorInitX0)
    init_presented
    (fun w La => by simpa [solMUReplRealized] using init_zero w La)
    (fun w La i => by simpa [solMUReplRealized] using init_succ w La i)
    boxInputs late

open MachineInstance in
theorem bgp_MU_replicator_settled_realized
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit selectorInitX0 w g₀))
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
                  La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
                  La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj
              (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
              La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin w)
                  La (g₀ : ℝ) 0 k ^ 2) + 1))
    (boxInputs : MUReplicatorBoxInputs eta heta M κ₀ g₀
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin))
    (settled : MUReplicatorSettledFacts
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0 hfin)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_halt eta heta M κ₀ g₀ HP Kq R hfin
    init_presented init_zero init_succ boxInputs settled.toHaltFacts

attribute [irreducible] solMUReplRealized

#print axioms replAprioriField_mu_eq
#print axioms replAprioriField_alpha_eq
#print axioms replAprioriField_s_eq
#print axioms replAprioriField_c_eq
#print axioms replAprioriField_gateZ_eq
#print axioms replAprioriField_gateU_eq
#print axioms repl_mu_coord_affine
#print axioms repl_alpha_coord_eq
#print axioms repl_sc_realize
#print axioms repl_chiReset_eval_yt
#print axioms repl_chiGate_eval_yt
#print axioms repl_gate_exp_unique
#print axioms selector_replicator_gateZ_realize
#print axioms selector_replicator_gateU_realize
#print axioms selector_replicator_sol_exists_MU_realized
#print axioms selector_replicator_hgateZ_MU
#print axioms selector_replicator_hgateU_MU
#print axioms selector_replicator_h_chiReset_MU
#print axioms selector_replicator_h_chiGate_MU
#print axioms selector_replicator_h_kappa_MU
#print axioms selector_replicator_h_gain_MU
#print axioms selector_replicator_h_P_MU
#print axioms solMUReplRealized
#print axioms bgp_MU_replicator_settled_realized_halt
#print axioms bgp_MU_replicator_settled_realized_late_start
#print axioms bgp_MU_replicator_settled_realized

end Ripple.BoundedUniversality.BGP

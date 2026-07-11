import Ripple.BoundedUniversality.BGP.SelectorAprioriBound
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorAprioriBound38
----------------------------------
`bgpParams38` specialization of the MU selector existence wrapper.

The original `selector_sol_exists_MU_clean` uses `bgpParams` with `cα = 1/4`.
This file keeps the old theorem untouched and reuses the generic
`selector_sol_exists` path with `cμ = 1000` and `cα = 300`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MvPolynomial Set
open MachineInstance

/-- MU selector assembled vector field with fixed `cμ = 1000` and configurable `cα`. -/
noncomputable abbrev selectorMUFieldWithCAlpha
    (cαq : ℚ) (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ) :=
  selectorAssembledVectorField d_U B_U UniversalLocalView branchU
    (selChiResetPoly d_U UniversalLocalView M)
    (selChiGatePoly d_U UniversalLocalView M)
    (selKappaPoly d_U UniversalLocalView κ₀)
    (selGainPoly d_U UniversalLocalView)
    (muReadoutPoly eta heta) HP
    (1 : ℚ) Kq (1000 : ℚ) cαq 1 R

/-- MU selector field specialized to `cα = 300`. -/
noncomputable abbrev selectorMUField38
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ) :=
  selectorMUFieldWithCAlpha (300 : ℚ) eta heta M κ₀ g₀ HP Kq R

theorem selector_finiteHorizonBound_MU_withCAlpha
    (cαq : ℚ) (hcα0 : 0 ≤ (cαq : ℝ))
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco
          (selectorMUFieldWithCAlpha cαq eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco
          (selectorMUFieldWithCAlpha cαq eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ UniversalLocalView HP)| ≤ Rbd) :
    Ripple.FiniteHorizonBound
      (selectorMUFieldWithCAlpha cαq eta heta M κ₀ g₀ HP Kq R)
      (selectorMUInit x₀ w g₀) := by
  classical
  let Gbd : ℝ → ℝ := fun T => (g₀ : ℝ) * Real.exp ((cαq : ℝ) * T)
  let Abd : ℝ → ℝ :=
    fun _ => max |selectorMUInit x₀ w g₀
      (selOfContract UniversalLocalView (contractA d_U))| Rbd
  have hGbdmono : Monotone Gbd := by
    intro S T hST
    dsimp [Gbd]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hST hcα0))
      hg0
  have hAbdmono : Monotone Abd := by
    intro S T hST
    dsimp [Abd]
    exact le_rfl
  have hGbd0 : ∀ T : ℝ, 0 ≤ Gbd T := by
    intro T
    exact mul_nonneg hg0 (le_of_lt (Real.exp_pos _))
  have hAbd0 : ∀ T : ℝ, 0 ≤ Abd T := by
    intro T
    dsimp [Abd]
    exact le_trans (abs_nonneg _)
      (le_max_left _ _)
  refine selector_finiteHorizonBound_v2
    (branch := branchU)
    (chiResetP := selChiResetPoly d_U UniversalLocalView M)
    (chiGateP := selChiGatePoly d_U UniversalLocalView M)
    (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
    (gainP := selGainPoly d_U UniversalLocalView)
    (PpolyP := muReadoutPoly eta heta) (HP := HP)
    (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
    (cαq := cαq) (L := 1) (R := R)
    (x₀ := x₀) (w := w) (warmGainInit := g₀) (Gbd := Gbd) (Abd := Abd)
    (hBpos := by norm_num [B_U])
    hGbdmono hAbdmono hGbd0 hAbd0 ?_ ?_ hytcont ?_
  · intro T hT yt hyt0 hderiv t ht
    have hs0 : yt 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : yt 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    have hgate := chiGate_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := cαq) (L := 1) (R := R) (M := M)
      (yt := yt) (T := T) hderiv hs0 hc0 t ht
    have hgain := gain_eval_yt (d := d_U) (V := UniversalLocalView) yt t
    have halpha := alpha_coord_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := cαq) (L := 1) (R := R)
      (yt := yt) (T := T) hderiv t ht
    have hα0 : yt 0 (selOfContract UniversalLocalView (contractAlpha d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractAlpha]
    have hwg : yt t (selWarmGainCoord d_U UniversalLocalView) = (g₀ : ℝ) := by
      have hconst := warmGain_coord_const (branch := branchU)
        (chiResetP := selChiResetPoly d_U UniversalLocalView M)
        (chiGateP := selChiGatePoly d_U UniversalLocalView M)
        (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
        (gainP := selGainPoly d_U UniversalLocalView)
        (PpolyP := muReadoutPoly eta heta) (HP := HP)
        (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
        (cαq := cαq) (L := 1) (R := R)
        (yt := yt) (T := T) hderiv t ht
      rw [hconst, hyt0]
      simp [selectorEuclInitQ, selWarmGainCoord, Fin.append_right]
      rfl
    have heq :
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selChiGatePoly d_U UniversalLocalView M) *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selGainPoly d_U UniversalLocalView) =
        ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp ((cαq : ℝ) * t)) := by
      rw [hgate, hgain, hwg, halpha, hα0]
      ring
    have hq0 : 0 ≤ ((1 + Real.sin t) / 2) ^ M := by
      simpa [qPulse] using qPulse_nonneg M t
    have hq1 : ((1 + Real.sin t) / 2) ^ M ≤ 1 := by
      simpa [qPulse] using qPulse_le_one M t
    rw [heq, abs_of_nonneg
      (mul_nonneg hq0 (mul_nonneg hg0 (le_of_lt (Real.exp_pos _))))]
    calc
      ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp ((cαq : ℝ) * t))
          ≤ 1 * ((g₀ : ℝ) * Real.exp ((cαq : ℝ) * t)) := by
            exact mul_le_mul_of_nonneg_right hq1
              (mul_nonneg hg0 (le_of_lt (Real.exp_pos _)))
      _ ≤ (g₀ : ℝ) * Real.exp ((cαq : ℝ) * T) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (le_of_lt ht.2) hcα0))
          hg0
      _ = Gbd T := rfl
  · intro T hT yt hyt0 hderiv t ht
    have hs0 : yt 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : yt 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    have hreset := chiReset_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := cαq) (L := 1) (R := R) (M := M)
      (yt := yt) (T := T) hderiv hs0 hc0 t ht
    have hkappa := kappa_eval_yt (d := d_U) (V := UniversalLocalView) κ₀ yt t
    rw [hreset, hkappa]
    exact mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) M) hκ0
  · intro T hT yt hyt0 hderiv t ht
    have hA := contractA_coord_abs_bound
      (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := cαq) (L := 1) (R := R)
      (x₀ := x₀) (w := w) (warmGainInit := g₀) (yt := yt) (T := T) (Rbd := Rbd)
      hT hKq0 (hytcont T hT yt hyt0 hderiv) hyt0 hderiv
      (hRen T hT yt hyt0 hderiv) t ht
    rw [hyt0] at hA
    simpa [Abd, selectorMUInit] using hA

private theorem selector_gate_exp_unique_withCAlpha {n : ℕ}
    (y : ℝ → Fin n → ℝ) (gate μ : Fin n) (pulse pulseDeriv : ℝ → ℝ)
    (hgate0 : y 0 gate = 1) (hμ0 : y 0 μ = 0)
    (hgate : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun τ => y τ gate)
        (-((1000 : ℝ) * pulse s + y s μ * pulseDeriv s) * y s gate) s)
    (hμ : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun τ => y τ μ) 1000 s)
    (hpulse : ∀ s : ℝ, HasDerivAt pulse (pulseDeriv s) s) :
    ∀ t : ℝ, 0 ≤ t →
      y t gate = Real.exp (-(y t μ * pulse t)) := by
  intro t ht
  let G : ℝ → ℝ := fun s =>
    y s gate * Real.exp (y s μ * pulse s)
  have hGconst := affine_of_const_deriv (T := t + 1) (c := (0 : ℝ)) G ?_
    t ⟨ht, by linarith⟩
  have hG0 : G 0 = 1 := by simp [G, hgate0, hμ0]
  have hGt : G t = 1 := by simpa [hG0] using hGconst
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
    convert hG using 1 <;> ring_nf

theorem selector_gateZ_realize_withCAlpha
    (cαq : ℚ) (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ)
    (y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ)
    (hy0 : y 0 = selectorMUInit x₀ w g₀)
    (hyode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y
        (selectorMUFieldWithCAlpha cαq eta heta M κ₀ g₀ HP Kq R (y t)) t) :
    ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
        bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t := by
  let gate := selOfContract UniversalLocalView (contractGateZ d_U)
  let μ := selOfContract UniversalLocalView (contractMu d_U)
  have hgate0 : y 0 gate = 1 := by
    rw [hy0]; simp [gate, selectorMUInit, selectorEuclInitQ, selOfContract, contractGateZ]
  have hμ0 : y 0 μ = 0 := by
    rw [hy0]; simp [μ, selectorMUInit, selectorEuclInitQ, selOfContract, contractMu]
  have hμder : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun τ => y τ μ) 1000 s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) μ
    simp only [selectorMUFieldWithCAlpha] at hpi
    rw [aprioriField_mu_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := cαq)
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
        (-((1000 : ℝ) * rPulse 1 s + y s μ * (-(Real.cos s / 2))) * y s gate) s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) gate
    simp only [selectorMUFieldWithCAlpha] at hpi
    rw [aprioriField_gateZ_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := cαq)
      (L := 1) (R := R)] at hpi
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    have hsc := sc_realize (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := cαq)
      (L := 1) (R := R) (yt := y) (T := s + 1)
      (fun r hr => hyode r hr.1) hs0 hc0 s ⟨hs, by linarith⟩
    have hrp : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selRP d_U UniversalLocalView 1) = rPulse 1 s := by
      simp [selRP, rPulse, hsc.1]; ring
    have hrpd : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selRPderiv d_U UniversalLocalView 1) = -(Real.cos s / 2) := by
      simp [selRPderiv, hsc.1, hsc.2]; ring
    rw [hrp, hrpd] at hpi
    simpa [gate, μ] using hpi
  intro t ht
  simpa [gate, μ, bGateZ] using
    selector_gate_exp_unique_withCAlpha y gate μ (rPulse 1)
      (fun s => -(Real.cos s / 2)) hgate0 hμ0 hgateDer hμder hpulse t ht

theorem selector_gateU_realize_withCAlpha
    (cαq : ℚ) (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ)
    (y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ)
    (hy0 : y 0 = selectorMUInit x₀ w g₀)
    (hyode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y
        (selectorMUFieldWithCAlpha cαq eta heta M κ₀ g₀ HP Kq R (y t)) t) :
    ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract UniversalLocalView (contractGateU d_U)) =
        bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t := by
  let gate := selOfContract UniversalLocalView (contractGateU d_U)
  let μ := selOfContract UniversalLocalView (contractMu d_U)
  have hgate0 : y 0 gate = 1 := by
    rw [hy0]; simp [gate, selectorMUInit, selectorEuclInitQ, selOfContract, contractGateU]
  have hμ0 : y 0 μ = 0 := by
    rw [hy0]; simp [μ, selectorMUInit, selectorEuclInitQ, selOfContract, contractMu]
  have hμder : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun τ => y τ μ) 1000 s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) μ
    simp only [selectorMUFieldWithCAlpha] at hpi
    rw [aprioriField_mu_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := cαq)
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
        (-((1000 : ℝ) * qPulse 1 s + y s μ * (Real.cos s / 2)) * y s gate) s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) gate
    simp only [selectorMUFieldWithCAlpha] at hpi
    rw [aprioriField_gateU_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := cαq)
      (L := 1) (R := R)] at hpi
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    have hsc := sc_realize (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1000 : ℚ)) (cαq := cαq)
      (L := 1) (R := R) (yt := y) (T := s + 1)
      (fun r hr => hyode r hr.1) hs0 hc0 s ⟨hs, by linarith⟩
    have hqp : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selQP d_U UniversalLocalView 1) = qPulse 1 s := by
      simp [selQP, qPulse, hsc.1]; ring
    have hqpd : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selQPderiv d_U UniversalLocalView 1) = Real.cos s / 2 := by
      simp [selQPderiv, hsc.1, hsc.2]; ring
    rw [hqp, hqpd] at hpi
    simpa [gate, μ] using hpi
  intro t ht
  simpa [gate, μ, bGateU] using
    selector_gate_exp_unique_withCAlpha y gate μ (qPulse 1)
      (fun s => Real.cos s / 2) hgate0 hμ0 hgateDer hμder hpulse t ht

theorem selector_sol_exists_MU_withCAlpha
    (p : DynGateParams) (cαq : ℚ)
    (hA : p.A = ((1 : ℚ) : ℝ))
    (hcμ : p.cμ = ((1000 : ℚ) : ℝ))
    (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = 1)
    (hcα0 : 0 ≤ (cαq : ℝ))
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco
          (selectorMUFieldWithCAlpha cαq eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco
          (selectorMUFieldWithCAlpha cαq eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ UniversalLocalView HP)| ≤ Rbd)
    (hgateZ :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUFieldWithCAlpha cαq eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorMUFieldWithCAlpha cαq eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t) :
    ∃ sol : SelectorDynSol d_U B_U UniversalLocalView p selectorSchedule
        branchU
        (fun t => ((1 + Real.cos t) / 2) ^ M)
        (fun t => ((1 + Real.sin t) / 2) ^ M)
        (fun _ => (κ₀ : ℝ))
        (fun t => (g₀ : ℝ) * Real.exp (p.cα * t))
        (universalPval eta heta),
      sol.z 0 = sol.init_z ∧ sol.u 0 = sol.init_u ∧
        (∀ i,
          sol.u 0 i =
            ((selectorEuclInitQ d_U UniversalLocalView x₀ w g₀
              (selU UniversalLocalView i) : ℚ) : ℝ)) ∧
        sol.ZUFiniteCoordBound := by
  classical
  refine selector_sol_exists
    (p := p) (sched := selectorSchedule) (branch := branchU)
    (chiResetP := selChiResetPoly d_U UniversalLocalView M)
    (chiGateP := selChiGatePoly d_U UniversalLocalView M)
    (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
    (gainP := selGainPoly d_U UniversalLocalView)
    (PpolyP := muReadoutPoly eta heta) (HP := HP)
    (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
    (cαq := cαq) (L := 1) (R := R)
    (hA := hA) (hcμ := hcμ) (hcα := hcα) (hL := hL)
    (hdomain_nonneg := by intro t ht; simpa [selectorSchedule] using ht)
    (chiResetF := fun t => ((1 + Real.cos t) / 2) ^ M)
    (chiGateF := fun t => ((1 + Real.sin t) / 2) ^ M)
    (kappaF := fun _ => (κ₀ : ℝ))
    (gainF := fun t => (g₀ : ℝ) * Real.exp (p.cα * t))
    (readoutP := universalPval eta heta) (x₀ := x₀) (w := w) (warmGainInit := g₀) ?_
    hgateZ hgateU ?_ ?_ ?_ ?_ ?_
  · exact selector_finiteHorizonBound_MU_withCAlpha cαq hcα0 eta heta M κ₀ g₀
      HP Kq R x₀ w hκ0 hg0 hKq0 hytcont hRen
  · intro y hy0 hyode t ht
    have hT : 0 < t + 1 := by linarith
    have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    exact chiReset_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := cαq) (L := 1) (R := R) (M := M)
      (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) hs0 hc0 t htIco
  · intro y hy0 hyode t ht
    have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    exact chiGate_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := cαq) (L := 1) (R := R) (M := M)
      (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) hs0 hc0 t htIco
  · intro y _hy0 _hyode t _ht
    exact kappa_eval_yt (d := d_U) (V := UniversalLocalView) κ₀ y t
  · intro y hy0 hyode t ht
    have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hα0 : y 0 (selOfContract UniversalLocalView (contractAlpha d_U)) = 1 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractAlpha]
    rw [gain_eval_yt (d := d_U) (V := UniversalLocalView) y t]
    have hwg : y t (selWarmGainCoord d_U UniversalLocalView) = (g₀ : ℝ) := by
      have hconst := warmGain_coord_const (branch := branchU)
        (chiResetP := selChiResetPoly d_U UniversalLocalView M)
        (chiGateP := selChiGatePoly d_U UniversalLocalView M)
        (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
        (gainP := selGainPoly d_U UniversalLocalView)
        (PpolyP := muReadoutPoly eta heta) (HP := HP)
        (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
        (cαq := cαq) (L := 1) (R := R)
        (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) t htIco
      rw [hconst, hy0]
      simp [selectorMUInit, selectorEuclInitQ, selWarmGainCoord, Fin.append_right]
      rfl
    rw [hwg]
    rw [alpha_coord_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := cαq) (L := 1) (R := R)
      (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) t htIco]
    rw [hα0, hcα]
    ring
  · intro y _hy0 _hyode v t _ht
    exact muReadoutPoly_eval_yt eta heta v y t

theorem selector_sol_exists_MU38
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ UniversalLocalView HP)| ≤ Rbd)
    (hgateZ :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUField38 eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUField38 eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t) :
    ∃ sol : SelectorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
        branchU
        (fun t => ((1 + Real.cos t) / 2) ^ M)
        (fun t => ((1 + Real.sin t) / 2) ^ M)
        (fun _ => (κ₀ : ℝ))
        (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
        (universalPval eta heta),
      sol.z 0 = sol.init_z ∧ sol.u 0 = sol.init_u ∧
        (∀ i,
          sol.u 0 i =
            ((selectorEuclInitQ d_U UniversalLocalView x₀ w g₀
              (selU UniversalLocalView i) : ℚ) : ℝ)) ∧
        sol.ZUFiniteCoordBound :=
  selector_sol_exists_MU_withCAlpha bgpParams38 (300 : ℚ)
    (by norm_num [bgpParams38]) (by norm_num [bgpParams38])
    (by norm_num [bgpParams38]) rfl (by norm_num)
    eta heta M κ₀ g₀ HP Kq R x₀ w hκ0 hg0 hKq0 hytcont hRen hgateZ hgateU

/-- `bgpParams38` version of `selector_sol_exists_MU_clean`. -/
theorem selector_sol_exists_MU38_clean
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ UniversalLocalView HP)| ≤ Rbd) :
    ∃ sol : SelectorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
        branchU
        (fun t => ((1 + Real.cos t) / 2) ^ M)
        (fun t => ((1 + Real.sin t) / 2) ^ M)
        (fun _ => (κ₀ : ℝ))
        (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
        (universalPval eta heta),
      sol.z 0 = sol.init_z ∧ sol.u 0 = sol.init_u ∧
        (∀ i,
          sol.u 0 i =
            ((selectorEuclInitQ d_U UniversalLocalView x₀ w g₀
              (selU UniversalLocalView i) : ℚ) : ℝ)) ∧
        sol.ZUFiniteCoordBound :=
  selector_sol_exists_MU38 eta heta M κ₀ g₀ HP Kq R x₀ w
    hκ0 hg0 hKq0 hytcont hRen
    (fun y hy0 hyode =>
      selector_gateZ_realize_withCAlpha (300 : ℚ) eta heta M κ₀ g₀
        HP Kq R x₀ w y hy0 hyode)
    (fun y hy0 hyode =>
      selector_gateU_realize_withCAlpha (300 : ℚ) eta heta M κ₀ g₀
        HP Kq R x₀ w y hy0 hyode)

end Ripple.BoundedUniversality.BGP

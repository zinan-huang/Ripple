import Ripple.BoundedUniversality.BGP.SelectorReplicatorPrefixSimplex
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSolWired
import Ripple.Core.ODEBox

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorAprioriBound
-----------------------------------------
Finite-time a-priori bounds for the MU selector replicator field.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance MeasureTheory
open scoped BigOperators Topology
open MvPolynomial

variable {d B : ℕ} {V : Type} [Fintype V]
  (branch : V → BranchData d B)
  (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
  (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
  (HP : MvPolynomial (Fin d) ℚ)
  (Aq Kq cμq cαq : ℚ) (L R : ℕ)
  (y : Fin (selectorDim d V) → ℝ)

theorem replAprioriField_z_eq (i : Fin d) :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selZ V i) =
      (Aq : ℝ) * y (selOfContract V (contractAlpha d)) * y (selOfContract V (contractGateZ d))
        * (MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selectorMixField branch i)
          - y (selZ V i)) := by
  unfold selectorReplicatorAssembledVectorField
  rw [show selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selZ V i) =
        C Aq * X (selOfContract V (contractAlpha d)) * X (selOfContract V (contractGateZ d))
          * (selectorMixField branch i - X (selZ V i)) from by
    simp [selectorReplicatorAssembledField, selZ, selOfContract, contractZ, contractTailZ]]
  simp [eval₂_mul, eval₂_C, eval₂_X, eval₂_sub]

theorem replAprioriField_u_eq (i : Fin d) :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selU V i) =
      (Aq : ℝ) * y (selOfContract V (contractAlpha d)) * y (selOfContract V (contractGateU d))
        * (y (selZ V i) - y (selU V i)) := by
  unfold selectorReplicatorAssembledVectorField
  rw [show selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selU V i) =
        C Aq * X (selOfContract V (contractAlpha d)) * X (selOfContract V (contractGateU d))
          * (X (selZ V i) - X (selU V i)) from by
    simp [selectorReplicatorAssembledField, selU, selZ, selOfContract, contractU, contractTailU]]
  simp [eval₂_mul, eval₂_C, eval₂_X, eval₂_sub]

theorem replAprioriField_G_eq :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selGCoord d V) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) y chiGateP
        * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y gainP := by
  unfold selectorReplicatorAssembledVectorField
  rw [show selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selGCoord d V) = selectorGainFieldPoly chiGateP gainP from by
    simp [selectorReplicatorAssembledField, selGCoord, Fin.append_right, Fin.append_left]; rfl]
  rw [eval₂_selectorGainFieldPoly]

theorem replAprioriField_A_eq :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractA d)) =
      (Kq : ℝ) *
        (((1 / 2 : ℝ) *
          (1 - y (selOfContract V (contractC d)))) ^ R) *
        (MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selRenameZ V HP) -
          y (selOfContract V (contractA d))) := by
  unfold selectorReplicatorAssembledVectorField
  rw [show selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
        PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractA d)) =
        C Kq *
          ((C (1 / 2 : ℚ) *
            (1 - X (selOfContract V (contractC d)))) ^ R) *
          (selRenameZ V HP - X (selOfContract V (contractA d))) from by
    simp [selectorReplicatorAssembledField, selOfContract, contractA, contractTailA]]
  simp [eval₂_mul, eval₂_pow, eval₂_C, eval₂_sub, eval₂_one, eval₂_X,
    eq_ratCast]
theorem repl_sc_conservation
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T,
      (yt t (selOfContract V (contractS d))) ^ 2 + (yt t (selOfContract V (contractC d))) ^ 2
        = (yt 0 (selOfContract V (contractS d))) ^ 2
          + (yt 0 (selOfContract V (contractC d))) ^ 2 := by
  have h := affine_of_const_deriv (T := T) (c := (0 : ℝ))
    (fun s => (yt s (selOfContract V (contractS d))) ^ 2
      + (yt s (selOfContract V (contractC d))) ^ 2) ?_
  · intro t ht; have := h t ht; simpa using this
  · intro t ht
    have hs := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractS d))
    have hc := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractC d))
    rw [replAprioriField_s_eq] at hs
    rw [replAprioriField_c_eq] at hc
    have hs2 := hs.pow 2
    have hc2 := hc.pow 2
    have hsum := hs2.add hc2
    have hz : (2 : ℕ) * yt t (selOfContract V (contractS d)) ^ (2 - 1)
          * yt t (selOfContract V (contractC d))
        + (2 : ℕ) * yt t (selOfContract V (contractC d)) ^ (2 - 1)
          * (-yt t (selOfContract V (contractS d))) = 0 := by
      push_cast; ring
    rw [hz] at hsum
    exact hsum



theorem repl_gateZ_coord_abs_bound
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hSelRP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)| ≤ 1)
    (hSelRPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)| ≤ (L : ℝ)) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractGateZ d))| ≤
        |yt 0 (selOfContract V (contractGateZ d))| *
          Real.exp ((|(cμq : ℝ)|
            + (|yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T)
              * (L : ℝ)) * T) := by
  let k : ℝ → ℝ := fun t =>
    (cμq : ℝ) * MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)
      + yt t (selOfContract V (contractMu d))
        * MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)
  let Kbd : ℝ := |(cμq : ℝ)|
    + (|yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T) * (L : ℝ)
  have hlin := scalar_linear_homog_abs_bound (T := T)
    (g := fun t => yt t (selOfContract V (contractGateZ d))) (k := k)
    (Kbd := Kbd) ?_ ?_
  · simpa [k, Kbd] using hlin
  · intro τ hτ
    let rp := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt τ) (selRP d V L)
    let rpd := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt τ) (selRPderiv d V L)
    let mu := yt τ (selOfContract V (contractMu d))
    let muBd := |yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T
    have hT_nonneg : 0 ≤ T := le_trans hτ.1 (le_of_lt hτ.2)
    have hmuBd_nonneg : 0 ≤ muBd := by
      dsimp [muBd]
      exact add_nonneg (abs_nonneg _)
        (mul_nonneg (abs_nonneg _) hT_nonneg)
    have hmu : |mu| ≤ muBd := by
      dsimp [mu, muBd]
      rw [repl_mu_coord_affine (branch := branch) (chiResetP := chiResetP)
        (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
        (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
        (cμq := cμq) (cαq := cαq) (L := L) (R := R)
        (yt := yt) (T := T) hderiv τ hτ]
      have h1 := abs_add_le (yt 0 (selOfContract V (contractMu d))) ((cμq : ℝ) * τ)
      rw [abs_mul, abs_of_nonneg hτ.1] at h1
      have h2 : |(cμq : ℝ)| * τ ≤ |(cμq : ℝ)| * T :=
        mul_le_mul_of_nonneg_left (le_of_lt hτ.2) (abs_nonneg _)
      linarith
    have hRp : |rp| ≤ 1 := by simpa [rp] using hSelRP τ hτ
    have hRpd : |rpd| ≤ (L : ℝ) := by simpa [rpd] using hSelRPderiv τ hτ
    have hterm1 : |(cμq : ℝ) * rp| ≤ |(cμq : ℝ)| * 1 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hRp (abs_nonneg _)
    have hterm2 : |mu * rpd| ≤ muBd * (L : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul hmu hRpd (abs_nonneg _) hmuBd_nonneg
    have hsum : |(cμq : ℝ) * rp + mu * rpd| ≤ |(cμq : ℝ)| + muBd * (L : ℝ) := by
      calc
        |(cμq : ℝ) * rp + mu * rpd| ≤ |(cμq : ℝ) * rp| + |mu * rpd| :=
          abs_add_le _ _
        _ ≤ |(cμq : ℝ)| * 1 + muBd * (L : ℝ) :=
          add_le_add hterm1 hterm2
        _ = |(cμq : ℝ)| + muBd * (L : ℝ) := by ring
    simpa [k, Kbd, rp, rpd, mu, muBd] using hsum
  · intro τ hτ
    have hpi := (hasDerivAt_pi.mp (hderiv τ hτ))
      (selOfContract V (contractGateZ d))
    rw [replAprioriField_gateZ_eq] at hpi
    simpa [k] using hpi

theorem repl_gateU_coord_abs_bound
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hSelQP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)| ≤ 1)
    (hSelQPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)| ≤ (L : ℝ)) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractGateU d))| ≤
        |yt 0 (selOfContract V (contractGateU d))| *
          Real.exp ((|(cμq : ℝ)|
            + (|yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T)
              * (L : ℝ)) * T) := by
  let k : ℝ → ℝ := fun t =>
    (cμq : ℝ) * MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)
      + yt t (selOfContract V (contractMu d))
        * MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)
  let Kbd : ℝ := |(cμq : ℝ)|
    + (|yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T) * (L : ℝ)
  have hlin := scalar_linear_homog_abs_bound (T := T)
    (g := fun t => yt t (selOfContract V (contractGateU d))) (k := k)
    (Kbd := Kbd) ?_ ?_
  · simpa [k, Kbd] using hlin
  · intro τ hτ
    let qp := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt τ) (selQP d V L)
    let qpd := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt τ) (selQPderiv d V L)
    let mu := yt τ (selOfContract V (contractMu d))
    let muBd := |yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T
    have hT_nonneg : 0 ≤ T := le_trans hτ.1 (le_of_lt hτ.2)
    have hmuBd_nonneg : 0 ≤ muBd := by
      dsimp [muBd]
      exact add_nonneg (abs_nonneg _)
        (mul_nonneg (abs_nonneg _) hT_nonneg)
    have hmu : |mu| ≤ muBd := by
      dsimp [mu, muBd]
      rw [repl_mu_coord_affine (branch := branch) (chiResetP := chiResetP)
        (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
        (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
        (cμq := cμq) (cαq := cαq) (L := L) (R := R)
        (yt := yt) (T := T) hderiv τ hτ]
      have h1 := abs_add_le (yt 0 (selOfContract V (contractMu d))) ((cμq : ℝ) * τ)
      rw [abs_mul, abs_of_nonneg hτ.1] at h1
      have h2 : |(cμq : ℝ)| * τ ≤ |(cμq : ℝ)| * T :=
        mul_le_mul_of_nonneg_left (le_of_lt hτ.2) (abs_nonneg _)
      linarith
    have hQp : |qp| ≤ 1 := by simpa [qp] using hSelQP τ hτ
    have hQpd : |qpd| ≤ (L : ℝ) := by simpa [qpd] using hSelQPderiv τ hτ
    have hterm1 : |(cμq : ℝ) * qp| ≤ |(cμq : ℝ)| * 1 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hQp (abs_nonneg _)
    have hterm2 : |mu * qpd| ≤ muBd * (L : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul hmu hQpd (abs_nonneg _) hmuBd_nonneg
    have hsum : |(cμq : ℝ) * qp + mu * qpd| ≤ |(cμq : ℝ)| + muBd * (L : ℝ) := by
      calc
        |(cμq : ℝ) * qp + mu * qpd| ≤ |(cμq : ℝ) * qp| + |mu * qpd| :=
          abs_add_le _ _
        _ ≤ |(cμq : ℝ)| * 1 + muBd * (L : ℝ) :=
          add_le_add hterm1 hterm2
        _ = |(cμq : ℝ)| + muBd * (L : ℝ) := by ring
    simpa [k, Kbd, qp, qpd, mu, muBd] using hsum
  · intro τ hτ
    have hpi := (hasDerivAt_pi.mp (hderiv τ hτ))
      (selOfContract V (contractGateU d))
    rw [replAprioriField_gateU_eq] at hpi
    simpa [k] using hpi



theorem repl_G_coord_abs_bound
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T Gbd : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hGbd : 0 ≤ Gbd)
    (hChiGain : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selGCoord d V)| ≤ |yt 0 (selGCoord d V)| + Gbd * T := by
  intro t ht
  let g : ℝ → ℝ := fun s => yt s (selGCoord d V)
  let g' : ℝ → ℝ := fun s =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) chiGateP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) gainP
  have hcont : ContinuousOn g (Icc (0 : ℝ) t) := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hpi := (hasDerivAt_pi.mp (hderiv s hsT)) (selGCoord d V)
    rw [replAprioriField_G_eq] at hpi
    exact hpi.continuousAt.continuousWithinAt
  have hderivWithin : ∀ s ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt g (g' s) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hpi := (hasDerivAt_pi.mp (hderiv s hsT)) (selGCoord d V)
    rw [replAprioriField_G_eq] at hpi
    exact hpi.hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, ‖g' s‖ ≤ 0 * ‖g s‖ + Gbd := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    simpa [g', Real.norm_eq_abs] using hChiGain s hsT
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := g) (f' := g') (δ := |g 0|) (K := 0) (ε := Gbd)
    (a := (0 : ℝ)) (b := t) hcont hderivWithin
    (by simp [g, Real.norm_eq_abs]) hbound t ⟨ht.1, le_rfl⟩
  have ht_bound : |g t| ≤ |g 0| + Gbd * t := by
    simpa [g, Real.norm_eq_abs, gronwallBound_K0, sub_zero] using hgr
  have hGT : Gbd * t ≤ Gbd * T :=
    mul_le_mul_of_nonneg_left (le_of_lt ht.2) hGbd
  dsimp [g] at ht_bound ⊢
  linarith



theorem repl_zu_coord_abs_bound (i : Fin d)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T Cbd Mbd : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hCbd : 0 ≤ Cbd) (hMbd : 0 ≤ Mbd)
    (hCoef : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd ∧
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd)
    (hMix : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selectorMixField branch i)| ≤ Mbd) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selZ V i)| ≤
        gronwallBound ‖(yt 0 (selZ V i), yt 0 (selU V i))‖
          (2 * Cbd) (Cbd * Mbd) T ∧
      |yt t (selU V i)| ≤
        gronwallBound ‖(yt 0 (selZ V i), yt 0 (selU V i))‖
          (2 * Cbd) (Cbd * Mbd) T := by
  intro t ht
  let f : ℝ → ℝ × ℝ := fun s => (yt s (selZ V i), yt s (selU V i))
  let f' : ℝ → ℝ × ℝ := fun s =>
    ((Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
        yt s (selOfContract V (contractGateZ d)) *
        (MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) (selectorMixField branch i)
          - yt s (selZ V i)),
      (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
        yt s (selOfContract V (contractGateU d)) *
        (yt s (selZ V i) - yt s (selU V i)))
  have hcont : ContinuousOn f (Icc (0 : ℝ) t) := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hz := (hasDerivAt_pi.mp (hderiv s hsT)) (selZ V i)
    have hu := (hasDerivAt_pi.mp (hderiv s hsT)) (selU V i)
    exact (hz.prodMk hu).continuousAt.continuousWithinAt
  have hderivWithin : ∀ s ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt f (f' s) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hz := (hasDerivAt_pi.mp (hderiv s hsT)) (selZ V i)
    have hu := (hasDerivAt_pi.mp (hderiv s hsT)) (selU V i)
    rw [replAprioriField_z_eq] at hz
    rw [replAprioriField_u_eq] at hu
    have hpair : HasDerivAt f (f' s) s := by simpa [f, f'] using (hz.prodMk hu)
    exact hpair.hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) t,
      ‖f' s‖ ≤ (2 * Cbd) * ‖f s‖ + Cbd * Mbd := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    let z := yt s (selZ V i)
    let u := yt s (selU V i)
    let m := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) (selectorMixField branch i)
    let az := (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
      yt s (selOfContract V (contractGateZ d))
    let au := (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
      yt s (selOfContract V (contractGateU d))
    have haz : |az| ≤ Cbd := by simpa [az] using (hCoef s hsT).1
    have hau : |au| ≤ Cbd := by simpa [au] using (hCoef s hsT).2
    have hm : |m| ≤ Mbd := by simpa [m] using hMix s hsT
    have hzle : |z| ≤ ‖(z, u)‖ := by
      change |z| ≤ max ‖z‖ ‖u‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact le_max_left _ _
    have hule : |u| ≤ ‖(z, u)‖ := by
      change |u| ≤ max ‖z‖ ‖u‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact le_max_right _ _
    have hmz_abs : |m - z| ≤ |m| + |z| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le m (-z)
    have hzu_abs : |z - u| ≤ |z| + |u| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le z (-u)
    have hdz : |az * (m - z)| ≤ (2 * Cbd) * ‖(z, u)‖ + Cbd * Mbd := by
      calc
        |az * (m - z)| = |az| * |m - z| := abs_mul _ _
        _ ≤ Cbd * |m - z| :=
          mul_le_mul_of_nonneg_right haz (abs_nonneg _)
        _ ≤ Cbd * (|m| + |z|) :=
          mul_le_mul_of_nonneg_left hmz_abs hCbd
        _ ≤ Cbd * (Mbd + ‖(z, u)‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hm hzle) hCbd
        _ = Cbd * Mbd + Cbd * ‖(z, u)‖ := by ring
        _ ≤ (2 * Cbd) * ‖(z, u)‖ + Cbd * Mbd := by
          have hcn : 0 ≤ Cbd * ‖(z, u)‖ := mul_nonneg hCbd (norm_nonneg _)
          linarith
    have hdu : |au * (z - u)| ≤ (2 * Cbd) * ‖(z, u)‖ + Cbd * Mbd := by
      calc
        |au * (z - u)| = |au| * |z - u| := abs_mul _ _
        _ ≤ Cbd * |z - u| :=
          mul_le_mul_of_nonneg_right hau (abs_nonneg _)
        _ ≤ Cbd * (|z| + |u|) :=
          mul_le_mul_of_nonneg_left hzu_abs hCbd
        _ ≤ Cbd * (‖(z, u)‖ + ‖(z, u)‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hzle hule) hCbd
        _ ≤ (2 * Cbd) * ‖(z, u)‖ + Cbd * Mbd := by
          have hε : 0 ≤ Cbd * Mbd := mul_nonneg hCbd hMbd
          nlinarith
    simpa [f, f', z, u, m, az, au, Real.norm_eq_abs] using max_le hdz hdu
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := f) (f' := f') (δ := ‖f 0‖) (K := 2 * Cbd)
    (ε := Cbd * Mbd) (a := (0 : ℝ)) (b := t)
    hcont hderivWithin (by simp [f]) hbound t ⟨ht.1, le_rfl⟩
  have hK : 0 ≤ 2 * Cbd := mul_nonneg (by norm_num) hCbd
  have hε : 0 ≤ Cbd * Mbd := mul_nonneg hCbd hMbd
  have hmono := gronwallBound_mono (δ := ‖f 0‖) (K := 2 * Cbd)
    (ε := Cbd * Mbd) (norm_nonneg _) hε hK
  have hpairT : ‖f t‖ ≤
      gronwallBound ‖f 0‖ (2 * Cbd) (Cbd * Mbd) T := by
    have hpairt : ‖f t‖ ≤ gronwallBound ‖f 0‖ (2 * Cbd) (Cbd * Mbd) t := by
      simpa [sub_zero] using hgr
    exact hpairt.trans (hmono (le_of_lt ht.2))
  have hz_abs : |yt t (selZ V i)| ≤ ‖f t‖ := by
    have := norm_fst_le (f t)
    simpa [f, Real.norm_eq_abs] using this
  have hu_abs : |yt t (selU V i)| ≤ ‖f t‖ := by
    have := norm_snd_le (f t)
    simpa [f, Real.norm_eq_abs] using this
  constructor
  · exact hz_abs.trans (by simpa [f] using hpairT)
  · exact hu_abs.trans (by simpa [f] using hpairT)

/-- The selector weight coordinate is nonnegative on `[0,T)` once the reset
factor has the expected sign. -/
private theorem selector_replicator_sc_abs_le_one
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    {T : ℝ} (yt : ℝ → Fin (selectorDim d V) → ℝ)
    (hyt0 : yt 0 = (fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractS d))| ≤ 1 ∧
      |yt t (selOfContract V (contractC d))| ≤ 1 := by
  intro t ht
  have hsc := repl_sc_conservation (branch := branch) (chiResetP := chiResetP)
    (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
    (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
    (cμq := cμq) (cαq := cαq) (L := L) (R := R)
    (yt := yt) (T := T) hderiv t ht
  rw [hyt0] at hsc
  have hsc1 :
      (yt t (selOfContract V (contractS d))) ^ 2
        + (yt t (selOfContract V (contractC d))) ^ 2 = 1 := by
    rw [hsc]
    norm_num [selectorReplicatorEuclInitQ, selOfContract, contractS, contractC, Fin.isValue]
  have hs_sq :
      (yt t (selOfContract V (contractS d))) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (yt t (selOfContract V (contractC d))), hsc1]
  have hc_sq :
      (yt t (selOfContract V (contractC d))) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (yt t (selOfContract V (contractS d))), hsc1]
  exact ⟨abs_le_of_sq_le_sq (b := (1:ℝ)) (by nlinarith [hs_sq]) (by norm_num),
    abs_le_of_sq_le_sq (b := (1:ℝ)) (by nlinarith [hc_sq]) (by norm_num)⟩



private theorem selector_replicator_pulse_bounds
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    {T : ℝ} (yt : ℝ → Fin (selectorDim d V) → ℝ)
    (hyt0 : yt 0 = (fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    (∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)| ≤ 1) ∧
    (∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)| ≤ (L : ℝ)) ∧
    (∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)| ≤ 1) ∧
    (∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)| ≤ (L : ℝ)) := by
  classical
  have hsc := selector_replicator_sc_abs_le_one branch chiResetP chiGateP kappaP gainP
    PpolyP HP Aq Kq cμq cαq L R x₀ w warmGainInit yt hyt0 hderiv
  have hpulse :
      ∀ (σ : ℝ), |σ| ≤ 1 →
        |((1 / 2 : ℝ) * (1 - σ)) ^ L| ≤ 1 ∧
        |((1 / 2 : ℝ) * (1 + σ)) ^ L| ≤ 1 := by
    intro σ hσ
    have hσlo : -1 ≤ σ := (abs_le.mp hσ).1
    have hσhi : σ ≤ 1 := (abs_le.mp hσ).2
    have hr0 : 0 ≤ (1 / 2 : ℝ) * (1 - σ) := by nlinarith
    have hr1 : (1 / 2 : ℝ) * (1 - σ) ≤ 1 := by nlinarith
    have hq0 : 0 ≤ (1 / 2 : ℝ) * (1 + σ) := by nlinarith
    have hq1 : (1 / 2 : ℝ) * (1 + σ) ≤ 1 := by nlinarith
    exact ⟨by
      rw [abs_of_nonneg (pow_nonneg hr0 L)]
      exact pow_le_one₀ hr0 hr1, by
      rw [abs_of_nonneg (pow_nonneg hq0 L)]
      exact pow_le_one₀ hq0 hq1⟩
  have hpulseDeriv :
      ∀ (σ κ : ℝ), |σ| ≤ 1 → |κ| ≤ 1 →
        |(L : ℝ) * ((1 / 2 : ℝ) * (1 - σ)) ^ (L - 1) *
            (-(1 / 2 : ℝ) * κ)| ≤ (L : ℝ) ∧
        |(L : ℝ) * ((1 / 2 : ℝ) * (1 + σ)) ^ (L - 1) *
            ((1 / 2 : ℝ) * κ)| ≤ (L : ℝ) := by
    intro σ κ hσ hκ
    have hσlo : -1 ≤ σ := (abs_le.mp hσ).1
    have hσhi : σ ≤ 1 := (abs_le.mp hσ).2
    have hr0 : 0 ≤ (1 / 2 : ℝ) * (1 - σ) := by nlinarith
    have hr1 : (1 / 2 : ℝ) * (1 - σ) ≤ 1 := by nlinarith
    have hq0 : 0 ≤ (1 / 2 : ℝ) * (1 + σ) := by nlinarith
    have hq1 : (1 / 2 : ℝ) * (1 + σ) ≤ 1 := by nlinarith
    have hκhalf : |(1 / 2 : ℝ) * κ| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      nlinarith [hκ]
    constructor
    · calc
        |(L : ℝ) * ((1 / 2 : ℝ) * (1 - σ)) ^ (L - 1) *
            (-(1 / 2 : ℝ) * κ)|
            = (L : ℝ) *
              |((1 / 2 : ℝ) * (1 - σ)) ^ (L - 1)| *
              |-(1 / 2 : ℝ) * κ| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg L)]
        _ ≤ (L : ℝ) * 1 * 1 := by
          gcongr
          · rw [abs_of_nonneg (pow_nonneg hr0 (L - 1))]
            exact pow_le_one₀ hr0 hr1
          · simpa [abs_neg] using hκhalf
        _ = (L : ℝ) := by ring
    · calc
        |(L : ℝ) * ((1 / 2 : ℝ) * (1 + σ)) ^ (L - 1) *
            ((1 / 2 : ℝ) * κ)|
            = (L : ℝ) *
              |((1 / 2 : ℝ) * (1 + σ)) ^ (L - 1)| *
              |(1 / 2 : ℝ) * κ| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg L)]
        _ ≤ (L : ℝ) * 1 * 1 := by
          gcongr
          rw [abs_of_nonneg (pow_nonneg hq0 (L - 1))]
          exact pow_le_one₀ hq0 hq1
        _ = (L : ℝ) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    have hs := (hsc t ht).1
    simpa [selRP, eval₂_pow, eval₂_mul, eval₂_C, eval₂_sub, eval₂_one, eval₂_X]
      using (hpulse (yt t (selOfContract V (contractS d))) hs).1
  · intro t ht
    have hs := (hsc t ht).1
    have hc := (hsc t ht).2
    simpa [selRPderiv, eval₂_pow, eval₂_mul, eval₂_C, eval₂_sub, eval₂_one,
      eval₂_X] using (hpulseDeriv (yt t (selOfContract V (contractS d)))
        (yt t (selOfContract V (contractC d))) hs hc).1
  · intro t ht
    have hs := (hsc t ht).1
    simpa [selQP, eval₂_pow, eval₂_mul, eval₂_C, eval₂_add, eval₂_one, eval₂_X]
      using (hpulse (yt t (selOfContract V (contractS d))) hs).2
  · intro t ht
    have hs := (hsc t ht).1
    have hc := (hsc t ht).2
    simpa [selQPderiv, eval₂_pow, eval₂_mul, eval₂_C, eval₂_add, eval₂_one,
      eval₂_X] using (hpulseDeriv (yt t (selOfContract V (contractS d)))
        (yt t (selOfContract V (contractC d))) hs hc).2



theorem repl_zu_coord_abs_bound_selfcontained (i : Fin d)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T Cbd Cmix kmix : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hCbd : 0 ≤ Cbd) (hCmix : 0 ≤ Cmix) (hkmix : 0 ≤ kmix)
    (hCoefZ : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd)
    (hCoefU : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd)
    (hMixAff : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selectorMixField branch i)| ≤
        Cmix + kmix * |yt t (selU V i)|) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selZ V i)| ≤
        gronwallBound ‖(yt 0 (selZ V i), yt 0 (selU V i))‖
          (Cbd * (2 + kmix)) (Cbd * Cmix) T ∧
      |yt t (selU V i)| ≤
        gronwallBound ‖(yt 0 (selZ V i), yt 0 (selU V i))‖
          (Cbd * (2 + kmix)) (Cbd * Cmix) T := by
  intro t ht
  let f : ℝ → ℝ × ℝ := fun s => (yt s (selZ V i), yt s (selU V i))
  let f' : ℝ → ℝ × ℝ := fun s =>
    ((Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
        yt s (selOfContract V (contractGateZ d)) *
        (MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) (selectorMixField branch i)
          - yt s (selZ V i)),
      (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
        yt s (selOfContract V (contractGateU d)) *
        (yt s (selZ V i) - yt s (selU V i)))
  have hcont : ContinuousOn f (Icc (0 : ℝ) t) := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hz := (hasDerivAt_pi.mp (hderiv s hsT)) (selZ V i)
    have hu := (hasDerivAt_pi.mp (hderiv s hsT)) (selU V i)
    exact (hz.prodMk hu).continuousAt.continuousWithinAt
  have hderivWithin : ∀ s ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt f (f' s) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hz := (hasDerivAt_pi.mp (hderiv s hsT)) (selZ V i)
    have hu := (hasDerivAt_pi.mp (hderiv s hsT)) (selU V i)
    rw [replAprioriField_z_eq] at hz
    rw [replAprioriField_u_eq] at hu
    have hpair : HasDerivAt f (f' s) s := by simpa [f, f'] using (hz.prodMk hu)
    exact hpair.hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) t,
      ‖f' s‖ ≤ (Cbd * (2 + kmix)) * ‖f s‖ + Cbd * Cmix := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    let z := yt s (selZ V i)
    let u := yt s (selU V i)
    let m := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) (selectorMixField branch i)
    let az := (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
      yt s (selOfContract V (contractGateZ d))
    let au := (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
      yt s (selOfContract V (contractGateU d))
    have haz : |az| ≤ Cbd := by simpa [az] using hCoefZ s hsT
    have hau : |au| ≤ Cbd := by simpa [au] using hCoefU s hsT
    have hm : |m| ≤ Cmix + kmix * |u| := by simpa [m, u] using hMixAff s hsT
    have hzle : |z| ≤ ‖(z, u)‖ := by
      change |z| ≤ max ‖z‖ ‖u‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact le_max_left _ _
    have hule : |u| ≤ ‖(z, u)‖ := by
      change |u| ≤ max ‖z‖ ‖u‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact le_max_right _ _
    have hmN : |m| ≤ Cmix + kmix * ‖(z, u)‖ :=
      hm.trans (by linarith [mul_le_mul_of_nonneg_left hule hkmix])
    have hmz_abs : |m - z| ≤ |m| + |z| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le m (-z)
    have hzu_abs : |z - u| ≤ |z| + |u| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le z (-u)
    have hdz :
        |az * (m - z)| ≤ (Cbd * (2 + kmix)) * ‖(z, u)‖ + Cbd * Cmix := by
      calc
        |az * (m - z)| = |az| * |m - z| := abs_mul _ _
        _ ≤ Cbd * |m - z| :=
          mul_le_mul_of_nonneg_right haz (abs_nonneg _)
        _ ≤ Cbd * (|m| + |z|) :=
          mul_le_mul_of_nonneg_left hmz_abs hCbd
        _ ≤ Cbd * ((Cmix + kmix * ‖(z, u)‖) + ‖(z, u)‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hmN hzle) hCbd
        _ ≤ (Cbd * (2 + kmix)) * ‖(z, u)‖ + Cbd * Cmix := by
          nlinarith [hCbd, hCmix, hkmix, norm_nonneg (z, u),
            mul_nonneg (mul_nonneg hCbd hkmix) (norm_nonneg (z, u)),
            mul_nonneg hCbd hCmix]
    have hdu :
        |au * (z - u)| ≤ (Cbd * (2 + kmix)) * ‖(z, u)‖ + Cbd * Cmix := by
      calc
        |au * (z - u)| = |au| * |z - u| := abs_mul _ _
        _ ≤ Cbd * |z - u| :=
          mul_le_mul_of_nonneg_right hau (abs_nonneg _)
        _ ≤ Cbd * (|z| + |u|) :=
          mul_le_mul_of_nonneg_left hzu_abs hCbd
        _ ≤ Cbd * (‖(z, u)‖ + ‖(z, u)‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hzle hule) hCbd
        _ ≤ (Cbd * (2 + kmix)) * ‖(z, u)‖ + Cbd * Cmix := by
          nlinarith [hCbd, hCmix, hkmix, norm_nonneg (z, u),
            mul_nonneg (mul_nonneg hCbd hkmix) (norm_nonneg (z, u)),
            mul_nonneg hCbd hCmix]
    simpa [f, f', z, u, m, az, au, Real.norm_eq_abs] using max_le hdz hdu
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := f) (f' := f') (δ := ‖f 0‖) (K := Cbd * (2 + kmix))
    (ε := Cbd * Cmix) (a := (0 : ℝ)) (b := t)
    hcont hderivWithin (by simp [f]) hbound t ⟨ht.1, le_rfl⟩
  have hK : 0 ≤ Cbd * (2 + kmix) :=
    mul_nonneg hCbd (by nlinarith)
  have hε : 0 ≤ Cbd * Cmix := mul_nonneg hCbd hCmix
  have hmono := gronwallBound_mono (δ := ‖f 0‖) (K := Cbd * (2 + kmix))
    (ε := Cbd * Cmix) (norm_nonneg _) hε hK
  have hpairT : ‖f t‖ ≤
      gronwallBound ‖f 0‖ (Cbd * (2 + kmix)) (Cbd * Cmix) T := by
    have hpairt : ‖f t‖ ≤
        gronwallBound ‖f 0‖ (Cbd * (2 + kmix)) (Cbd * Cmix) t := by
      simpa [sub_zero] using hgr
    exact hpairt.trans (hmono (le_of_lt ht.2))
  have hz_abs : |yt t (selZ V i)| ≤ ‖f t‖ := by
    have := norm_fst_le (f t)
    simpa [f, Real.norm_eq_abs] using this
  have hu_abs : |yt t (selU V i)| ≤ ‖f t‖ := by
    have := norm_snd_le (f t)
    simpa [f, Real.norm_eq_abs] using this
  constructor
  · exact hz_abs.trans (by simpa [f] using hpairT)
  · exact hu_abs.trans (by simpa [f] using hpairT)



private def selectorReplicatorMixConst
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B) : ℝ :=
  ∑ v : V, ∑ j : Fin d,
    |BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) j|

/-- Explicit slope for the selector mixture affine estimate. -/
private def selectorReplicatorMixSlope
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B) : ℝ :=
  ∑ v : V, ∑ j : Fin d,
    BranchAction.multiplier B ((branch v).action j)

private theorem selectorReplicatorMixConst_nonneg
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B) :
    0 ≤ selectorReplicatorMixConst branch := by
  dsimp [selectorReplicatorMixConst]
  exact Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _))

private theorem selectorReplicatorMixSlope_nonneg
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B) :
    0 ≤ selectorReplicatorMixSlope branch := by
  dsimp [selectorReplicatorMixSlope]
  exact Finset.sum_nonneg (fun v _ =>
    Finset.sum_nonneg (fun j _ => by
      simpa [BranchAction.multiplier] using
        abs_nonneg (((branch v).action j).scale : ℝ)))

private noncomputable def mvPolynomialBoxBound {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (r : Fin n → ℝ) : ℝ :=
  ∑ m ∈ p.support, |((p.coeff m : ℚ) : ℝ)| * ∏ i : Fin n, r i ^ m i

private theorem mvPolynomialBoxBound_nonneg {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) {r : Fin n → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) :
    0 ≤ mvPolynomialBoxBound p r := by
  dsimp [mvPolynomialBoxBound]
  exact Finset.sum_nonneg fun m _ =>
    mul_nonneg (abs_nonneg _)
      (Finset.prod_nonneg fun i _ => pow_nonneg (hr0 i) _)

private theorem mvPolynomialBoxBound_mono {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) {r s : Fin n → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hrs : ∀ i, r i ≤ s i) :
    mvPolynomialBoxBound p r ≤ mvPolynomialBoxBound p s := by
  dsimp [mvPolynomialBoxBound]
  refine Finset.sum_le_sum ?_
  intro m hm
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine Finset.prod_le_prod ?_ ?_
  · intro i hi
    exact pow_nonneg (hr0 i) _
  · intro i hi
    exact pow_le_pow_left₀ (hr0 i) (hrs i) _

private theorem mvPolynomial_eval₂_abs_le_boxBound {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) {x r : Fin n → ℝ}
    (hr0 : ∀ i, 0 ≤ r i) (hx : ∀ i, |x i| ≤ r i) :
    |MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p| ≤ mvPolynomialBoxBound p r := by
  rw [MvPolynomial.eval₂_eq']
  calc
    |∑ m ∈ p.support,
        (algebraMap ℚ ℝ) (p.coeff m) * ∏ i : Fin n, x i ^ m i|
        ≤ ∑ m ∈ p.support,
          |(algebraMap ℚ ℝ) (p.coeff m) * ∏ i : Fin n, x i ^ m i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ mvPolynomialBoxBound p r := by
      dsimp [mvPolynomialBoxBound]
      refine Finset.sum_le_sum ?_
      intro m hm
      rw [abs_mul]
      change |((p.coeff m : ℚ) : ℝ)| * |∏ i : Fin n, x i ^ m i| ≤
        |((p.coeff m : ℚ) : ℝ)| * ∏ i : Fin n, r i ^ m i
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [Finset.abs_prod]
      refine Finset.prod_le_prod ?_ ?_
      · intro i hi
        exact abs_nonneg _
      · intro i hi
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _

private theorem eval_selRenameZ_abs_le_boxBound
    {d : ℕ} {V : Type} [Fintype V]
    (p : MvPolynomial (Fin d) ℚ) (y : Fin (selectorDim d V) → ℝ)
    {r : Fin d → ℝ} (hr0 : ∀ i, 0 ≤ r i)
    (hz : ∀ i, |y (selZ V i)| ≤ r i) :
    |MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selRenameZ V p)| ≤
      mvPolynomialBoxBound p r := by
  rw [selRenameZ, MvPolynomial.eval₂_rename]
  exact mvPolynomial_eval₂_abs_le_boxBound p hr0 hz

/-- Explicit version of `selector_mix_affine_bound`, with constants independent
of the particular trajectory and horizon. -/
private theorem selector_replicator_mix_affine_bound_explicit
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hBpos : 0 < B)
    (hLam01 : ∀ v : V, ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ yt t (selLamCoord v) ∧ yt t (selLamCoord v) ≤ 1) :
    ∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selectorMixField branch i)| ≤
      selectorReplicatorMixConst branch + selectorReplicatorMixSlope branch *
        |yt t (selU V i)| := by
  classical
  intro i t ht
  have heval :
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
          (selectorMixField branch i) =
        ∑ v : V, yt t (selLamCoord v) *
          BranchData.evalBranch (branch v)
            (fun j => yt t (selU V j)) i := by
    rw [selectorMixField, eval₂_selectorMixFieldPoly]
  have hterm : ∀ v : V,
      |yt t (selLamCoord v) *
        BranchData.evalBranch (branch v) (fun j => yt t (selU V j)) i| ≤
      |BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) i| +
        BranchAction.multiplier B ((branch v).action i) *
          |yt t (selU V i)| := by
    intro v
    let a := BranchData.evalBranch (branch v) (fun j => yt t (selU V j)) i
    let b := BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) i
    let m := BranchAction.multiplier B ((branch v).action i)
    have hm_nonneg : 0 ≤ m := by
      simpa [m, BranchAction.multiplier] using
        abs_nonneg (((branch v).action i).scale : ℝ)
    have hlam : |yt t (selLamCoord v)| ≤ 1 := by
      rw [abs_of_nonneg (hLam01 v t ht).1]
      exact (hLam01 v t ht).2
    have hlip : |a - b| ≤ m * |yt t (selU V i)| := by
      simpa [a, b, m] using
        BranchData.coord_lipschitz hBpos (branch v)
          (fun j => yt t (selU V j)) (fun _ => (0 : ℝ)) i
    have hbranch : |a| ≤ |b| + m * |yt t (selU V i)| := by
      calc
        |a| = |(a - b) + b| := by congr 1; ring
        _ ≤ |a - b| + |b| := abs_add_le _ _
        _ ≤ m * |yt t (selU V i)| + |b| := by linarith [hlip]
        _ = |b| + m * |yt t (selU V i)| := by ring
    calc
      |yt t (selLamCoord v) * a| =
          |yt t (selLamCoord v)| * |a| := abs_mul _ _
      _ ≤ 1 * (|b| + m * |yt t (selU V i)|) :=
        mul_le_mul hlam hbranch (abs_nonneg _) zero_le_one
      _ = |b| + m * |yt t (selU V i)| := by ring
  have hsum :
      |∑ v : V, yt t (selLamCoord v) *
          BranchData.evalBranch (branch v)
            (fun j => yt t (selU V j)) i| ≤
      (∑ v : V, |BranchData.evalBranch (branch v)
          (fun _ => (0 : ℝ)) i|) +
        (∑ v : V, BranchAction.multiplier B ((branch v).action i)) *
          |yt t (selU V i)| := by
    calc
      |∑ v : V, yt t (selLamCoord v) *
          BranchData.evalBranch (branch v)
            (fun j => yt t (selU V j)) i|
          ≤ ∑ v : V, |yt t (selLamCoord v) *
              BranchData.evalBranch (branch v)
                (fun j => yt t (selU V j)) i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v : V, (|BranchData.evalBranch (branch v)
              (fun _ => (0 : ℝ)) i| +
            BranchAction.multiplier B ((branch v).action i) *
              |yt t (selU V i)|) :=
            Finset.sum_le_sum (fun v _ => hterm v)
      _ = (∑ v : V, |BranchData.evalBranch (branch v)
              (fun _ => (0 : ℝ)) i|) +
            (∑ v : V, BranchAction.multiplier B ((branch v).action i)) *
              |yt t (selU V i)| := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
  have hCcoord :
      (∑ v : V, |BranchData.evalBranch (branch v)
          (fun _ => (0 : ℝ)) i|) ≤ selectorReplicatorMixConst branch := by
    dsimp [selectorReplicatorMixConst]
    exact Finset.sum_le_sum (fun v _ =>
      Finset.single_le_sum
        (fun j _ => abs_nonneg
          (BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) j))
        (Finset.mem_univ i))
  have hKcoord :
      (∑ v : V, BranchAction.multiplier B ((branch v).action i)) ≤
        selectorReplicatorMixSlope branch := by
    dsimp [selectorReplicatorMixSlope]
    exact Finset.sum_le_sum (fun v _ =>
      Finset.single_le_sum
        (f := fun j => BranchAction.multiplier B ((branch v).action j))
        (fun j _ => abs_nonneg _)
        (Finset.mem_univ i))
  calc
    |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selectorMixField branch i)|
        = |∑ v : V, yt t (selLamCoord v) *
            BranchData.evalBranch (branch v)
              (fun j => yt t (selU V j)) i| := by rw [heval]
    _ ≤ (∑ v : V, |BranchData.evalBranch (branch v)
          (fun _ => (0 : ℝ)) i|) +
        (∑ v : V, BranchAction.multiplier B ((branch v).action i)) *
          |yt t (selU V i)| := hsum
    _ ≤ selectorReplicatorMixConst branch + selectorReplicatorMixSlope branch *
          |yt t (selU V i)| :=
      add_le_add hCcoord
        (mul_le_mul_of_nonneg_right hKcoord (abs_nonneg _))


private theorem repl_selRenameZ_abs_bound_from_selfcontained
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T Cbd Cmix kmix : ℝ}
    (hT : 0 < T)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        (yt t)) t)
    (hCbd : 0 ≤ Cbd) (hCmix : 0 ≤ Cmix) (hkmix : 0 ≤ kmix)
    (hCoefZ : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd)
    (hCoefU : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd)
    (hMixAff : ∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selectorMixField branch i)| ≤ Cmix + kmix * |yt t (selU V i)|) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRenameZ V HP)| ≤
        mvPolynomialBoxBound HP (fun i : Fin d =>
          gronwallBound ‖(yt 0 (selZ V i), yt 0 (selU V i))‖
            (Cbd * (2 + kmix)) (Cbd * Cmix) T) := by
  intro t ht
  refine eval_selRenameZ_abs_le_boxBound HP (yt t) ?_ ?_
  · intro i
    exact gronwallBound_nonneg_of_nonneg (norm_nonneg _)
      (mul_nonneg hCbd hCmix) (le_of_lt hT)
  · intro i
    exact (repl_zu_coord_abs_bound_selfcontained (branch := branch)
      (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
      (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
      (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      i (yt := yt) (T := T) (Cbd := Cbd) (Cmix := Cmix) (kmix := kmix)
      hderiv hCbd hCmix hkmix hCoefZ hCoefU (hMixAff i) t ht).1


private def selectorReplicatorAprioriBnd
    {d : ℕ} {V : Type} [Fintype V]
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (cμq cαq : ℚ) (L : ℕ) (Cbd Mbd Gbd Abd : ℝ → ℝ) : ℝ → ℝ := by
  classical
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  exact fun τ =>
    let scBd : ℝ :=
      Real.sqrt (y0 (selOfContract V (contractS d)) ^ 2 +
        y0 (selOfContract V (contractC d)) ^ 2)
    let muBd : ℝ :=
      |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * τ
    let alphaBd : ℝ :=
      |y0 (selOfContract V (contractAlpha d))| * Real.exp (|(cαq : ℝ)| * τ)
    let gateZBd : ℝ :=
      |y0 (selOfContract V (contractGateZ d))| *
        Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * τ)
    let gateUBd : ℝ :=
      |y0 (selOfContract V (contractGateU d))| *
        Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * τ)
    let zuBd : ℝ :=
      ∑ i : Fin d,
        gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
          (2 * Cbd τ) (Cbd τ * Mbd τ) τ
    let GBd : ℝ := |y0 (selGCoord d V)| + Gbd τ * τ
    let warmGainBd : ℝ := |y0 (selWarmGainCoord d V)|
    max 1 (max scBd (max muBd (max alphaBd
      (max gateZBd (max gateUBd (max zuBd (max GBd (max warmGainBd (Abd τ)))))))))

set_option maxHeartbeats 2000000

/-- Specific version of the coordinatewise selector a-priori bound, using the
explicit shared max-fold bound `selectorReplicatorAprioriBnd`. -/
theorem selector_replicator_coordwise_bound_specific
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    {T : ℝ} (Cbd Mbd Gbd Abd : ℝ → ℝ) (hT : 0 < T)
    (hCbdmono : Monotone Cbd) (hMbdmono : Monotone Mbd)
    (hGbdmono : Monotone Gbd) (hAbdmono : Monotone Abd)
    (hCbd0 : ∀ τ : ℝ, 0 ≤ Cbd τ) (hMbd0 : ∀ τ : ℝ, 0 ≤ Mbd τ)
    (hGbd0 : ∀ τ : ℝ, 0 ≤ Gbd τ) (hAbd0 : ∀ τ : ℝ, 0 ≤ Abd τ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ)
    (hyt0 : yt 0 = (fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hSelRP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)| ≤ 1)
    (hSelRPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)| ≤ (L : ℝ))
    (hSelQP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)| ≤ 1)
    (hSelQPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)| ≤ (L : ℝ))
    (hCoefZ : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd T)
    (hCoefU : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd T)
    (hMix : ∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selectorMixField branch i)| ≤ Mbd T)
    (hChiGain : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd T)
    (hCr : ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hA : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractA d))| ≤ Abd T) :
    let Bnd := selectorReplicatorAprioriBnd (V := V) x₀ w warmGainInit cμq cαq L Cbd Mbd Gbd Abd
    (∀ T' : ℝ, 0 < T' → 0 < Bnd T') ∧
    (∀ ⦃S T' : ℝ⦄, 0 < S → S ≤ T' → Bnd S ≤ Bnd T') ∧
    ∀ t ∈ Ico (0 : ℝ) T, ∀ i, |yt t i| ≤ Bnd T := by
  classical
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  let scBd : ℝ :=
    Real.sqrt (y0 (selOfContract V (contractS d)) ^ 2 +
      y0 (selOfContract V (contractC d)) ^ 2)
  let muBd : ℝ → ℝ := fun τ =>
    |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * τ
  let alphaBd : ℝ → ℝ := fun τ =>
    |y0 (selOfContract V (contractAlpha d))| * Real.exp (|(cαq : ℝ)| * τ)
  let gateZBd : ℝ → ℝ := fun τ =>
    |y0 (selOfContract V (contractGateZ d))| *
      Real.exp ((|(cμq : ℝ)| + muBd τ * (L : ℝ)) * τ)
  let gateUBd : ℝ → ℝ := fun τ =>
    |y0 (selOfContract V (contractGateU d))| *
      Real.exp ((|(cμq : ℝ)| + muBd τ * (L : ℝ)) * τ)
  let zuBd : ℝ → ℝ := fun τ =>
    (∑ i : Fin d,
      gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
        (2 * Cbd τ) (Cbd τ * Mbd τ) τ)
  let GBd : ℝ → ℝ := fun τ => |y0 (selGCoord d V)| + Gbd τ * τ
  let warmGainBd : ℝ := |y0 (selWarmGainCoord d V)|
  let Bnd : ℝ → ℝ := fun τ =>
    max 1 (max scBd (max (muBd τ) (max (alphaBd τ)
      (max (gateZBd τ) (max (gateUBd τ)
        (max (zuBd τ) (max (GBd τ) (max warmGainBd (Abd τ)))))))))
  change (∀ T' : ℝ, 0 < T' → 0 < Bnd T') ∧
    (∀ ⦃S T' : ℝ⦄, 0 < S → S ≤ T' → Bnd S ≤ Bnd T') ∧
    ∀ t ∈ Ico (0 : ℝ) T, ∀ i, |yt t i| ≤ Bnd T
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    exact lt_of_lt_of_le zero_lt_one (by dsimp [Bnd]; aesop)
  · intro S T' hS hST
    have hSnn : 0 ≤ S := le_of_lt hS
    have hTnn : 0 ≤ T' := le_trans hSnn hST
    have hmu : muBd S ≤ muBd T' := by dsimp [muBd]; gcongr
    have halpha : alphaBd S ≤ alphaBd T' := by
      dsimp [alphaBd]
      gcongr
    have hgateZ : gateZBd S ≤ gateZBd T' := by
      dsimp [gateZBd]
      gcongr
    have hgateU : gateUBd S ≤ gateUBd T' := by
      dsimp [gateUBd]
      gcongr
    have hzu : zuBd S ≤ zuBd T' := by
      dsimp [zuBd]
      refine Finset.sum_le_sum ?_
      intro i hi
      let δi : ℝ := ‖(y0 (selZ V i), y0 (selU V i))‖
      have hδ : 0 ≤ δi := norm_nonneg _
      have hKS : 0 ≤ 2 * Cbd S := mul_nonneg (by norm_num) (hCbd0 S)
      have hεS : 0 ≤ Cbd S * Mbd S := mul_nonneg (hCbd0 S) (hMbd0 S)
      have htime :
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) S ≤
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) T' :=
        gronwallBound_mono (δ := δi) (K := 2 * Cbd S)
          (ε := Cbd S * Mbd S) hδ hεS hKS hST
      have hKST : 2 * Cbd S ≤ 2 * Cbd T' :=
        mul_le_mul_of_nonneg_left (hCbdmono hST) (by norm_num)
      have hKstep :
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) T' ≤
          gronwallBound δi (2 * Cbd T') (Cbd S * Mbd S) T' :=
        gronwallBound_mono_K (δ := δi) (ε := Cbd S * Mbd S)
          (x := T') hδ hεS hTnn hKST
      have hεST : Cbd S * Mbd S ≤ Cbd T' * Mbd T' :=
        mul_le_mul (hCbdmono hST) (hMbdmono hST) (hMbd0 S) (hCbd0 T')
      have hεstep :
          gronwallBound δi (2 * Cbd T') (Cbd S * Mbd S) T' ≤
          gronwallBound δi (2 * Cbd T') (Cbd T' * Mbd T') T' :=
        gronwallBound_mono_epsilon (δ := δi) (K := 2 * Cbd T')
          (x := T') hTnn hεST
      exact htime.trans (hKstep.trans hεstep)
    have hG : GBd S ≤ GBd T' := by
      dsimp [GBd]
      have hprod : Gbd S * S ≤ Gbd T' * T' :=
        mul_le_mul (hGbdmono hST) hST hSnn (hGbd0 T')
      linarith
    have hAbd : Abd S ≤ Abd T' := hAbdmono hST
    dsimp [Bnd]
    gcongr
  · intro t ht i
    have hyt0' : yt 0 = y0 := by simpa [y0] using hyt0
    have htoB {x : ℝ} (hx : x ≤ Bnd T) : x ≤ Bnd T := hx
    have hone_to_B : (1 : ℝ) ≤ Bnd T := by
      dsimp [Bnd]
      exact le_max_left _ _
    have hsc_to_B : scBd ≤ Bnd T := by
      dsimp [Bnd]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hmu_to_B : muBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        muBd T ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))) :=
          le_max_left _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))))) :=
          le_max_right _ _
    have halpha_to_B : alphaBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        alphaBd T ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))) :=
          le_max_left _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))))) :=
          le_max_right _ _
    have hgateZ_to_B : gateZBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        gateZBd T ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))) :=
          le_max_left _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))))) :=
          le_max_right _ _
    have hgateU_to_B : gateUBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        gateUBd T ≤ max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))) :=
          le_max_left _ _
        _ ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))) :=
          le_max_right _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))))) :=
          le_max_right _ _
    have hzu_to_B : zuBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        zuBd T ≤ max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))) := le_max_left _ _
        _ ≤ max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))) :=
          le_max_right _ _
        _ ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))) :=
          le_max_right _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))))) :=
          le_max_right _ _
    have hG_to_B : GBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        GBd T ≤ max (GBd T) (max warmGainBd (Abd T)) := le_max_left _ _
        _ ≤ max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))) := le_max_right _ _
        _ ≤ max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))) :=
          le_max_right _ _
        _ ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))) :=
          le_max_right _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))))) :=
          le_max_right _ _
    have hwarmGain_to_B : warmGainBd ≤ Bnd T := by
      dsimp [Bnd]
      calc
        warmGainBd ≤ max warmGainBd (Abd T) := le_max_left _ _
        _ ≤ max (GBd T) (max warmGainBd (Abd T)) := le_max_right _ _
        _ ≤ max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))) := le_max_right _ _
        _ ≤ max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))) :=
          le_max_right _ _
        _ ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))) :=
          le_max_right _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))))) :=
          le_max_right _ _
    have hA_to_B : Abd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        Abd T ≤ max warmGainBd (Abd T) := le_max_right _ _
        _ ≤ max (GBd T) (max warmGainBd (Abd T)) := le_max_right _ _
        _ ≤ max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))) := le_max_right _ _
        _ ≤ max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))) :=
          le_max_right _ _
        _ ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))) :=
          le_max_right _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmGainBd (Abd T))))))))) :=
          le_max_right _ _
    refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ i
    · intro j
      refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ j
      · intro a
        fin_cases a
        · have hsc := repl_sc_conservation (branch := branch) (chiResetP := chiResetP)
            (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
            (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
            (cμq := cμq) (cαq := cαq) (L := L) (R := R)
            (yt := yt) (T := T) hderiv t ht
          have hs : |yt t (selOfContract V (contractS d))| ≤ scBd := by
            have hsq : (yt t (selOfContract V (contractS d))) ^ 2 ≤ scBd ^ 2 := by
              have hnn : 0 ≤ y0 (selOfContract V (contractS d)) ^ 2 +
                  y0 (selOfContract V (contractC d)) ^ 2 := by positivity
              dsimp [scBd]
              rw [Real.sq_sqrt hnn]
              rw [hyt0'] at hsc
              nlinarith [sq_nonneg (yt t (selOfContract V (contractC d)))]
            exact abs_le_of_sq_le_sq hsq (by positivity)
          exact hs.trans hsc_to_B
        · have hsc := repl_sc_conservation (branch := branch) (chiResetP := chiResetP)
            (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
            (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
            (cμq := cμq) (cαq := cαq) (L := L) (R := R)
            (yt := yt) (T := T) hderiv t ht
          have hc : |yt t (selOfContract V (contractC d))| ≤ scBd := by
            have hsq : (yt t (selOfContract V (contractC d))) ^ 2 ≤ scBd ^ 2 := by
              have hnn : 0 ≤ y0 (selOfContract V (contractS d)) ^ 2 +
                  y0 (selOfContract V (contractC d)) ^ 2 := by positivity
              dsimp [scBd]
              rw [Real.sq_sqrt hnn]
              rw [hyt0'] at hsc
              nlinarith [sq_nonneg (yt t (selOfContract V (contractS d)))]
            exact abs_le_of_sq_le_sq hsq (by positivity)
          exact hc.trans hsc_to_B
        · change |yt t (selOfContract V (contractMu d))| ≤ Bnd T
          rw [repl_mu_coord_affine (branch := branch) (chiResetP := chiResetP)
            (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
            (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
            (cμq := cμq) (cαq := cαq) (L := L) (R := R)
            (yt := yt) (T := T) hderiv t ht]
          rw [hyt0']
          have hle : |y0 (selOfContract V (contractMu d)) + (cμq : ℝ) * t| ≤
              muBd T := by
            have h1 := abs_add_le (y0 (selOfContract V (contractMu d))) ((cμq : ℝ) * t)
            rw [abs_mul, abs_of_nonneg ht.1] at h1
            have h2 : |(cμq : ℝ)| * t ≤ |(cμq : ℝ)| * T :=
              mul_le_mul_of_nonneg_left (le_of_lt ht.2) (abs_nonneg _)
            dsimp [muBd]
            linarith
          exact hle.trans hmu_to_B
        · change |yt t (selOfContract V (contractAlpha d))| ≤ Bnd T
          rw [repl_alpha_coord_eq (branch := branch) (chiResetP := chiResetP)
            (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
            (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
            (cμq := cμq) (cαq := cαq) (L := L) (R := R)
            (yt := yt) (T := T) hderiv t ht]
          rw [hyt0']
          have hle : |y0 (selOfContract V (contractAlpha d)) *
              Real.exp ((cαq : ℝ) * t)| ≤ alphaBd T := by
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            dsimp [alphaBd]
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr
              ((mul_le_mul_of_nonneg_right (le_abs_self _) ht.1).trans
                (mul_le_mul_of_nonneg_left (le_of_lt ht.2) (abs_nonneg _))))
              (abs_nonneg _)
          exact hle.trans halpha_to_B
      · intro b
        refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ b
        · intro g
          fin_cases g
          · have hb := repl_gateZ_coord_abs_bound (branch := branch)
              (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
              (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
              (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
              (yt := yt) (T := T) hderiv hSelRP hSelRPderiv t ht
            rw [hyt0'] at hb
            exact hb.trans hgateZ_to_B
          · have hb := repl_gateU_coord_abs_bound (branch := branch)
              (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
              (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
              (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
              (yt := yt) (T := T) hderiv hSelQP hSelQPderiv t ht
            rw [hyt0'] at hb
            exact hb.trans hgateU_to_B
        · intro r
          refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ r
          · intro z
            have hz := (repl_zu_coord_abs_bound (branch := branch)
              (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
              (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
              (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
              z (yt := yt) (T := T) (Cbd := Cbd T) (Mbd := Mbd T) hderiv
              (hCbd0 T) (hMbd0 T) (fun s hs => ⟨hCoefZ s hs, hCoefU s hs⟩)
              (hMix z) t ht).1
            rw [hyt0'] at hz
            have hsum : gronwallBound ‖(y0 (selZ V z), y0 (selU V z))‖
                (2 * Cbd T) (Cbd T * Mbd T) T ≤ zuBd T := by
              dsimp [zuBd]
              refine Finset.single_le_sum
                (f := fun i : Fin d =>
                  gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
                    (2 * Cbd T) (Cbd T * Mbd T) T)
                ?_ (Finset.mem_univ z)
              intro i hi
              have hK : 0 ≤ 2 * Cbd T := mul_nonneg (by norm_num) (hCbd0 T)
              have hε : 0 ≤ Cbd T * Mbd T := mul_nonneg (hCbd0 T) (hMbd0 T)
              have hδ : 0 ≤ ‖(y0 (selZ V i), y0 (selU V i))‖ := norm_nonneg _
              have h0T := (gronwallBound_mono
                (δ := ‖(y0 (selZ V i), y0 (selU V i))‖)
                (K := 2 * Cbd T) (ε := Cbd T * Mbd T) hδ hε hK
                (le_of_lt hT))
              rw [gronwallBound_x0] at h0T
              exact hδ.trans h0T
            exact hz.trans (hsum.trans hzu_to_B)
          · intro s
            refine Fin.addCases (m := d) (n := 1) ?_ ?_ s
            · intro u
              have hu := (repl_zu_coord_abs_bound (branch := branch)
                (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
                (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
                (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
                u (yt := yt) (T := T) (Cbd := Cbd T) (Mbd := Mbd T) hderiv
                (hCbd0 T) (hMbd0 T) (fun s hs => ⟨hCoefZ s hs, hCoefU s hs⟩)
                (hMix u) t ht).2
              rw [hyt0'] at hu
              have hsum : gronwallBound ‖(y0 (selZ V u), y0 (selU V u))‖
                  (2 * Cbd T) (Cbd T * Mbd T) T ≤ zuBd T := by
                dsimp [zuBd]
                refine Finset.single_le_sum
                  (f := fun i : Fin d =>
                    gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
                      (2 * Cbd T) (Cbd T * Mbd T) T)
                  ?_ (Finset.mem_univ u)
                intro i hi
                have hK : 0 ≤ 2 * Cbd T := mul_nonneg (by norm_num) (hCbd0 T)
                have hε : 0 ≤ Cbd T * Mbd T := mul_nonneg (hCbd0 T) (hMbd0 T)
                have hδ : 0 ≤ ‖(y0 (selZ V i), y0 (selU V i))‖ := norm_nonneg _
                have h0T := (gronwallBound_mono
                  (δ := ‖(y0 (selZ V i), y0 (selU V i))‖)
                  (K := 2 * Cbd T) (ε := Cbd T * Mbd T) hδ hε hK
                  (le_of_lt hT))
                rw [gronwallBound_x0] at h0T
                exact hδ.trans h0T
              exact hu.trans (hsum.trans hzu_to_B)
            · intro a1
              fin_cases a1
              exact (hA t ht).trans hA_to_B
    · intro k
      refine Fin.addCases (m := Fintype.card V) (n := 2) ?_ ?_ k
      · intro v
        let v' : V := (Fintype.equivFin V).symm v
        letI : Nonempty V := ⟨v'⟩
        have hlam0 : ∀ u : V, 0 ≤ yt 0 (selLamCoord u) := by
          intro u
          rw [hyt0]
          simp [selectorReplicatorEuclInitQ, selLamCoord]
        have hsum0 : (∑ u : V, yt 0 (selLamCoord u)) = 1 := by
          rw [hyt0]
          simpa using selectorReplicatorEuclInitQ_lam_sum (d := d) (V := V) x₀ w warmGainInit
        have hlow :=
          replicator_lam_coord_nonneg_on_prefix branch chiResetP chiGateP kappaP gainP
            PpolyP HP Aq Kq cμq cαq L R yt v' (hlam0 v') hCr hderiv t ht
        have hup :=
          replicator_lam_coord_le_one_on_prefix branch chiResetP chiGateP kappaP gainP
            PpolyP HP Aq Kq cμq cαq L R yt v' hlam0 hsum0 hCr hderiv t ht
        have hlam : |yt t (selLamCoord v')| ≤ 1 := abs_le.mpr ⟨by linarith, hup⟩
        simpa [selLamCoord, v'] using hlam.trans hone_to_B
      · intro g
        fin_cases g
        have hG := repl_G_coord_abs_bound (branch := branch) (chiResetP := chiResetP)
          (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
          (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
          (cμq := cμq) (cαq := cαq) (L := L) (R := R)
          (yt := yt) (T := T) (Gbd := Gbd T) hderiv (hGbd0 T) hChiGain t ht
        rw [hyt0'] at hG
        exact hG.trans hG_to_B
        · change |yt t (selWarmGainCoord d V)| ≤ Bnd T
          have hconst := repl_warmGain_coord_eq (branch := branch)
            (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
            (gainP := gainP) (PpolyP := PpolyP) (HP := HP)
            (Aq := Aq) (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
            (yt := yt) (T := T) hderiv t ht
          rw [hconst, hyt0']
          exact hwarmGain_to_B

/-- Genuine coordinatewise selector a-priori bound, proved by decomposing the
selector coordinate layout and dispatching each leaf to the corresponding
per-coordinate scalar bound. -/
theorem selector_replicator_coordwise_bound
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    {T : ℝ} (Cbd Mbd Gbd Abd : ℝ → ℝ) (hT : 0 < T)
    (hCbdmono : Monotone Cbd) (hMbdmono : Monotone Mbd)
    (hGbdmono : Monotone Gbd) (hAbdmono : Monotone Abd)
    (hCbd0 : ∀ τ : ℝ, 0 ≤ Cbd τ) (hMbd0 : ∀ τ : ℝ, 0 ≤ Mbd τ)
    (hGbd0 : ∀ τ : ℝ, 0 ≤ Gbd τ) (hAbd0 : ∀ τ : ℝ, 0 ≤ Abd τ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ)
    (hyt0 : yt 0 = (fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hSelRP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)| ≤ 1)
    (hSelRPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)| ≤ (L : ℝ))
    (hSelQP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)| ≤ 1)
    (hSelQPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)| ≤ (L : ℝ))
    (hCoefZ : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd T)
    (hCoefU : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd T)
    (hMix : ∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selectorMixField branch i)| ≤ Mbd T)
    (hChiGain : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd T)
    (hCr : ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hA : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractA d))| ≤ Abd T) :
    ∃ Bnd : ℝ → ℝ,
      (∀ T' : ℝ, 0 < T' → 0 < Bnd T') ∧
      (∀ ⦃S T' : ℝ⦄, 0 < S → S ≤ T' → Bnd S ≤ Bnd T') ∧
      ∀ t ∈ Ico (0 : ℝ) T, ∀ i, |yt t i| ≤ Bnd T := by
  refine ⟨selectorReplicatorAprioriBnd (V := V) x₀ w warmGainInit cμq cαq L Cbd Mbd Gbd Abd, ?_⟩
  simpa using
    selector_replicator_coordwise_bound_specific branch chiResetP chiGateP kappaP gainP
      PpolyP HP Aq Kq cμq cαq L R x₀ w warmGainInit Cbd Mbd Gbd Abd hT
      hCbdmono hMbdmono hGbdmono hAbdmono hCbd0 hMbd0 hGbd0 hAbd0
      yt hyt0 hderiv hSelRP hSelRPderiv hSelQP hSelQPderiv hCoefZ hCoefU
      hMix hChiGain hCr hA

/-- A prefix-uniform finite-horizon selector bound from the structural
per-coordinate hypotheses, packaged into Ripple's `FiniteHorizonBound`. -/
theorem selector_replicator_finiteHorizonBound
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (Cbd Mbd Gbd Abd : ℝ → ℝ)
    (hCbdmono : Monotone Cbd) (hMbdmono : Monotone Mbd)
    (hGbdmono : Monotone Gbd) (hAbdmono : Monotone Abd)
    (hCbd0 : ∀ τ : ℝ, 0 ≤ Cbd τ) (hMbd0 : ∀ τ : ℝ, 0 ≤ Mbd τ)
    (hGbd0 : ∀ τ : ℝ, 0 ≤ Gbd τ) (hAbd0 : ∀ τ : ℝ, 0 ≤ Abd τ)
    (hstruct : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorReplicatorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)| ≤ 1) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)| ≤ (L : ℝ)) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)| ≤ 1) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)| ≤ (L : ℝ)) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
            yt t (selOfContract V (contractGateZ d))| ≤ Cbd T) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
            yt t (selOfContract V (contractGateU d))| ≤ Cbd T) ∧
        (∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selectorMixField branch i)| ≤ Mbd T) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd T) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |yt t (selOfContract V (contractA d))| ≤ Abd T)) :
    Ripple.FiniteHorizonBound
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
      (fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) := by
  let Bnd : ℝ → ℝ :=
    selectorReplicatorAprioriBnd (V := V) x₀ w warmGainInit cμq cαq L Cbd Mbd Gbd Abd
  have hBpos : ∀ T : ℝ, 0 < T → 0 < Bnd T := by
    intro T hT
    dsimp [Bnd, selectorReplicatorAprioriBnd]
    exact lt_of_lt_of_le zero_lt_one (by aesop)
  have hBmono : ∀ ⦃S T : ℝ⦄, 0 < S → S ≤ T → Bnd S ≤ Bnd T := by
    intro S T hS hST
    have hSnn : 0 ≤ S := le_of_lt hS
    have hTnn : 0 ≤ T := le_trans hSnn hST
    have hGprod : Gbd S * S ≤ Gbd T * T :=
      mul_le_mul (hGbdmono hST) hST hSnn (hGbd0 T)
    have hAbdST : Abd S ≤ Abd T := hAbdmono hST
    dsimp [Bnd, selectorReplicatorAprioriBnd]
    gcongr
    · rename_i i hi
      let δi : ℝ :=
        max ‖((selectorReplicatorEuclInitQ d V x₀ w warmGainInit (selZ V i) : ℚ) : ℝ)‖
          ‖((selectorReplicatorEuclInitQ d V x₀ w warmGainInit (selU V i) : ℚ) : ℝ)‖
      have hδ : 0 ≤ δi := by
        dsimp [δi]
        exact le_trans (norm_nonneg _) (le_max_left _ _)
      have hKS : 0 ≤ 2 * Cbd S := mul_nonneg (by norm_num) (hCbd0 S)
      have hεS : 0 ≤ Cbd S * Mbd S := mul_nonneg (hCbd0 S) (hMbd0 S)
      have htime :
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) S ≤
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) T :=
        gronwallBound_mono (δ := δi) (K := 2 * Cbd S)
          (ε := Cbd S * Mbd S) hδ hεS hKS hST
      have hKST : 2 * Cbd S ≤ 2 * Cbd T :=
        mul_le_mul_of_nonneg_left (hCbdmono hST) (by norm_num)
      have hKstep :
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) T ≤
          gronwallBound δi (2 * Cbd T) (Cbd S * Mbd S) T :=
        gronwallBound_mono_K (δ := δi) (ε := Cbd S * Mbd S)
          (x := T) hδ hεS hTnn hKST
      have hεST : Cbd S * Mbd S ≤ Cbd T * Mbd T :=
        mul_le_mul (hCbdmono hST) (hMbdmono hST) (hMbd0 S) (hCbd0 T)
      have hεstep :
          gronwallBound δi (2 * Cbd T) (Cbd S * Mbd S) T ≤
          gronwallBound δi (2 * Cbd T) (Cbd T * Mbd T) T :=
        gronwallBound_mono_epsilon (δ := δi) (K := 2 * Cbd T)
          (x := T) hTnn hεST
      exact htime.trans (hKstep.trans hεstep)
  refine Ripple.finiteHorizonBound_of_monotone_bound
    (f := selectorReplicatorAssembledVectorField d B V branch
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
    (y₀ := fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ))
    Bnd hBpos ?_ ?_
  · intro S T hS hST
    exact hBmono hS hST
  · intro T hT yt hyt0 hderiv t ht
    obtain ⟨hSelRP, hSelRPderiv, hSelQP, hSelQPderiv,
      hCoefZ, hCoefU, hMix, hChiGain, hCr, hA⟩ :=
      hstruct T hT yt hyt0 hderiv
    have hspec := selector_replicator_coordwise_bound_specific
      (branch := branch) (chiResetP := chiResetP) (chiGateP := chiGateP)
      (kappaP := kappaP) (gainP := gainP) (PpolyP := PpolyP) (HP := HP)
      (Aq := Aq) (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (x₀ := x₀) (w := w) (warmGainInit := warmGainInit) (T := T) (Cbd := Cbd) (Mbd := Mbd)
      (Gbd := Gbd) (Abd := Abd) hT hCbdmono hMbdmono hGbdmono hAbdmono
      hCbd0 hMbd0 hGbd0 hAbd0 yt hyt0 hderiv hSelRP hSelRPderiv
      hSelQP hSelQPderiv hCoefZ hCoefU hMix hChiGain hCr hA
    have hcoordT :
        ∀ t ∈ Ico (0 : ℝ) T, ∀ i, |yt t i| ≤ Bnd T := by
      simpa [Bnd] using hspec.2.2
    have _hexists :=
      selector_replicator_coordwise_bound branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R x₀ w warmGainInit Cbd Mbd Gbd Abd hT hCbdmono hMbdmono
        hGbdmono hAbdmono hCbd0 hMbd0 hGbd0 hAbd0 yt hyt0 hderiv hSelRP
        hSelRPderiv hSelQP hSelQPderiv hCoefZ hCoefU hMix hChiGain hCr
        hA
    rw [pi_norm_le_iff_of_nonneg (le_of_lt (hBpos T hT))]
    intro i
    simpa [Real.norm_eq_abs] using hcoordT t ht i



/-- Explicit gate-coefficient bound used by
`selector_replicator_finiteHorizonBound_v2`.  The `max 0 τ` clamp only makes the function
globally monotone; on positive horizons it is exactly the intended bound. -/
private def selectorReplicatorCoeffBdV2
    {d : ℕ} {V : Type} [Fintype V]
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ) (Aq cμq cαq : ℚ) (L : ℕ) :
    ℝ → ℝ := by
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  exact fun τ =>
    let θ : ℝ := max 0 τ
    let muBd : ℝ :=
      |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * θ
    let alphaBd : ℝ :=
      |y0 (selOfContract V (contractAlpha d))| *
        Real.exp (|(cαq : ℝ)| * θ)
    let gateBd : ℝ :=
      |y0 (selOfContract V (contractGateZ d))| *
        Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * θ)
    |(Aq : ℝ)| * alphaBd * gateBd

private def selectorReplicatorMixMbdV2
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ) (Aq cμq cαq : ℚ) (L : ℕ) :
    ℝ → ℝ := by
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  let Cmix : ℝ := selectorReplicatorMixConst branch
  let kmix : ℝ := selectorReplicatorMixSlope branch
  let Cbd : ℝ → ℝ := selectorReplicatorCoeffBdV2 (V := V) x₀ w warmGainInit Aq cμq cαq L
  exact fun τ =>
    let θ : ℝ := max 0 τ
    Cmix + kmix * ∑ i : Fin d,
      gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
        (Cbd τ * (2 + kmix)) (Cbd τ * Cmix) θ

/-- A priori barrier for the replicated contract `A` coordinate.  The continuity
input is only the interval continuity of the `A` coordinate, supplied for prefix
solutions by `derivOnIco_continuousOn`. -/
theorem repl_contractA_coord_abs_bound
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T Rbd : ℝ}
    (hT : 0 < T) (hKq0 : 0 ≤ (Kq : ℝ))
    (hAcont : ContinuousOn
      (fun s : ℝ => yt s (selOfContract V (contractA d))) (Ico (0 : ℝ) T))
    (hyt0 : yt 0 = (fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        (yt t)) t)
    (hRen : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRenameZ V HP)| ≤ Rbd) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractA d))| ≤
        max |yt 0 (selOfContract V (contractA d))| Rbd := by
  classical
  let Acoord := selOfContract V (contractA d)
  let Ccoord := selOfContract V (contractC d)
  let g : ℝ → ℝ := fun s => yt s Acoord
  let q : ℝ → ℝ :=
    fun s => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) (selRenameZ V HP)
  let gp : ℝ → ℝ := fun s =>
    (Kq : ℝ) * (((1 / 2 : ℝ) * (1 - yt s Ccoord)) ^ R) * (q s - g s)
  let b : ℝ := max |g 0| Rbd
  have hs0 : yt 0 (selOfContract V (contractS d)) = 0 := by
    rw [hyt0]
    simp [selectorReplicatorEuclInitQ, selOfContract, contractS]
  have hc0 : yt 0 (selOfContract V (contractC d)) = 1 := by
    rw [hyt0]
    simp [selectorReplicatorEuclInitQ, selOfContract, contractC]
  have hcoef0 : ∀ s ∈ Ico (0 : ℝ) T,
      0 ≤ (Kq : ℝ) * (((1 / 2 : ℝ) * (1 - yt s Ccoord)) ^ R) := by
    intro s hs
    have hsc := repl_sc_realize (branch := branch) (chiResetP := chiResetP)
      (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
      (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
      (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) hderiv hs0 hc0 s hs
    have hbase0 : 0 ≤ (1 / 2 : ℝ) * (1 - yt s Ccoord) := by
      dsimp [Ccoord]
      rw [hsc.2]
      nlinarith [Real.cos_le_one s]
    exact mul_nonneg hKq0 (pow_nonneg hbase0 R)
  have hg0ub : g 0 ≤ b := (abs_le.mp (le_max_left |g 0| Rbd)).2
  have hg0lb : -b ≤ g 0 := (abs_le.mp (le_max_left |g 0| Rbd)).1
  intro t ht
  have hIcc_subset : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hcont : ContinuousOn g (Icc (0 : ℝ) t) := by
    exact hAcont.mono hIcc_subset
  have hderivWithin :
      ∀ s ∈ Ico (0 : ℝ) t, HasDerivWithinAt g (gp s) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hpi := (hasDerivAt_pi.mp (hderiv s hsT)) Acoord
    rw [replAprioriField_A_eq] at hpi
    have hcoord : HasDerivAt g (gp s) s := by
      simpa [g, gp, q, Acoord, Ccoord] using hpi
    exact hcoord.hasDerivWithinAt
  have hupper := Ripple.scalar_upper_barrier_exterior_on_Icc
    (T := t) (b := b) ht.1 g gp hg0ub hcont hderivWithin
    (by
      intro s hs hbg
      have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
      have hqle : q s ≤ b :=
        (abs_le.mp (hRen s hsT)).2.trans (le_max_right |g 0| Rbd)
      have hdiff : q s - g s ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos (hcoef0 s hsT) hdiff)
  have hlower := Ripple.scalar_lower_barrier_exterior_on_Icc
    (T := t) (a := -b) ht.1 g gp hg0lb hcont hderivWithin
    (by
      intro s hs hgb
      have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
      have hqlo : -b ≤ q s := by
        have hq := (abs_le.mp (hRen s hsT)).1
        have hbR : Rbd ≤ b := le_max_right |g 0| Rbd
        linarith
      have hdiff : 0 ≤ q s - g s := by linarith
      exact mul_nonneg (hcoef0 s hsT) hdiff)
  have htIcc : t ∈ Icc (0 : ℝ) t := ⟨ht.1, le_rfl⟩
  exact abs_le.mpr ⟨by simpa [g, b, Acoord] using hlower t htIcc,
    by simpa [g, b, Acoord] using hupper t htIcc⟩

/-- Finite-horizon selector bound carrying only the realization/sign facts.
The coefficient and mixture boxes are built internally from the self-contained
scalar, affine-mixture, and `z/u` Grönwall tools. -/
theorem selector_replicator_finiteHorizonBound_v2
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (Gbd : ℝ → ℝ)
    (hBpos : 0 < B) (hKq0 : 0 ≤ (Kq : ℝ))
    (hGbdmono : Monotone Gbd)
    (hGbd0 : ∀ τ : ℝ, 0 ≤ Gbd τ)
    (hChiGain : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorReplicatorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd T)
    (hCr : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorReplicatorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP) :
    Ripple.FiniteHorizonBound
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
      (fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) := by
  classical
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  let Cbd : ℝ → ℝ := selectorReplicatorCoeffBdV2 (V := V) x₀ w warmGainInit Aq cμq cαq L
  let Mbd : ℝ → ℝ := selectorReplicatorMixMbdV2 branch x₀ w warmGainInit Aq cμq cαq L
  let Rbd : ℝ → ℝ := fun τ =>
    mvPolynomialBoxBound HP (fun i : Fin d =>
      gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
        (Cbd τ * (2 + selectorReplicatorMixSlope branch))
        (Cbd τ * selectorReplicatorMixConst branch) (max 0 τ))
  let Abd : ℝ → ℝ := fun τ =>
    max |y0 (selOfContract V (contractA d))| (Rbd τ)
  have hCmix0 : 0 ≤ selectorReplicatorMixConst branch := selectorReplicatorMixConst_nonneg branch
  have hkmix0 : 0 ≤ selectorReplicatorMixSlope branch := selectorReplicatorMixSlope_nonneg branch
  have hCbd0 : ∀ τ : ℝ, 0 ≤ Cbd τ := by
    intro τ
    dsimp [Cbd, selectorReplicatorCoeffBdV2]
    positivity
  have hCbdmono : Monotone Cbd := by
    intro S T hST
    let y0 : Fin (selectorDim d V) → ℝ :=
      fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
    let θS : ℝ := max (0 : ℝ) S
    let θT : ℝ := max (0 : ℝ) T
    let muBd : ℝ → ℝ :=
      fun θ => |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * θ
    let alphaBd : ℝ → ℝ :=
      fun θ => |y0 (selOfContract V (contractAlpha d))| *
        Real.exp (|(cαq : ℝ)| * θ)
    let gateBd : ℝ → ℝ :=
      fun θ => |y0 (selOfContract V (contractGateZ d))| *
        Real.exp ((|(cμq : ℝ)| + muBd θ * (L : ℝ)) * θ)
    have hθ : θS ≤ θT := by
      dsimp [θS, θT]
      exact max_le_max le_rfl hST
    have hθS0 : 0 ≤ θS := by dsimp [θS]; exact le_max_left _ _
    have hθT0 : 0 ≤ θT := by dsimp [θT]; exact le_max_left _ _
    have hmu : muBd θS ≤ muBd θT := by
      dsimp [muBd]
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hθ (abs_nonneg _)) _
    have hmuT0 : 0 ≤ muBd θT := by
      dsimp [muBd]
      exact add_nonneg (abs_nonneg _)
        (mul_nonneg (abs_nonneg _) hθT0)
    have halpha : alphaBd θS ≤ alphaBd θT := by
      dsimp [alphaBd]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hθ (abs_nonneg _)))
        (abs_nonneg _)
    have hgate : gateBd θS ≤ gateBd θT := by
      have hcoef :
          |(cμq : ℝ)| + muBd θS * (L : ℝ) ≤
          |(cμq : ℝ)| + muBd θT * (L : ℝ) := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)) _
      have harg :
          (|(cμq : ℝ)| + muBd θS * (L : ℝ)) * θS ≤
          (|(cμq : ℝ)| + muBd θT * (L : ℝ)) * θT := by
        have hcoefT0 :
            0 ≤ |(cμq : ℝ)| + muBd θT * (L : ℝ) :=
          add_nonneg (abs_nonneg _)
            (mul_nonneg hmuT0 (Nat.cast_nonneg _))
        exact mul_le_mul hcoef hθ hθS0 hcoefT0
      dsimp [gateBd]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr harg) (abs_nonneg _)
    dsimp [Cbd, selectorReplicatorCoeffBdV2]
    change |(Aq : ℝ)| * alphaBd θS * gateBd θS ≤
      |(Aq : ℝ)| * alphaBd θT * gateBd θT
    have hleft :
        |(Aq : ℝ)| * alphaBd θS ≤ |(Aq : ℝ)| * alphaBd θT :=
      mul_le_mul_of_nonneg_left halpha (abs_nonneg _)
    exact mul_le_mul hleft hgate (by positivity) (by positivity)
  have hMbd0 : ∀ τ : ℝ, 0 ≤ Mbd τ := by
    intro τ
    dsimp [Mbd, selectorReplicatorMixMbdV2]
    refine add_nonneg hCmix0 (mul_nonneg hkmix0 ?_)
    exact Finset.sum_nonneg (fun i _ =>
      gronwallBound_nonneg_of_nonneg (by positivity)
        (mul_nonneg (hCbd0 τ) hCmix0) (le_max_left _ _))
  have hMbdmono : Monotone Mbd := by
    intro S T hST
    let θS : ℝ := max 0 S
    let θT : ℝ := max 0 T
    have hθ : θS ≤ θT := by
      dsimp [θS, θT]
      exact max_le_max le_rfl hST
    have hθT0 : 0 ≤ θT := by dsimp [θT]; exact le_max_left _ _
    have hθS0 : 0 ≤ θS := by dsimp [θS]; exact le_max_left _ _
    have hCST : Cbd S ≤ Cbd T := hCbdmono hST
    dsimp [Mbd, selectorReplicatorMixMbdV2]
    refine add_le_add_right ?_ (selectorReplicatorMixConst branch)
    refine mul_le_mul_of_nonneg_left ?_ hkmix0
    refine Finset.sum_le_sum ?_
    intro i _hi
    let δi : ℝ :=
      max ‖selectorReplicatorEuclInitQ d V x₀ w warmGainInit (selZ V i)‖
        ‖selectorReplicatorEuclInitQ d V x₀ w warmGainInit (selU V i)‖
    have hδ : 0 ≤ δi := by
      dsimp [δi]
      positivity
    have hεS : 0 ≤ Cbd S * selectorReplicatorMixConst branch :=
      mul_nonneg (hCbd0 S) hCmix0
    have hKST :
        Cbd S * (2 + selectorReplicatorMixSlope branch) ≤
        Cbd T * (2 + selectorReplicatorMixSlope branch) := by
      exact mul_le_mul_of_nonneg_right hCST (by nlinarith)
    have hεST :
        Cbd S * selectorReplicatorMixConst branch ≤
        Cbd T * selectorReplicatorMixConst branch :=
      mul_le_mul_of_nonneg_right hCST hCmix0
    have htime :
        gronwallBound δi (Cbd S * (2 + selectorReplicatorMixSlope branch))
          (Cbd S * selectorReplicatorMixConst branch) θS ≤
        gronwallBound δi (Cbd S * (2 + selectorReplicatorMixSlope branch))
          (Cbd S * selectorReplicatorMixConst branch) θT := by
      have hK : 0 ≤ Cbd S * (2 + selectorReplicatorMixSlope branch) :=
        mul_nonneg (hCbd0 S) (by nlinarith)
      exact gronwallBound_mono (δ := δi)
        (K := Cbd S * (2 + selectorReplicatorMixSlope branch))
        (ε := Cbd S * selectorReplicatorMixConst branch) hδ hεS hK hθ
    have hKstep :
        gronwallBound δi (Cbd S * (2 + selectorReplicatorMixSlope branch))
          (Cbd S * selectorReplicatorMixConst branch) θT ≤
        gronwallBound δi (Cbd T * (2 + selectorReplicatorMixSlope branch))
          (Cbd S * selectorReplicatorMixConst branch) θT := by
      exact gronwallBound_mono_K (δ := δi)
        (ε := Cbd S * selectorReplicatorMixConst branch) (x := θT)
        hδ hεS hθT0 hKST
    have hεstep :
        gronwallBound δi (Cbd T * (2 + selectorReplicatorMixSlope branch))
          (Cbd S * selectorReplicatorMixConst branch) θT ≤
        gronwallBound δi (Cbd T * (2 + selectorReplicatorMixSlope branch))
          (Cbd T * selectorReplicatorMixConst branch) θT := by
      exact gronwallBound_mono_epsilon (δ := δi)
        (K := Cbd T * (2 + selectorReplicatorMixSlope branch)) (x := θT) hθT0 hεST
    exact htime.trans (hKstep.trans hεstep)
  have hRbd0 : ∀ τ : ℝ, 0 ≤ Rbd τ := by
    intro τ
    dsimp [Rbd]
    refine mvPolynomialBoxBound_nonneg HP ?_
    intro i
    exact gronwallBound_nonneg_of_nonneg ((abs_nonneg _).trans (le_max_left _ _))
      (mul_nonneg (hCbd0 τ) hCmix0) (le_max_left _ _)
  have hRbdmono : Monotone Rbd := by
    intro S T hST
    let θS : ℝ := max 0 S
    let θT : ℝ := max 0 T
    have hθ : θS ≤ θT := by
      dsimp [θS, θT]
      exact max_le_max le_rfl hST
    have hθT0 : 0 ≤ θT := by dsimp [θT]; exact le_max_left _ _
    have hθS0 : 0 ≤ θS := by dsimp [θS]; exact le_max_left _ _
    have hCST : Cbd S ≤ Cbd T := hCbdmono hST
    dsimp [Rbd]
    refine mvPolynomialBoxBound_mono HP ?_ ?_
    · intro i
      exact gronwallBound_nonneg_of_nonneg ((abs_nonneg _).trans (le_max_left _ _))
        (mul_nonneg (hCbd0 S) hCmix0) hθS0
    · intro i
      let δi : ℝ := ‖(y0 (selZ V i), y0 (selU V i))‖
      have hδ : 0 ≤ δi := norm_nonneg _
      have hεS : 0 ≤ Cbd S * selectorReplicatorMixConst branch :=
        mul_nonneg (hCbd0 S) hCmix0
      have hKST :
          Cbd S * (2 + selectorReplicatorMixSlope branch) ≤
          Cbd T * (2 + selectorReplicatorMixSlope branch) := by
        exact mul_le_mul_of_nonneg_right hCST (by nlinarith)
      have hεST :
          Cbd S * selectorReplicatorMixConst branch ≤
          Cbd T * selectorReplicatorMixConst branch :=
        mul_le_mul_of_nonneg_right hCST hCmix0
      have htime :
          gronwallBound δi (Cbd S * (2 + selectorReplicatorMixSlope branch))
            (Cbd S * selectorReplicatorMixConst branch) θS ≤
          gronwallBound δi (Cbd S * (2 + selectorReplicatorMixSlope branch))
            (Cbd S * selectorReplicatorMixConst branch) θT := by
        have hK : 0 ≤ Cbd S * (2 + selectorReplicatorMixSlope branch) :=
          mul_nonneg (hCbd0 S) (by nlinarith)
        exact gronwallBound_mono (δ := δi)
          (K := Cbd S * (2 + selectorReplicatorMixSlope branch))
          (ε := Cbd S * selectorReplicatorMixConst branch) hδ hεS hK hθ
      have hKstep :
          gronwallBound δi (Cbd S * (2 + selectorReplicatorMixSlope branch))
            (Cbd S * selectorReplicatorMixConst branch) θT ≤
          gronwallBound δi (Cbd T * (2 + selectorReplicatorMixSlope branch))
            (Cbd S * selectorReplicatorMixConst branch) θT := by
        exact gronwallBound_mono_K (δ := δi)
          (ε := Cbd S * selectorReplicatorMixConst branch) (x := θT)
          hδ hεS hθT0 hKST
      have hεstep :
          gronwallBound δi (Cbd T * (2 + selectorReplicatorMixSlope branch))
            (Cbd S * selectorReplicatorMixConst branch) θT ≤
          gronwallBound δi (Cbd T * (2 + selectorReplicatorMixSlope branch))
            (Cbd T * selectorReplicatorMixConst branch) θT := by
        exact gronwallBound_mono_epsilon (δ := δi)
          (K := Cbd T * (2 + selectorReplicatorMixSlope branch)) (x := θT) hθT0 hεST
      exact htime.trans (hKstep.trans hεstep)
  have hAbdmono : Monotone Abd := by
    intro S T hST
    dsimp [Abd]
    exact max_le_max le_rfl (hRbdmono hST)
  have hAbd0 : ∀ τ : ℝ, 0 ≤ Abd τ := by
    intro τ
    dsimp [Abd]
    exact le_trans (abs_nonneg _) (le_max_left _ _)
  refine selector_replicator_finiteHorizonBound branch chiResetP chiGateP kappaP gainP
    PpolyP HP Aq Kq cμq cαq L R x₀ w warmGainInit Cbd Mbd Gbd Abd
    hCbdmono hMbdmono hGbdmono hAbdmono hCbd0 hMbd0 hGbd0 hAbd0 ?_
  intro T hT yt hyt0 hderiv
  have hpulse := selector_replicator_pulse_bounds branch chiResetP chiGateP kappaP gainP
    PpolyP HP Aq Kq cμq cαq L R x₀ w warmGainInit yt hyt0 hderiv
  obtain ⟨hSelRP, hSelRPderiv, hSelQP, hSelQPderiv⟩ := hpulse
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  let muBd : ℝ :=
    |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T
  let alphaBd : ℝ :=
    |y0 (selOfContract V (contractAlpha d))| *
      Real.exp (|(cαq : ℝ)| * T)
  let gateZBd : ℝ :=
    |y0 (selOfContract V (contractGateZ d))| *
      Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * T)
  let gateUBd : ℝ :=
    |y0 (selOfContract V (contractGateU d))| *
      Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * T)
  have hyt0' : yt 0 = y0 := by simpa [y0] using hyt0
  have hθT : max 0 T = T := max_eq_right (le_of_lt hT)
  have halpha : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractAlpha d))| ≤ alphaBd := by
    intro t ht
    rw [repl_alpha_coord_eq (branch := branch) (chiResetP := chiResetP)
      (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
      (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
      (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) hderiv t ht]
    rw [hyt0']
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    dsimp [alphaBd]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        ((mul_le_mul_of_nonneg_right (le_abs_self _) ht.1).trans
          (mul_le_mul_of_nonneg_left (le_of_lt ht.2) (abs_nonneg _))))
      (abs_nonneg _)
  have hgateZ : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractGateZ d))| ≤ gateZBd := by
    intro t ht
    have hb := repl_gateZ_coord_abs_bound (branch := branch)
      (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
      (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
      (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) hderiv hSelRP hSelRPderiv t ht
    rw [hyt0'] at hb
    simpa [gateZBd, muBd] using hb
  have hgateU : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractGateU d))| ≤ gateUBd := by
    intro t ht
    have hb := repl_gateU_coord_abs_bound (branch := branch)
      (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
      (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
      (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) hderiv hSelQP hSelQPderiv t ht
    rw [hyt0'] at hb
    simpa [gateUBd, muBd] using hb
  have hgateU_le_Z : gateUBd ≤ gateZBd := by
    dsimp [gateUBd, gateZBd]
    have hinit :
        |y0 (selOfContract V (contractGateU d))| ≤
        |y0 (selOfContract V (contractGateZ d))| := by
      simp [y0, selectorReplicatorEuclInitQ, selOfContract, contractGateZ, contractGateU]
    exact mul_le_mul_of_nonneg_right hinit (le_of_lt (Real.exp_pos _))
  have hCbdChoice :
      |(Aq : ℝ)| * alphaBd * gateZBd = Cbd T := by
    dsimp [Cbd, selectorReplicatorCoeffBdV2, alphaBd, gateZBd, muBd]
    simp [hθT, y0]
  have hCoefZ : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd T := by
    intro t ht
    calc
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
          yt t (selOfContract V (contractGateZ d))|
          = |(Aq : ℝ)| * |yt t (selOfContract V (contractAlpha d))| *
            |yt t (selOfContract V (contractGateZ d))| := by
              rw [abs_mul, abs_mul]
      _ ≤ |(Aq : ℝ)| * alphaBd * gateZBd := by
        have hleft :
            |(Aq : ℝ)| * |yt t (selOfContract V (contractAlpha d))| ≤
            |(Aq : ℝ)| * alphaBd :=
          mul_le_mul_of_nonneg_left (halpha t ht) (abs_nonneg _)
        exact mul_le_mul hleft (hgateZ t ht)
          (abs_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
      _ = Cbd T := hCbdChoice
  have hCoefU : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd T := by
    intro t ht
    calc
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
          yt t (selOfContract V (contractGateU d))|
          = |(Aq : ℝ)| * |yt t (selOfContract V (contractAlpha d))| *
            |yt t (selOfContract V (contractGateU d))| := by
              rw [abs_mul, abs_mul]
      _ ≤ |(Aq : ℝ)| * alphaBd * gateUBd := by
        have hleft :
            |(Aq : ℝ)| * |yt t (selOfContract V (contractAlpha d))| ≤
            |(Aq : ℝ)| * alphaBd :=
          mul_le_mul_of_nonneg_left (halpha t ht) (abs_nonneg _)
        exact mul_le_mul hleft (hgateU t ht)
          (abs_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
      _ ≤ |(Aq : ℝ)| * alphaBd * gateZBd := by
        exact mul_le_mul_of_nonneg_left hgateU_le_Z
          (mul_nonneg (abs_nonneg _) (by positivity))
      _ = Cbd T := hCbdChoice
  have hLam01 : ∀ v : V, ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ yt t (selLamCoord v) ∧ yt t (selLamCoord v) ≤ 1 := by
    intro v t ht
    letI : Nonempty V := ⟨v⟩
    have hlam0 : ∀ u : V, 0 ≤ yt 0 (selLamCoord u) := by
      intro u
      rw [hyt0]
      simp [selectorReplicatorEuclInitQ, selLamCoord]
    have hsum0 : (∑ u : V, yt 0 (selLamCoord u)) = 1 := by
      rw [hyt0]
      simpa using selectorReplicatorEuclInitQ_lam_sum (d := d) (V := V) x₀ w warmGainInit
    exact
      ⟨replicator_lam_coord_nonneg_on_prefix branch chiResetP chiGateP kappaP gainP
          PpolyP HP Aq Kq cμq cαq L R yt v (hlam0 v)
          (hCr T hT yt hyt0 hderiv) hderiv t ht,
        replicator_lam_coord_le_one_on_prefix branch chiResetP chiGateP kappaP gainP
          PpolyP HP Aq Kq cμq cαq L R yt v hlam0 hsum0
          (hCr T hT yt hyt0 hderiv) hderiv t ht⟩
  have hMixAff := selector_replicator_mix_affine_bound_explicit
    (branch := branch) (yt := yt) (T := T) hBpos hLam01
  have hMixBound : ∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selectorMixField branch i)| ≤ Mbd T := by
    intro i t ht
    have hzu := (repl_zu_coord_abs_bound_selfcontained (branch := branch)
      (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
      (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
      (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      i (yt := yt) (T := T) (Cbd := Cbd T)
      (Cmix := selectorReplicatorMixConst branch) (kmix := selectorReplicatorMixSlope branch)
      hderiv (hCbd0 T) hCmix0 hkmix0 hCoefZ hCoefU
      (hMixAff i) t ht).2
    rw [hyt0'] at hzu
    have hsum :
        gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
          (Cbd T * (2 + selectorReplicatorMixSlope branch))
          (Cbd T * selectorReplicatorMixConst branch) T ≤
        ∑ j : Fin d,
          gronwallBound ‖(y0 (selZ V j), y0 (selU V j))‖
            (Cbd T * (2 + selectorReplicatorMixSlope branch))
            (Cbd T * selectorReplicatorMixConst branch) T := by
      refine Finset.single_le_sum
        (f := fun j : Fin d =>
          gronwallBound ‖(y0 (selZ V j), y0 (selU V j))‖
            (Cbd T * (2 + selectorReplicatorMixSlope branch))
            (Cbd T * selectorReplicatorMixConst branch) T)
        ?_ (Finset.mem_univ i)
      intro j hj
      exact gronwallBound_nonneg_of_nonneg (norm_nonneg _)
        (mul_nonneg (hCbd0 T) hCmix0) (le_of_lt hT)
    calc
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
          (selectorMixField branch i)|
          ≤ selectorReplicatorMixConst branch + selectorReplicatorMixSlope branch *
              |yt t (selU V i)| := hMixAff i t ht
      _ ≤ selectorReplicatorMixConst branch + selectorReplicatorMixSlope branch *
        gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
          (Cbd T * (2 + selectorReplicatorMixSlope branch))
          (Cbd T * selectorReplicatorMixConst branch) T := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hzu hkmix0) (selectorReplicatorMixConst branch)
      _ ≤ selectorReplicatorMixConst branch + selectorReplicatorMixSlope branch *
          ∑ j : Fin d,
            gronwallBound ‖(y0 (selZ V j), y0 (selU V j))‖
              (Cbd T * (2 + selectorReplicatorMixSlope branch))
              (Cbd T * selectorReplicatorMixConst branch) T := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hsum hkmix0) (selectorReplicatorMixConst branch)
      _ = Mbd T := by
        dsimp [Mbd, selectorReplicatorMixMbdV2]
        rw [hθT]
        congr 2
  have hRen : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRenameZ V HP)| ≤
        Rbd T := by
    intro t ht
    have hren := repl_selRenameZ_abs_bound_from_selfcontained
      (branch := branch) (chiResetP := chiResetP) (chiGateP := chiGateP)
      (kappaP := kappaP) (gainP := gainP) (PpolyP := PpolyP) (HP := HP)
      (Aq := Aq) (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) (Cbd := Cbd T)
      (Cmix := selectorReplicatorMixConst branch) (kmix := selectorReplicatorMixSlope branch)
      hT hderiv (hCbd0 T) hCmix0 hkmix0 hCoefZ hCoefU hMixAff t ht
    rw [hyt0'] at hren
    simpa [Rbd, hθT, y0] using hren
  have hA : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractA d))| ≤ Abd T := by
    intro t ht
    have hA0 := repl_contractA_coord_abs_bound
      (branch := branch)
      (chiResetP := chiResetP) (chiGateP := chiGateP)
      (kappaP := kappaP) (gainP := gainP)
      (PpolyP := PpolyP) (HP := HP)
      (Aq := Aq) (Kq := Kq) (cμq := cμq)
      (cαq := cαq) (L := L) (R := R)
      (x₀ := x₀) (w := w) (warmGainInit := warmGainInit) (yt := yt) (T := T) (Rbd := Rbd T)
      hT hKq0 (derivOnIco_continuousOn hderiv (selOfContract V (contractA d)))
      hyt0 hderiv hRen t ht
    rw [hyt0'] at hA0
    simpa [Abd, y0] using hA0
  exact ⟨hSelRP, hSelRPderiv, hSelQP, hSelQPderiv, hCoefZ, hCoefU,
    hMixBound, hChiGain T hT yt hyt0 hderiv,
    hCr T hT yt hyt0 hderiv, hA⟩

open MachineInstance in
theorem selector_replicator_finiteHorizonBound_MU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ)) :
    Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
      (selectorMUReplicatorInit x₀ w g₀) := by
  classical
  let Gbd : ℝ → ℝ := fun T => (g₀ : ℝ) * Real.exp (bgpParams38.cα * T)
  have hGbdmono : Monotone Gbd := by
    intro S T hST
    dsimp [Gbd]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hST (by norm_num [bgpParams38])))
      hg0
  have hGbd0 : ∀ T : ℝ, 0 ≤ Gbd T := by
    intro T
    exact mul_nonneg hg0 (le_of_lt (Real.exp_pos _))
  refine selector_replicator_finiteHorizonBound_v2
    (branch := branchU)
    (chiResetP := selChiResetPoly d_U UniversalLocalView M)
    (chiGateP := selChiGatePoly d_U UniversalLocalView M)
    (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
    (gainP := selGainPoly d_U UniversalLocalView)
    (PpolyP := muReadoutPoly eta heta) (HP := HP)
    (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
    (cαq := (300 : ℚ)) (L := 1) (R := R)
    (x₀ := x₀) (w := w) (warmGainInit := g₀) (Gbd := Gbd)
    (hBpos := by norm_num [B_U]) hKq0 hGbdmono hGbd0 ?_ ?_
  · intro T hT yt hyt0 hderiv t ht
    have hs0 : yt 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hyt0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractS]
    have hc0 : yt 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractC]
    have hgate := repl_chiGate_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := (300 : ℚ)) (L := 1) (R := R) (M := M)
      (yt := yt) (T := T) hderiv hs0 hc0 t ht
    have hgain := gain_eval_yt (d := d_U) (V := UniversalLocalView) yt t
    have halpha := repl_alpha_coord_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := (300 : ℚ)) (L := 1) (R := R)
      (yt := yt) (T := T) hderiv t ht
    have hα0 : yt 0 (selOfContract UniversalLocalView (contractAlpha d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractAlpha]
    have heq :
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selChiGatePoly d_U UniversalLocalView M) *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selGainPoly d_U UniversalLocalView) =
        ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)) := by
      rw [hgate, hgain, halpha, hα0]
      have hwg : yt t (selWarmGainCoord d_U UniversalLocalView) = ↑g₀ := by
        have hconst := repl_warmGain_coord_eq (branch := branchU)
          (chiResetP := selChiResetPoly d_U UniversalLocalView M)
          (chiGateP := selChiGatePoly d_U UniversalLocalView M)
          (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
          (gainP := selGainPoly d_U UniversalLocalView)
          (PpolyP := muReadoutPoly eta heta) (HP := HP)
          (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
          (cαq := (300 : ℚ)) (L := 1) (R := R)
          (yt := yt) (T := T) hderiv t ht
        rw [hconst, hyt0]
        simp only [selectorReplicatorEuclInitQ, selWarmGainCoord, Fin.append_right]
      rw [hwg]
      norm_num [bgpParams38]
    have hq0 : 0 ≤ ((1 + Real.sin t) / 2) ^ M := by
      simpa [qPulse] using qPulse_nonneg M t
    have hq1 : ((1 + Real.sin t) / 2) ^ M ≤ 1 := by
      simpa [qPulse] using qPulse_le_one M t
    rw [heq, abs_of_nonneg
      (mul_nonneg hq0 (mul_nonneg hg0 (le_of_lt (Real.exp_pos _))))]
    calc
      ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          ≤ 1 * ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)) := by
            exact mul_le_mul_of_nonneg_right hq1
              (mul_nonneg hg0 (le_of_lt (Real.exp_pos _)))
      _ ≤ (g₀ : ℝ) * Real.exp (bgpParams38.cα * T) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (le_of_lt ht.2)
              (by norm_num [bgpParams38])))
          hg0
      _ = Gbd T := rfl
  · intro T hT yt hyt0 hderiv t ht
    have hs0 : yt 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hyt0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractS]
    have hc0 : yt 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractC]
    have hreset := repl_chiReset_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1000 : ℚ))
      (cαq := (300 : ℚ)) (L := 1) (R := R) (M := M)
      (yt := yt) (T := T) hderiv hs0 hc0 t ht
    have hkappa := kappa_eval_yt (d := d_U) (V := UniversalLocalView) κ₀ yt t
    rw [hreset, hkappa]
    exact mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) M) hκ0

open MachineInstance in
theorem bgp_MU_replicator_settled_realized_hfin_halt
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
    (init_zero :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
            (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
              selectorInitX0 w hκ0 hg0 hKq0) w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                    (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                      selectorInitX0 w hκ0 hg0 hKq0) w)
                  La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                    (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                      selectorInitX0 w hκ0 hg0 hKq0) w)
                  La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
            (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
              selectorInitX0 w hκ0 hg0 hKq0) w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0
            w g₀ i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj
              (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                  selectorInitX0 w hκ0 hg0 hKq0) w)
              La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                    (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                      selectorInitX0 w hκ0 hg0 hKq0) w)
                  La (g₀ : ℝ) 0 k ^ 2) + 1))
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
  exact bgp_MU_replicator_settled_realized_halt eta heta M κ₀ g₀ HP Kq R
    (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
      selectorInitX0 w hκ0 hg0 hKq0)
    init_presented init_zero init_succ boxInputs settled

open MachineInstance in
theorem bgp_MU_replicator_settled_realized_hfin_late_start
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
    (init_zero :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
            (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
              selectorInitX0 w hκ0 hg0 hKq0) w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                    (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                      selectorInitX0 w hκ0 hg0 hKq0) w)
                  La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                    (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                      selectorInitX0 w hκ0 hg0 hKq0) w)
                  La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
            (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
              selectorInitX0 w hκ0 hg0 hKq0) w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0
            w g₀ i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj
              (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                  selectorInitX0 w hκ0 hg0 hKq0) w)
              La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                    (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                      selectorInitX0 w hκ0 hg0 hKq0) w)
                  La (g₀ : ℝ) 0 k ^ 2) + 1))
    (boxInputs : MUReplicatorBoxInputs eta heta M κ₀ g₀
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
        (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
          selectorInitX0 w hκ0 hg0 hKq0)))
    (late : MUReplicatorLateStartHaltFacts
      (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
        (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
          selectorInitX0 w hκ0 hg0 hKq0))) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_late_start eta heta M κ₀ g₀ HP Kq R
    (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
      selectorInitX0 w hκ0 hg0 hKq0)
    init_presented init_zero init_succ boxInputs late

open MachineInstance in
theorem bgp_MU_replicator_settled_realized_hfin
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
    (init_zero :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
            (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
              selectorInitX0 w hκ0 hg0 hKq0) w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                    (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                      selectorInitX0 w hκ0 hg0 hKq0) w)
                  La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                    (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                      selectorInitX0 w hκ0 hg0 hKq0) w)
                  La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (La : SelectorReplicatorHaltLatchSol
          (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
            (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
              selectorInitX0 w hκ0 hg0 hKq0) w)
          (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0
            w g₀ i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj
              (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                  selectorInitX0 w hκ0 hg0 hKq0) w)
              La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj
                  (solMUReplRealized eta heta M κ₀ g₀ HP Kq R selectorInitX0
                    (fun w => selector_replicator_finiteHorizonBound_MU eta heta M κ₀ g₀ HP Kq R
                      selectorInitX0 w hκ0 hg0 hKq0) w)
                  La (g₀ : ℝ) 0 k ^ 2) + 1))
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
  bgp_MU_replicator_settled_realized_hfin_halt eta heta M κ₀ g₀ HP Kq R
    hκ0 hg0 hKq0 init_presented init_zero init_succ boxInputs settled.toHaltFacts


#print axioms selector_replicator_coordwise_bound
#print axioms selector_replicator_finiteHorizonBound_MU
#print axioms bgp_MU_replicator_settled_realized_hfin_halt
#print axioms bgp_MU_replicator_settled_realized_hfin_late_start
#print axioms bgp_MU_replicator_settled_realized_hfin

end Ripple.BoundedUniversality.BGP

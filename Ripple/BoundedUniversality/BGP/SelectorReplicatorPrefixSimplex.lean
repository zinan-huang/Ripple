import Ripple.BoundedUniversality.BGP.SelectorReplicatorExistence

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorPrefixSimplex
------------------------------------------
Prefix-local simplex bounds for the selector replicator field.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance MeasureTheory
open scoped BigOperators Topology
open MvPolynomial

theorem derivOnIco_continuousOn
    {N : ℕ} {f : (Fin N → ℝ) → Fin N → ℝ} {y : ℝ → Fin N → ℝ} {T : ℝ}
    (hy : Ripple.DerivOnIco f y T) (k : Fin N) :
    ContinuousOn (fun τ : ℝ => y τ k) (Ico (0 : ℝ) T) := by
  intro t ht
  exact ((hasDerivAt_pi.mp (hy t ht)) k).continuousAt.continuousWithinAt

private theorem eval₂_comp_continuousOn_of_derivOnIco
    {N : ℕ} {f : (Fin N → ℝ) → Fin N → ℝ}
    {yt : ℝ → Fin N → ℝ} {T : ℝ}
    (hy : Ripple.DerivOnIco f yt T) {s : Set ℝ} (hs : s ⊆ Ico (0 : ℝ) T)
    (p : MvPolynomial (Fin N) ℚ) :
    ContinuousOn (fun t : ℝ => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) p) s := by
  have hyt : ContinuousOn yt s := by
    exact continuousOn_pi.2 fun k => (derivOnIco_continuousOn hy k).mono hs
  convert
    (MvPolynomial.continuous_eval
      (p := MvPolynomial.map (algebraMap ℚ ℝ) p)).comp_continuousOn hyt
    using 1
  ext t
  exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (yt t) p

private theorem nonneg_of_linear_inhomogeneous_on_Icc
    (b : ℝ) (hb : 0 ≤ b) (y a p : ℝ → ℝ)
    (hy_cont : ContinuousOn y (Icc (0 : ℝ) b))
    (ha_cont : ContinuousOn a (Icc (0 : ℝ) b))
    (hy0 : 0 ≤ y 0)
    (hp_nonneg : ∀ t ∈ Ico (0 : ℝ) b, 0 ≤ p t)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) b, HasDerivAt y (p t + a t * y t) t) :
    ∀ t ∈ Icc (0 : ℝ) b, 0 ≤ y t := by
  classical
  let A : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, a u
  let E : ℝ → ℝ := fun s => Real.exp (-(A s))
  let H : ℝ → ℝ := fun s => -(y s * E s)
  let Hp : ℝ → ℝ :=
    fun s =>
      -(((p s + a s * y s) * E s) +
        y s * (E s * (-(a s))))

  have hA_deriv_Icc :
      ∀ s ∈ Icc (0 : ℝ) b, HasDerivWithinAt A (a s) (Icc (0 : ℝ) b) s := by
    intro s hs
    have hsub : uIcc (0 : ℝ) s ⊆ Icc (0 : ℝ) b := by
      intro x hx
      have hxs : x ∈ Icc (0 : ℝ) s := by
        simpa [uIcc_of_le hs.1] using hx
      exact ⟨hxs.1, hxs.2.trans hs.2⟩
    have hInt : IntervalIntegrable a volume (0 : ℝ) s :=
      (ha_cont.mono hsub).intervalIntegrable
    have hMeas : StronglyMeasurableAtFilter a (𝓝[Icc (0 : ℝ) b] s) :=
      ha_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s
    haveI : Fact (s ∈ Icc (0 : ℝ) b) := ⟨hs⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right hInt hMeas (ha_cont s hs)

  have hA_cont : ContinuousOn A (Icc (0 : ℝ) b) := by
    intro s hs
    exact (hA_deriv_Icc s hs).continuousWithinAt

  have hE_cont : ContinuousOn E (Icc (0 : ℝ) b) := by
    dsimp [E]
    exact Real.continuous_exp.comp_continuousOn hA_cont.neg

  have hH_cont : ContinuousOn H (Icc (0 : ℝ) b) := by
    dsimp [H]
    exact (hy_cont.mul hE_cont).neg

  have hA_deriv_right :
      ∀ s ∈ Ico (0 : ℝ) b, HasDerivWithinAt A (a s) (Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Icc (0 : ℝ) b := ⟨hs.1, le_of_lt hs.2⟩
    have hsub : uIcc (0 : ℝ) s ⊆ Icc (0 : ℝ) b := by
      intro x hx
      have hxs : x ∈ Icc (0 : ℝ) s := by
        simpa [uIcc_of_le hs.1] using hx
      exact ⟨hxs.1, hxs.2.trans (le_of_lt hs.2)⟩
    have hInt : IntervalIntegrable a volume (0 : ℝ) s :=
      (ha_cont.mono hsub).intervalIntegrable
    have hMeas : StronglyMeasurableAtFilter a (𝓝[Icc (0 : ℝ) b] s) :=
      ha_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s
    haveI : Fact (s ∈ Icc (0 : ℝ) b) := ⟨hsIcc⟩
    have hIcc_deriv :
        HasDerivWithinAt A (a s) (Icc (0 : ℝ) b) s :=
      intervalIntegral.integral_hasDerivWithinAt_right hInt hMeas (ha_cont s hsIcc)
    exact hIcc_deriv.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)

  have hE_deriv :
      ∀ s ∈ Ico (0 : ℝ) b,
        HasDerivWithinAt E (E s * (-(a s))) (Ici s) s := by
    intro s hs
    have hnegA : HasDerivWithinAt (fun r : ℝ => -(A r)) (-(a s)) (Ici s) s :=
      (hA_deriv_right s hs).neg
    dsimp [E]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnegA.exp

  have hH_deriv :
      ∀ s ∈ Ico (0 : ℝ) b,
        HasDerivWithinAt H (Hp s) (Ici s) s := by
    intro s hs
    have hy' : HasDerivWithinAt y (p s + a s * y s) (Ici s) s :=
      (hderiv s hs).hasDerivWithinAt
    have hE' : HasDerivWithinAt E (E s * (-(a s))) (Ici s) s :=
      hE_deriv s hs
    have hmul :
        HasDerivWithinAt
          (fun r : ℝ => y r * E r)
          ((p s + a s * y s) * E s +
            y s * (E s * (-(a s))))
          (Ici s) s :=
      hy'.mul hE'
    have hneg : HasDerivWithinAt H (Hp s) (Ici s) s := by
      dsimp [H, Hp]
      simpa using hmul.neg
    exact hneg

  have hH0 : H 0 ≤ (fun _ : ℝ => (0 : ℝ)) 0 := by
    have hA0 : A 0 = 0 := by
      simp [A]
    have hE0 : E 0 = 1 := by
      simp [E, hA0]
    dsimp [H]
    rw [hE0]
    linarith

  have hB_cont : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc (0 : ℝ) b) :=
    continuous_const.continuousOn

  have hB_deriv :
      ∀ s ∈ Ico (0 : ℝ) b,
        HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Ici s) s := by
    intro s _hs
    simpa using (hasDerivAt_const (x := s) (c := (0 : ℝ))).hasDerivWithinAt

  have hHp_nonpos : ∀ s ∈ Ico (0 : ℝ) b, Hp s ≤ 0 := by
    intro s hs
    have hp_s : 0 ≤ p s := hp_nonneg s hs
    have hEpos : 0 < E s := by
      dsimp [E]
      exact Real.exp_pos _
    have hHp_eq : Hp s = -(E s * p s) := by
      dsimp [Hp]
      ring
    rw [hHp_eq]
    exact neg_nonpos.mpr (mul_nonneg (le_of_lt hEpos) hp_s)

  have hH_le_zero :
      ∀ s ∈ Icc (0 : ℝ) b, H s ≤ 0 := by
    intro s hs
    exact
      image_le_of_deriv_right_le_deriv_boundary
        (f := H)
        (f' := Hp)
        (a := (0 : ℝ))
        (b := b)
        (B := fun _ : ℝ => (0 : ℝ))
        (B' := fun _ : ℝ => (0 : ℝ))
        hH_cont
        hH_deriv
        hH0
        hB_cont
        hB_deriv
        hHp_nonpos
        hs

  intro t ht
  have hHt : H t ≤ 0 := hH_le_zero t ht
  have hprod : 0 ≤ y t * E t := by
    dsimp [H] at hHt
    linarith
  have hEpos : 0 < E t := by
    dsimp [E]
    exact Real.exp_pos _
  exact (mul_nonneg_iff_of_pos_right hEpos).mp hprod

theorem replicator_lam_coord_nonneg_on_prefix
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ} (v : V)
    (hlam0 : 0 ≤ yt 0 (selLamCoord v))
    (hCr : ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hderiv : Ripple.DerivOnIco
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R) yt T) :
    ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ yt t (selLamCoord v) := by
  classical
  let lam : ℝ → ℝ := fun t => yt t (selLamCoord v)
  let cr : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP
  let cg : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP
  let phi : ℝ → ℝ := fun t =>
    ∑ w : V, yt t (selLamCoord w) *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (PpolyP w)
  let a : ℝ → ℝ := fun t =>
    -cr t + cg t *
      (MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (PpolyP v) - phi t)
  let psrc : ℝ → ℝ := fun t => cr t * (1 / (Fintype.card V : ℝ))

  intro t ht
  have hIcc_subset : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hIco_subset : Ico (0 : ℝ) t ⊆ Ico (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, lt_trans hs.2 ht.2⟩

  have hlam_cont : ContinuousOn lam (Icc (0 : ℝ) t) := by
    exact (derivOnIco_continuousOn hderiv (selLamCoord v)).mono hIcc_subset

  have hcr_cont : ContinuousOn cr (Icc (0 : ℝ) t) := by
    exact
      (eval₂_comp_continuousOn_of_derivOnIco hderiv hIcc_subset chiResetP).mul
        (eval₂_comp_continuousOn_of_derivOnIco hderiv hIcc_subset kappaP)

  have hcg_cont : ContinuousOn cg (Icc (0 : ℝ) t) := by
    exact
      (eval₂_comp_continuousOn_of_derivOnIco hderiv hIcc_subset chiGateP).mul
        (eval₂_comp_continuousOn_of_derivOnIco hderiv hIcc_subset gainP)

  have hP_cont :
      ContinuousOn
        (fun s : ℝ =>
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) (PpolyP v))
        (Icc (0 : ℝ) t) :=
    eval₂_comp_continuousOn_of_derivOnIco hderiv hIcc_subset (PpolyP v)

  have hphi_cont : ContinuousOn phi (Icc (0 : ℝ) t) := by
    dsimp [phi]
    exact continuousOn_finsetSum Finset.univ (fun w _ =>
      ((derivOnIco_continuousOn hderiv (selLamCoord w)).mono hIcc_subset).mul
        (eval₂_comp_continuousOn_of_derivOnIco hderiv hIcc_subset (PpolyP w)))

  have ha_cont : ContinuousOn a (Icc (0 : ℝ) t) := by
    dsimp [a]
    exact hcr_cont.neg.add (hcg_cont.mul (hP_cont.sub hphi_cont))

  have hp_nonneg : ∀ s ∈ Ico (0 : ℝ) t, 0 ≤ psrc s := by
    intro s hs
    dsimp [psrc, cr]
    exact mul_nonneg (hCr s (hIco_subset hs)) (one_div_nonneg.mpr (Nat.cast_nonneg _))

  have hlin :
      ∀ s ∈ Ico (0 : ℝ) t,
        HasDerivAt lam (psrc s + a s * lam s) s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hderiv s (hIco_subset hs))) (selLamCoord v)
    rw [aprioriReplicatorField_lam_eq] at hpi
    convert hpi using 1 <;> simp [lam, cr, cg, phi, a, psrc] <;> ring

  have hnonneg :=
    nonneg_of_linear_inhomogeneous_on_Icc t ht.1 lam a psrc
      hlam_cont ha_cont (by simpa [lam] using hlam0) hp_nonneg hlin
  exact hnonneg t (right_mem_Icc.mpr ht.1)

private theorem replicator_lam_sum_eq_one_on_prefix
    {d B : ℕ} {V : Type} [Fintype V] [Nonempty V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hsum0 : (∑ v : V, yt 0 (selLamCoord v)) = 1)
    (hderiv : Ripple.DerivOnIco
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R) yt T) :
    ∀ t ∈ Ico (0 : ℝ) T, (∑ v : V, yt t (selLamCoord v)) = 1 := by
  classical
  let lam : V → ℝ → ℝ := fun v t => yt t (selLamCoord v)
  let P : V → ℝ → ℝ := fun v t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (PpolyP v)
  let cr : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP
  let cg : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP
  let coeff : ℝ → ℝ := fun t => cr t + cg t * (∑ w : V, lam w t * P w t)
  let massGap : ℝ → ℝ := fun t => 1 - ∑ v : V, lam v t

  have hcard_ne : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card V))

  have hconst_sum : (∑ _v : V, (1 : ℝ) / (Fintype.card V : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel hcard_ne

  have hsum_rhs :
      ∀ s : ℝ,
        (∑ v : V,
          (cr s * (1 / (Fintype.card V : ℝ) - lam v s)
            + cg s * lam v s * (P v s - ∑ w : V, lam w s * P w s))) =
          massGap s * coeff s := by
    intro s
    let phi : ℝ := ∑ w : V, lam w s * P w s
    let total : ℝ := ∑ v : V, lam v s
    have hreset :
        (∑ v : V, cr s * (1 / (Fintype.card V : ℝ) - lam v s)) =
          cr s * (1 - total) := by
      calc
        (∑ v : V, cr s * (1 / (Fintype.card V : ℝ) - lam v s))
            = cr s * (∑ v : V, (1 / (Fintype.card V : ℝ) - lam v s)) := by
                rw [Finset.mul_sum]
        _ = cr s * ((∑ _v : V, (1 : ℝ) / (Fintype.card V : ℝ))
              - ∑ v : V, lam v s) := by
                rw [Finset.sum_sub_distrib]
        _ = cr s * (1 - total) := by rw [hconst_sum]
    have hgate :
        (∑ v : V, cg s * lam v s * (P v s - phi)) =
          cg s * (phi - total * phi) := by
      calc
        (∑ v : V, cg s * lam v s * (P v s - phi))
            = cg s * (∑ v : V, lam v s * (P v s - phi)) := by
                simp_rw [mul_assoc (cg s)]
                rw [Finset.mul_sum]
        _ = cg s * ((∑ v : V, lam v s * P v s) - ∑ v : V, lam v s * phi) := by
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib]
                rw [mul_sub]
        _ = cg s * (phi - total * phi) := by rw [Finset.sum_mul]
    calc
      (∑ v : V,
          (cr s * (1 / (Fintype.card V : ℝ) - lam v s)
            + cg s * lam v s * (P v s - ∑ w : V, lam w s * P w s)))
          = (∑ v : V, cr s * (1 / (Fintype.card V : ℝ) - lam v s))
              + ∑ v : V, cg s * lam v s * (P v s - phi) := by
                rw [Finset.sum_add_distrib]
      _ = cr s * (1 - total) + cg s * (phi - total * phi) := by rw [hreset, hgate]
      _ = massGap s * coeff s := by
                dsimp [massGap, coeff, phi, total]
                ring

  have hgap_deriv :
      ∀ s ∈ Ico (0 : ℝ) T, HasDerivAt massGap (-(coeff s) * massGap s) s := by
    intro s hs
    have hsum_deriv :
        HasDerivAt (fun τ : ℝ => ∑ v : V, lam v τ)
          (∑ v : V,
            (cr s * (1 / (Fintype.card V : ℝ) - lam v s)
              + cg s * lam v s * (P v s - ∑ w : V, lam w s * P w s))) s := by
      refine HasDerivAt.fun_sum (u := Finset.univ) ?_
      intro v _hv
      have hpi := (hasDerivAt_pi.mp (hderiv s hs)) (selLamCoord v)
      rw [aprioriReplicatorField_lam_eq] at hpi
      simpa [lam, P, cr, cg, mul_assoc] using hpi
    have hgap := hsum_deriv.const_sub 1
    convert hgap using 1
    · rw [hsum_rhs s]
      ring

  have hgap0 : massGap 0 = 0 := by
    dsimp [massGap, lam]
    linarith

  intro t ht
  have hIcc_subset : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hIco_subset : Ico (0 : ℝ) t ⊆ Ico (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, lt_trans hs.2 ht.2⟩

  have hmass_cont : ContinuousOn massGap (Icc (0 : ℝ) t) := by
    dsimp [massGap, lam]
    exact continuousOn_const.sub
      (continuousOn_finsetSum Finset.univ (fun v _ =>
        (derivOnIco_continuousOn hderiv (selLamCoord v)).mono hIcc_subset))

  have hcr_cont : ContinuousOn cr (Icc (0 : ℝ) t) := by
    exact
      (eval₂_comp_continuousOn_of_derivOnIco hderiv hIcc_subset chiResetP).mul
        (eval₂_comp_continuousOn_of_derivOnIco hderiv hIcc_subset kappaP)

  have hcg_cont : ContinuousOn cg (Icc (0 : ℝ) t) := by
    exact
      (eval₂_comp_continuousOn_of_derivOnIco hderiv hIcc_subset chiGateP).mul
        (eval₂_comp_continuousOn_of_derivOnIco hderiv hIcc_subset gainP)

  have hcoupling_cont :
      ContinuousOn (fun s : ℝ => ∑ w : V, lam w s * P w s) (Icc (0 : ℝ) t) := by
    dsimp [lam, P]
    exact continuousOn_finsetSum Finset.univ (fun w _ =>
      ((derivOnIco_continuousOn hderiv (selLamCoord w)).mono hIcc_subset).mul
        (eval₂_comp_continuousOn_of_derivOnIco hderiv hIcc_subset (PpolyP w)))

  have hcoeff_cont : ContinuousOn coeff (Icc (0 : ℝ) t) := by
    dsimp [coeff]
    exact hcr_cont.add (hcg_cont.mul hcoupling_cont)

  have hgap_nonneg : 0 ≤ massGap t := by
    have h :=
      nonneg_of_linear_inhomogeneous_on_Icc t ht.1 massGap
        (fun s => -(coeff s)) (fun _ => (0 : ℝ))
        hmass_cont hcoeff_cont.neg (by simpa [hgap0])
        (fun s _hs => by simp)
        (fun s hs => by
          have hder := hgap_deriv s (hIco_subset hs)
          convert hder using 1
          ring)
    exact h t (right_mem_Icc.mpr ht.1)

  have hneg_gap_nonneg : 0 ≤ -massGap t := by
    have h :=
      nonneg_of_linear_inhomogeneous_on_Icc t ht.1 (fun s => -massGap s)
        (fun s => -(coeff s)) (fun _ => (0 : ℝ))
        hmass_cont.neg hcoeff_cont.neg (by simp [hgap0])
        (fun s _hs => by simp)
        (fun s hs => by
          have hder := (hgap_deriv s (hIco_subset hs)).neg
          convert hder using 1
          ring)
    exact h t (right_mem_Icc.mpr ht.1)

  dsimp [massGap, lam] at hgap_nonneg hneg_gap_nonneg
  linarith

theorem replicator_lam_coord_le_one_on_prefix
    {d B : ℕ} {V : Type} [Fintype V] [Nonempty V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ} (v : V)
    (hlam0 : ∀ v : V, 0 ≤ yt 0 (selLamCoord v))
    (hsum0 : (∑ v : V, yt 0 (selLamCoord v)) = 1)
    (hCr : ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hderiv : Ripple.DerivOnIco
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R) yt T) :
    ∀ t ∈ Ico (0 : ℝ) T, yt t (selLamCoord v) ≤ 1 := by
  classical
  intro t ht
  have hnonneg : ∀ w : V, 0 ≤ yt t (selLamCoord w) := by
    intro w
    exact
      replicator_lam_coord_nonneg_on_prefix branch chiResetP chiGateP kappaP gainP
        PpolyP HP Aq Kq cμq cαq L R yt w (hlam0 w) hCr hderiv t ht
  have hsum :=
    replicator_lam_sum_eq_one_on_prefix branch chiResetP chiGateP kappaP gainP
      PpolyP HP Aq Kq cμq cαq L R yt hsum0 hderiv t ht
  have hle_sum : yt t (selLamCoord v) ≤ ∑ w : V, yt t (selLamCoord w) :=
    Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
  simpa [hsum] using hle_sum

#print axioms derivOnIco_continuousOn
#print axioms replicator_lam_coord_nonneg_on_prefix
#print axioms replicator_lam_coord_le_one_on_prefix

end Ripple.BoundedUniversality.BGP

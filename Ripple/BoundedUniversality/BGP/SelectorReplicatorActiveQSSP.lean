import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledResidual

/-!
# Parameter-generic active-QSS chain

`P` twins of the statement-level `bgpParams38` active-QSS dependency chain.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine Filter Set
open scoped BigOperators Topology

def selectorMU_uDerivRHSP
    {p : DynGateParams} {eta : ℚ} {heta : 0 < eta}
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (t : ℝ) (i : Fin d_U) : ℝ :=
  p.A * (sol w).α t * bGateU p.L ((sol w).μ t) t *
    ((sol w).z t i - (sol w).u t i)

def selectorMU_universalPvalDerivRHSP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (v : UniversalLocalView) (t : ℝ) : ℝ :=
  ∑ i : Fin d_U,
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u t)
      (MvPolynomial.pderiv i
        (viewSelectorPolyN universalViewSpecN
          (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)) *
      selectorMU_uDerivRHSP sol w t i

theorem selectorMU_universalPvalDerivRHS_abs_le_of_coord_boundsP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (v : UniversalLocalView) (t : ℝ)
    (G U : Fin d_U → ℝ)
    (hG_nonneg : ∀ i : Fin d_U, 0 ≤ G i)
    (hgrad :
      ∀ i : Fin d_U,
        |MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u t)
          (MvPolynomial.pderiv i
            (viewSelectorPolyN universalViewSpecN
              (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v))| ≤
          G i)
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHSP sol w t i| ≤ U i) :
    |selectorMU_universalPvalDerivRHSP eta heta sol w v t| ≤
      ∑ i : Fin d_U, G i * U i := by
  classical
  unfold selectorMU_universalPvalDerivRHSP
  calc
    |∑ i : Fin d_U,
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u t)
          (MvPolynomial.pderiv i
            (viewSelectorPolyN universalViewSpecN
              (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)) *
          selectorMU_uDerivRHSP sol w t i|
        ≤ ∑ i : Fin d_U,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u t)
            (MvPolynomial.pderiv i
              (viewSelectorPolyN universalViewSpecN
                (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)) *
            selectorMU_uDerivRHSP sol w t i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d_U, G i * U i := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        rw [abs_mul]
        exact mul_le_mul (hgrad i) (huRHS i) (abs_nonneg _) (hG_nonneg i)

theorem selectorMU_universalPvalDerivRHS_abs_le_gradBoxBound_mul_uniform_uRHSP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (v : UniversalLocalView) (t : ℝ)
    (r : Fin d_U → ℝ) {URhs : ℝ}
    (hr0 : ∀ k : Fin d_U, 0 ≤ r k)
    (hu_coord : ∀ k : Fin d_U, |(sol w).u t k| ≤ r k)
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHSP sol w t i| ≤ URhs) :
    |selectorMU_universalPvalDerivRHSP eta heta sol w v t| ≤
      selectorMU_pvalGradBoxBound eta heta v r * URhs := by
  have h :=
    selectorMU_universalPvalDerivRHS_abs_le_of_coord_boundsP
      eta heta (sol := sol) w v t
      (fun i : Fin d_U => selectorMU_pvalPderivBoxBound eta heta v i r)
      (fun _ : Fin d_U => URhs)
      (fun i => selectorMU_pvalPderivBoxBound_nonneg eta heta v i hr0)
      (fun i =>
        selectorMU_pval_pderiv_eval_abs_le_boxBound
          eta heta v i ((sol w).u t) r hr0 hu_coord)
      huRHS
  calc
    |selectorMU_universalPvalDerivRHSP eta heta sol w v t|
        ≤ ∑ i : Fin d_U,
          selectorMU_pvalPderivBoxBound eta heta v i r * URhs := h
    _ = selectorMU_pvalGradBoxBound eta heta v r * URhs := by
        simp [selectorMU_pvalGradBoxBound, Finset.sum_mul]

theorem selectorMU_universalPvalGapDerivRHS_abs_le_of_view_boundsP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (t : ℝ)
    (B : UniversalLocalView → ℝ)
    (hB : ∀ x : UniversalLocalView,
      |selectorMU_universalPvalDerivRHSP eta heta sol w x t| ≤ B x) :
    |selectorMU_universalPvalDerivRHSP eta heta sol w c t -
      selectorMU_universalPvalDerivRHSP eta heta sol w v t| ≤ B c + B v := by
  calc
    |selectorMU_universalPvalDerivRHSP eta heta sol w c t -
      selectorMU_universalPvalDerivRHSP eta heta sol w v t|
        ≤ |selectorMU_universalPvalDerivRHSP eta heta sol w c t| +
          |selectorMU_universalPvalDerivRHSP eta heta sol w v t| :=
            abs_sub _ _
    _ ≤ B c + B v := add_le_add (hB c) (hB v)

theorem selectorMU_universalPvalDerivRHS_abs_le_utube_gradBoxBound_mul_uniform_uRHSP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (v : UniversalLocalView) (t : ℝ)
    (cfg : UConf) (ρ : ℝ) {URhs : ℝ}
    (hρ0 : 0 ≤ ρ)
    (hutube : UTube ρ cfg ((sol w).u t))
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHSP sol w t i| ≤ URhs) :
    |selectorMU_universalPvalDerivRHSP eta heta sol w v t| ≤
      selectorMU_pvalGradBoxBound eta heta v
          (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|) *
        URhs := by
  exact
    selectorMU_universalPvalDerivRHS_abs_le_gradBoxBound_mul_uniform_uRHSP
      eta heta (sol := sol) w v t
      (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|)
      (by intro k; exact add_nonneg hρ0 (abs_nonneg _))
      (selectorMU_abs_u_le_tube_radius_add_enc_abs hutube)
      huRHS

theorem selectorMU_universalPvalGapDerivRHS_abs_le_utube_gradBoxBound_mul_uniform_uRHSP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (t : ℝ)
    (cfg : UConf) (ρ : ℝ) {URhs : ℝ}
    (hρ0 : 0 ≤ ρ)
    (hutube : UTube ρ cfg ((sol w).u t))
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHSP sol w t i| ≤ URhs) :
    |selectorMU_universalPvalDerivRHSP eta heta sol w c t -
      selectorMU_universalPvalDerivRHSP eta heta sol w v t| ≤
      (selectorMU_pvalGradBoxBound eta heta c
          (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|) +
        selectorMU_pvalGradBoxBound eta heta v
          (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|)) *
        URhs := by
  let r : Fin d_U → ℝ := fun k => ρ + |(confEncU cfg k : ℝ)|
  have hview :
      ∀ x : UniversalLocalView,
        |selectorMU_universalPvalDerivRHSP eta heta sol w x t| ≤
          selectorMU_pvalGradBoxBound eta heta x r * URhs := by
    intro x
    simpa [r] using
      selectorMU_universalPvalDerivRHS_abs_le_utube_gradBoxBound_mul_uniform_uRHSP
        eta heta (sol := sol) w x t cfg ρ hρ0 hutube huRHS
  have hgap :=
    selectorMU_universalPvalGapDerivRHS_abs_le_of_view_boundsP
      eta heta (sol := sol) w c v t
      (fun x : UniversalLocalView =>
        selectorMU_pvalGradBoxBound eta heta x r * URhs)
      hview
  calc
    |selectorMU_universalPvalDerivRHSP eta heta sol w c t -
      selectorMU_universalPvalDerivRHSP eta heta sol w v t|
        ≤ selectorMU_pvalGradBoxBound eta heta c r * URhs +
          selectorMU_pvalGradBoxBound eta heta v r * URhs := hgap
    _ = (selectorMU_pvalGradBoxBound eta heta c r +
          selectorMU_pvalGradBoxBound eta heta v r) * URhs := by
          ring
    _ = (selectorMU_pvalGradBoxBound eta heta c
            (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|) +
          selectorMU_pvalGradBoxBound eta heta v
            (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|)) * URhs := by
          rfl

theorem selectorMU_universalPval_hasDerivAt_of_sol_u_hasDerivAtP
    {p : DynGateParams} {eta : ℚ} {heta : 0 < eta}
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (v : UniversalLocalView) {t : ℝ}
    (ht : t ∈ selectorSchedule.domain) :
    HasDerivAt
      (fun τ => universalPval eta heta v ((sol w).u τ))
      (selectorMU_universalPvalDerivRHSP eta heta sol w v t) t := by
  simpa [selectorMU_universalPvalDerivRHSP, selectorMU_uDerivRHSP] using
    universalPval_hasDerivAt_of_u_hasDerivAt eta heta v
      (fun i => (sol w).u_hasDeriv t ht i)

theorem selectorMU_universalPval_gap_hasDerivAt_of_sol_u_hasDerivAtP
    {p : DynGateParams} {eta : ℚ} {heta : 0 < eta}
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) {t : ℝ}
    (ht : t ∈ selectorSchedule.domain) :
    HasDerivAt
      (fun τ =>
        universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ))
      (selectorMU_universalPvalDerivRHSP eta heta sol w c t -
        selectorMU_universalPvalDerivRHSP eta heta sol w v t) t := by
  exact
    (selectorMU_universalPval_hasDerivAt_of_sol_u_hasDerivAtP
      (sol := sol) w c ht).sub
      (selectorMU_universalPval_hasDerivAt_of_sol_u_hasDerivAtP
        (sol := sol) w v ht)

theorem selectorMU_uDerivRHS_continuousP
    {p : DynGateParams} {eta : ℚ} {heta : 0 < eta}
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (i : Fin d_U) :
    Continuous fun τ : ℝ => selectorMU_uDerivRHSP sol w τ i := by
  have hq : Continuous fun τ : ℝ => qPulse p.L τ := by
    simp only [qPulse]
    exact ((continuous_const.add Real.continuous_sin).div_const 2).pow p.L
  have hgateU : Continuous fun τ : ℝ =>
      bGateU p.L ((sol w).μ τ) τ := by
    simp only [bGateU]
    exact Real.continuous_exp.comp ((((sol w).cont_μ).mul hq).neg)
  exact (((continuous_const.mul ((sol w).cont_α)).mul hgateU).mul
    (((sol w).cont_z i).sub ((sol w).cont_u i)))

private theorem mvPolynomial_eval₂_continuous_of_cont_uP
    {sigma : Type} [Fintype sigma]
    (poly : MvPolynomial sigma ℚ) {u : ℝ → sigma → ℝ}
    (hu : ∀ i : sigma, Continuous fun t => u t i) :
    Continuous fun t => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) poly := by
  have hucont : Continuous u := continuous_pi hu
  convert
    (MvPolynomial.continuous_eval
      (p := MvPolynomial.map (algebraMap ℚ ℝ) poly)).comp hucont
    using 1
  ext t
  exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (u t) poly

theorem selectorMU_universalPvalDerivRHS_continuousP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (v : UniversalLocalView) :
    Continuous fun τ : ℝ =>
      selectorMU_universalPvalDerivRHSP eta heta sol w v τ := by
  classical
  unfold selectorMU_universalPvalDerivRHSP
  refine continuous_finsetSum Finset.univ ?_
  intro i _hi
  have hpoly :
      Continuous fun τ : ℝ =>
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u τ)
          (MvPolynomial.pderiv i
            (viewSelectorPolyN universalViewSpecN
              (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)) :=
    mvPolynomial_eval₂_continuous_of_cont_uP _ (fun k => (sol w).cont_u k)
  exact hpoly.mul (selectorMU_uDerivRHS_continuousP sol w i)

theorem selectorMU_activeSuffix_sinkCoeff_pos_of_gap_nonnegP
    {p : DynGateParams} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (j : ℕ) {τ delta : ℝ}
    (hτ : τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j))
    (hdelta_nonneg : 0 ≤ delta) :
    0 < selectorMU_activeCr Mcy κ₀ τ +
      (((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (p.cα * τ))) * delta := by
  have hcr_pos : 0 < selectorMU_activeCr Mcy κ₀ τ := by
    simpa [selectorMU_activeCr] using
      selectorMU_activeSuffix_resetCoeff_pos hκ₀_pos j hτ
  have hsin_base_nonneg : 0 ≤ (1 + Real.sin τ) / 2 := by
    nlinarith [Real.neg_one_le_sin τ]
  have hcg_nonneg :
      0 ≤ ((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (p.cα * τ)) := by
    exact mul_nonneg (pow_nonneg hsin_base_nonneg Mcy)
      (mul_nonneg hg₀_nonneg (Real.exp_pos _).le)
  exact add_pos_of_pos_of_nonneg hcr_pos (mul_nonneg hcg_nonneg hdelta_nonneg)

def selectorMU_activeCgP
    {p : DynGateParams} (Mcy : ℕ) (g₀ : ℚ) (τ : ℝ) : ℝ :=
  ((1 + Real.sin τ) / 2) ^ Mcy *
    ((g₀ : ℝ) * Real.exp (p.cα * τ))

def selectorMU_activeSinkP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ) : ℝ :=
  selectorMU_activeCr Mcy κ₀ τ +
    selectorMU_activeCgP (p := p) Mcy g₀ τ *
    (universalPval eta heta c ((sol w).u τ) -
      universalPval eta heta v ((sol w).u τ))

def selectorMU_activeQSSP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ) : ℝ :=
  (selectorMU_activeCr Mcy κ₀ τ *
      (Fintype.card UniversalLocalView : ℝ)⁻¹) /
    selectorMU_activeSinkP eta heta sol w c v τ

def selectorMU_activeCgDerivP
    {p : DynGateParams} (Mcy : ℕ) (g₀ : ℚ) (τ : ℝ) : ℝ :=
  deriv (fun s : ℝ => selectorMU_activeCgP (p := p) Mcy g₀ s) τ

theorem selectorMU_activeCg_abs_le_exp_gainP
    {p : DynGateParams} (Mcy : ℕ) (g₀ : ℚ) (τ : ℝ) :
    |selectorMU_activeCgP (p := p) Mcy g₀ τ| ≤
      |(g₀ : ℝ)| * Real.exp (p.cα * τ) := by
  let base : ℝ := (1 + Real.sin τ) / 2
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    nlinarith [Real.neg_one_le_sin τ]
  have hbase1 : base ≤ 1 := by
    dsimp [base]
    nlinarith [Real.sin_le_one τ]
  have hbase_pow_abs : |base ^ Mcy| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hbase0 _)]
    exact pow_le_one₀ hbase0 hbase1
  have hexp_nonneg : 0 ≤ Real.exp (p.cα * τ) := (Real.exp_pos _).le
  calc
    |selectorMU_activeCgP (p := p) Mcy g₀ τ|
        = |base ^ Mcy| * (|(g₀ : ℝ)| * Real.exp (p.cα * τ)) := by
            rw [selectorMU_activeCgP, abs_mul, abs_mul,
              abs_of_nonneg hexp_nonneg]
    _ ≤ 1 * (|(g₀ : ℝ)| * Real.exp (p.cα * τ)) :=
        mul_le_mul_of_nonneg_right hbase_pow_abs
          (mul_nonneg (abs_nonneg _) hexp_nonneg)
    _ = |(g₀ : ℝ)| * Real.exp (p.cα * τ) := by ring

theorem selectorMU_activeCgDeriv_abs_le_exp_gainP
    {p : DynGateParams} (Mcy : ℕ) (g₀ : ℚ) (τ : ℝ) :
    |selectorMU_activeCgDerivP (p := p) Mcy g₀ τ| ≤
      ((Mcy : ℝ) + |p.cα|) *
        (|(g₀ : ℝ)| * Real.exp (p.cα * τ)) := by
  let base : ℝ := (1 + Real.sin τ) / 2
  let gain : ℝ := |(g₀ : ℝ)| * Real.exp (p.cα * τ)
  let baseDeriv : ℝ := Real.cos τ / 2
  let gainDeriv : ℝ :=
    (g₀ : ℝ) * (p.cα * Real.exp (p.cα * τ))
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    nlinarith [Real.neg_one_le_sin τ]
  have hbase1 : base ≤ 1 := by
    dsimp [base]
    nlinarith [Real.sin_le_one τ]
  have hbase_pow_abs_pred : |base ^ (Mcy - 1)| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hbase0 _)]
    exact pow_le_one₀ hbase0 hbase1
  have hbase_pow_abs : |base ^ Mcy| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hbase0 _)]
    exact pow_le_one₀ hbase0 hbase1
  have hbase_deriv :
      HasDerivAt (fun s : ℝ => (1 + Real.sin s) / 2) baseDeriv τ := by
    dsimp [baseDeriv]
    convert ((hasDerivAt_const (x := τ) (c := (1 : ℝ))).add
      (Real.hasDerivAt_sin τ)).div_const 2 using 1
    ring
  have hexp_deriv :
      HasDerivAt (fun s : ℝ =>
        (g₀ : ℝ) * Real.exp (p.cα * s)) gainDeriv τ := by
    simpa [gainDeriv, mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id τ).const_mul p.cα).exp.const_mul (g₀ : ℝ))
  have hcg :
      HasDerivAt (fun s : ℝ => selectorMU_activeCgP (p := p) Mcy g₀ s)
        ((Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
            ((g₀ : ℝ) * Real.exp (p.cα * τ)) +
          base ^ Mcy * gainDeriv) τ := by
    dsimp [selectorMU_activeCgP, base]
    convert (hbase_deriv.pow Mcy).mul hexp_deriv using 1
  have hderiv :
      selectorMU_activeCgDerivP (p := p) Mcy g₀ τ =
        (Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
            ((g₀ : ℝ) * Real.exp (p.cα * τ)) +
          base ^ Mcy * gainDeriv := by
    simpa [selectorMU_activeCgDerivP] using hcg.deriv
  have hcos_half_abs : |baseDeriv| ≤ 1 := by
    dsimp [baseDeriv]
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [Real.abs_cos_le_one τ]
  have hexp_nonneg : 0 ≤ Real.exp (p.cα * τ) := (Real.exp_pos _).le
  have hgain_nonneg : 0 ≤ gain := by
    dsimp [gain]
    exact mul_nonneg (abs_nonneg _) hexp_nonneg
  have hM_nonneg : 0 ≤ (Mcy : ℝ) := Nat.cast_nonneg Mcy
  have hterm_base :
      |(Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
          ((g₀ : ℝ) * Real.exp (p.cα * τ))| ≤
        (Mcy : ℝ) * gain := by
    calc
      |(Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
          ((g₀ : ℝ) * Real.exp (p.cα * τ))|
          = (Mcy : ℝ) * |base ^ (Mcy - 1)| * |baseDeriv| * gain := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul,
                abs_of_nonneg hM_nonneg, abs_of_nonneg hexp_nonneg]
      _ ≤ (Mcy : ℝ) * 1 * 1 * gain := by
          have hprod :
              (Mcy : ℝ) * (|base ^ (Mcy - 1)| * |baseDeriv|) ≤
                (Mcy : ℝ) * (1 * 1) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hbase_pow_abs_pred hcos_half_abs
                (abs_nonneg _) zero_le_one) hM_nonneg
          exact mul_le_mul_of_nonneg_right
            (by simpa [mul_assoc] using hprod) hgain_nonneg
      _ = (Mcy : ℝ) * gain := by ring
  have hterm_exp :
      |base ^ Mcy * gainDeriv| ≤ |p.cα| * gain := by
    have hgainDeriv_abs : |gainDeriv| ≤ |p.cα| * gain := by
      calc
        |gainDeriv|
            = |(g₀ : ℝ)| * (|p.cα| * Real.exp (p.cα * τ)) := by
                dsimp [gainDeriv]
                rw [abs_mul, abs_mul, abs_of_nonneg hexp_nonneg]
        _ = |p.cα| * gain := by
            dsimp [gain]
            ring
        _ ≤ |p.cα| * gain := le_rfl
    calc
      |base ^ Mcy * gainDeriv|
          = |base ^ Mcy| * |gainDeriv| := by rw [abs_mul]
      _ ≤ 1 * (|p.cα| * gain) :=
          mul_le_mul hbase_pow_abs hgainDeriv_abs (abs_nonneg _) zero_le_one
      _ = |p.cα| * gain := by ring
  calc
    |selectorMU_activeCgDerivP (p := p) Mcy g₀ τ|
        = |((Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
              ((g₀ : ℝ) * Real.exp (p.cα * τ)) +
            base ^ Mcy * gainDeriv)| := by rw [hderiv]
    _ ≤ |(Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
            ((g₀ : ℝ) * Real.exp (p.cα * τ))| +
          |base ^ Mcy * gainDeriv| :=
        abs_add_le _ _
    _ ≤ (Mcy : ℝ) * gain + |p.cα| * gain :=
      add_le_add hterm_base hterm_exp
    _ = ((Mcy : ℝ) + |p.cα|) * gain := by ring_nf

def selectorMU_activeSinkDerivRHSP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ) : ℝ :=
  let delta :=
    universalPval eta heta c ((sol w).u τ) -
      universalPval eta heta v ((sol w).u τ)
  let delta' :=
    selectorMU_universalPvalDerivRHSP eta heta sol w c τ -
      selectorMU_universalPvalDerivRHSP eta heta sol w v τ
  selectorMU_activeCrDeriv Mcy κ₀ τ +
    selectorMU_activeCgDerivP (p := p) Mcy g₀ τ * delta +
      selectorMU_activeCgP (p := p) Mcy g₀ τ * delta'

def selectorMU_activeQSSDerivRHSP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ) : ℝ :=
  let card : ℝ := Fintype.card UniversalLocalView
  let r := selectorMU_activeCr Mcy κ₀ τ * card⁻¹
  let r' := selectorMU_activeCrDeriv Mcy κ₀ τ * card⁻¹
  let k := selectorMU_activeSinkP eta heta sol w c v τ
  let k' := selectorMU_activeSinkDerivRHSP eta heta sol w c v τ
  (r' * k - r * k') / (k ^ 2)

theorem selectorMU_activeQSSDerivRHS_abs_le_of_deltaD_boundP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ)
    {gamma CrD DeltaD : ℝ}
    (hgamma_pos : 0 < gamma)
    (hcr_nonneg : 0 ≤ selectorMU_activeCr Mcy κ₀ τ)
    (hdelta_floor :
      gamma ≤ selectorMU_activeCgP (p := p) Mcy g₀ τ *
        (universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ)))
    (hcrD : |selectorMU_activeCrDeriv Mcy κ₀ τ| ≤ CrD)
    (hdeltaD :
      |selectorMU_activeCgDerivP (p := p) Mcy g₀ τ *
          (universalPval eta heta c ((sol w).u τ) -
            universalPval eta heta v ((sol w).u τ)) +
        selectorMU_activeCgP (p := p) Mcy g₀ τ *
          (selectorMU_universalPvalDerivRHSP eta heta sol w c τ -
            selectorMU_universalPvalDerivRHSP eta heta sol w v τ)| ≤ DeltaD) :
    |selectorMU_activeQSSDerivRHSP eta heta sol w c v τ| ≤
      (1 / (Fintype.card UniversalLocalView : ℝ)) *
        (CrD / gamma + selectorMU_activeCr Mcy κ₀ τ * DeltaD / gamma ^ 2) := by
  classical
  let card : ℝ := Fintype.card UniversalLocalView
  let cr : ℝ := selectorMU_activeCr Mcy κ₀ τ
  let crD : ℝ := selectorMU_activeCrDeriv Mcy κ₀ τ
  let delta : ℝ :=
    selectorMU_activeCgP (p := p) Mcy g₀ τ *
      (universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ))
  let deltaD : ℝ :=
    selectorMU_activeCgDerivP (p := p) Mcy g₀ τ *
        (universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ)) +
      selectorMU_activeCgP (p := p) Mcy g₀ τ *
        (selectorMU_universalPvalDerivRHSP eta heta sol w c τ -
          selectorMU_universalPvalDerivRHSP eta heta sol w v τ)
  have hcard_pos : 0 < card := by
    dsimp [card]
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨defaultLocalViewU⟩ :
        0 < Fintype.card UniversalLocalView)
  have hqss_eq :
      selectorMU_activeQSSDerivRHSP eta heta sol w c v τ =
        (1 / card) * ((crD * delta - cr * deltaD) / (cr + delta) ^ 2) := by
    dsimp [selectorMU_activeQSSDerivRHSP, selectorMU_activeSinkDerivRHSP,
      selectorMU_activeSinkP, card, cr, crD, delta, deltaD]
    ring
  have hbase :=
    selectorMU_activeQSSDeriv_abs_le_rho_delta
      (N := card) (gamma := gamma) (rho := cr) (rhoD := crD)
      (delta := delta) (deltaD := deltaD)
      hcard_pos hgamma_pos (by simpa [cr] using hcr_nonneg)
      (by simpa [delta] using hdelta_floor)
  have hcore :
      |crD| / gamma + cr * |deltaD| / gamma ^ 2 ≤
        CrD / gamma + cr * DeltaD / gamma ^ 2 := by
    have hgamma2_nonneg : 0 ≤ gamma ^ 2 := sq_nonneg gamma
    exact add_le_add
      (div_le_div_of_nonneg_right (by simpa [crD] using hcrD) hgamma_pos.le)
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by simpa [deltaD] using hdeltaD)
          (by simpa [cr] using hcr_nonneg))
        hgamma2_nonneg)
  have hNinv_nonneg : 0 ≤ 1 / card := by positivity
  calc
    |selectorMU_activeQSSDerivRHSP eta heta sol w c v τ|
        = |(1 / card) *
            ((crD * delta - cr * deltaD) / (cr + delta) ^ 2)| := by
              rw [hqss_eq]
    _ ≤ (1 / card) * (|crD| / gamma + cr * |deltaD| / gamma ^ 2) := hbase
    _ ≤ (1 / card) * (CrD / gamma + cr * DeltaD / gamma ^ 2) :=
        mul_le_mul_of_nonneg_left hcore hNinv_nonneg
    _ = (1 / (Fintype.card UniversalLocalView : ℝ)) *
          (CrD / gamma +
            selectorMU_activeCr Mcy κ₀ τ * DeltaD / gamma ^ 2) := by
        rfl

theorem selectorMU_activeQSSDerivRHS_abs_le_of_gap_and_pvalDeriv_boundsP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ)
    {gamma CrD CgD GapB PGapD : ℝ}
    (hgamma_pos : 0 < gamma)
    (hcr_nonneg : 0 ≤ selectorMU_activeCr Mcy κ₀ τ)
    (hcg_nonneg : 0 ≤ selectorMU_activeCgP (p := p) Mcy g₀ τ)
    (hdelta_floor :
      gamma ≤ selectorMU_activeCgP (p := p) Mcy g₀ τ *
        (universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ)))
    (hcrD : |selectorMU_activeCrDeriv Mcy κ₀ τ| ≤ CrD)
    (hcgD : |selectorMU_activeCgDerivP (p := p) Mcy g₀ τ| ≤ CgD)
    (hgapB :
      |universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)| ≤ GapB)
    (hpGapD :
      |selectorMU_universalPvalDerivRHSP eta heta sol w c τ -
        selectorMU_universalPvalDerivRHSP eta heta sol w v τ| ≤ PGapD) :
    |selectorMU_activeQSSDerivRHSP eta heta sol w c v τ| ≤
      (1 / (Fintype.card UniversalLocalView : ℝ)) *
        (CrD / gamma + selectorMU_activeCr Mcy κ₀ τ *
          (CgD * GapB +
            selectorMU_activeCgP (p := p) Mcy g₀ τ * PGapD) /
            gamma ^ 2) := by
  let gap : ℝ :=
    universalPval eta heta c ((sol w).u τ) -
      universalPval eta heta v ((sol w).u τ)
  let pGapD : ℝ :=
    selectorMU_universalPvalDerivRHSP eta heta sol w c τ -
      selectorMU_universalPvalDerivRHSP eta heta sol w v τ
  let cg : ℝ := selectorMU_activeCgP (p := p) Mcy g₀ τ
  let cgD : ℝ := selectorMU_activeCgDerivP (p := p) Mcy g₀ τ
  have hCgD_nonneg : 0 ≤ CgD :=
    le_trans (abs_nonneg cgD) (by simpa [cgD] using hcgD)
  have hGapB_nonneg : 0 ≤ GapB :=
    le_trans (abs_nonneg gap) (by simpa [gap] using hgapB)
  have hterm1 : |cgD * gap| ≤ CgD * GapB := by
    rw [abs_mul]
    exact mul_le_mul (by simpa [cgD] using hcgD)
      (by simpa [gap] using hgapB) (abs_nonneg gap) hCgD_nonneg
  have hterm2 : |cg * pGapD| ≤ cg * PGapD := by
    rw [abs_mul, abs_of_nonneg hcg_nonneg]
    exact mul_le_mul le_rfl (by simpa [pGapD] using hpGapD)
      (abs_nonneg pGapD) hcg_nonneg
  have hdeltaD :
      |selectorMU_activeCgDerivP (p := p) Mcy g₀ τ *
          (universalPval eta heta c ((sol w).u τ) -
            universalPval eta heta v ((sol w).u τ)) +
        selectorMU_activeCgP (p := p) Mcy g₀ τ *
          (selectorMU_universalPvalDerivRHSP eta heta sol w c τ -
            selectorMU_universalPvalDerivRHSP eta heta sol w v τ)| ≤
        CgD * GapB +
          selectorMU_activeCgP (p := p) Mcy g₀ τ * PGapD := by
    calc
      |selectorMU_activeCgDerivP (p := p) Mcy g₀ τ *
          (universalPval eta heta c ((sol w).u τ) -
            universalPval eta heta v ((sol w).u τ)) +
        selectorMU_activeCgP (p := p) Mcy g₀ τ *
          (selectorMU_universalPvalDerivRHSP eta heta sol w c τ -
            selectorMU_universalPvalDerivRHSP eta heta sol w v τ)|
          = |cgD * gap + cg * pGapD| := by rfl
      _ ≤ |cgD * gap| + |cg * pGapD| := abs_add_le _ _
      _ ≤ CgD * GapB + cg * PGapD := add_le_add hterm1 hterm2
      _ = CgD * GapB +
          selectorMU_activeCgP (p := p) Mcy g₀ τ * PGapD := by rfl
  exact
    selectorMU_activeQSSDerivRHS_abs_le_of_deltaD_boundP
      eta heta (sol := sol) w c v τ
      hgamma_pos hcr_nonneg hdelta_floor hcrD hdeltaD

theorem selectorMU_activeQSSDerivRHS_abs_le_of_utube_uRHS_boundsP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ)
    (cfg : UConf) {ρ gamma CrD CgD GapB URhs : ℝ}
    (hρ0 : 0 ≤ ρ)
    (hgamma_pos : 0 < gamma)
    (hcr_nonneg : 0 ≤ selectorMU_activeCr Mcy κ₀ τ)
    (hcg_nonneg : 0 ≤ selectorMU_activeCgP (p := p) Mcy g₀ τ)
    (hdelta_floor :
      gamma ≤ selectorMU_activeCgP (p := p) Mcy g₀ τ *
        (universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ)))
    (hcrD : |selectorMU_activeCrDeriv Mcy κ₀ τ| ≤ CrD)
    (hcgD : |selectorMU_activeCgDerivP (p := p) Mcy g₀ τ| ≤ CgD)
    (hgapB :
      |universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)| ≤ GapB)
    (hutube : UTube ρ cfg ((sol w).u τ))
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHSP sol w τ i| ≤ URhs) :
    |selectorMU_activeQSSDerivRHSP eta heta sol w c v τ| ≤
      (1 / (Fintype.card UniversalLocalView : ℝ)) *
        (CrD / gamma + selectorMU_activeCr Mcy κ₀ τ *
          (CgD * GapB + selectorMU_activeCgP (p := p) Mcy g₀ τ *
            ((selectorMU_pvalGradBoxBound eta heta c
                (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|) +
              selectorMU_pvalGradBoxBound eta heta v
                (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|)) * URhs)) /
            gamma ^ 2) := by
  have hpGapD :=
    selectorMU_universalPvalGapDerivRHS_abs_le_utube_gradBoxBound_mul_uniform_uRHSP
      eta heta (sol := sol) w c v τ cfg ρ hρ0 hutube huRHS
  exact
    selectorMU_activeQSSDerivRHS_abs_le_of_gap_and_pvalDeriv_boundsP
      eta heta (sol := sol) w c v τ hgamma_pos hcr_nonneg hcg_nonneg
      hdelta_floor hcrD hcgD hgapB hpGapD

theorem selectorMU_activeQSS_hasDerivAt_of_sol_u_hasDerivAtP
    {p : DynGateParams} {eta : ℚ} {heta : 0 < eta}
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀}
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c v : UniversalLocalView) {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j))
    (hdelta_nonneg :
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    HasDerivAt
      (fun s => selectorMU_activeQSSP eta heta sol w c v s)
      (selectorMU_activeQSSDerivRHSP eta heta sol w c v τ) τ := by
  classical
  have hτ0 : 0 ≤ τ := by
    exact le_trans (selectorMUWriteStartTime_nonneg j)
      (le_trans (selectorMUWriteStart_le_earlySubStart j) hτ.1)
  have hdom : τ ∈ selectorSchedule.domain :=
    selectorSchedule_domain_of_nonneg_structural τ hτ0
  have hcr_diff :
      DifferentiableAt ℝ (fun s : ℝ => selectorMU_activeCr Mcy κ₀ s) τ := by
    dsimp [selectorMU_activeCr]
    fun_prop
  have hcg_diff :
      DifferentiableAt ℝ
        (fun s : ℝ => selectorMU_activeCgP (p := p) Mcy g₀ s) τ := by
    dsimp [selectorMU_activeCgP]
    fun_prop
  have hcr :
      HasDerivAt (fun s : ℝ => selectorMU_activeCr Mcy κ₀ s)
        (selectorMU_activeCrDeriv Mcy κ₀ τ) τ := by
    simpa [selectorMU_activeCrDeriv] using hcr_diff.hasDerivAt
  have hcg :
      HasDerivAt (fun s : ℝ => selectorMU_activeCgP (p := p) Mcy g₀ s)
        (selectorMU_activeCgDerivP (p := p) Mcy g₀ τ) τ := by
    simpa [selectorMU_activeCgDerivP] using hcg_diff.hasDerivAt
  have hdelta :
      HasDerivAt
        (fun s =>
          universalPval eta heta c ((sol w).u s) -
            universalPval eta heta v ((sol w).u s))
        (selectorMU_universalPvalDerivRHSP eta heta sol w c τ -
          selectorMU_universalPvalDerivRHSP eta heta sol w v τ) τ :=
    selectorMU_universalPval_gap_hasDerivAt_of_sol_u_hasDerivAtP
      (sol := sol) w c v hdom
  have hk :
      HasDerivAt
        (fun s => selectorMU_activeSinkP eta heta sol w c v s)
        (selectorMU_activeSinkDerivRHSP eta heta sol w c v τ) τ := by
    convert hcr.add (hcg.mul hdelta) using 1
    simp [selectorMU_activeSinkDerivRHSP]
    ring
  have hr :
      HasDerivAt
        (fun s => selectorMU_activeCr Mcy κ₀ s *
          (Fintype.card UniversalLocalView : ℝ)⁻¹)
        (selectorMU_activeCrDeriv Mcy κ₀ τ *
          (Fintype.card UniversalLocalView : ℝ)⁻¹) τ :=
    hcr.mul_const _
  have hk_pos : 0 < selectorMU_activeSinkP eta heta sol w c v τ := by
    simpa [selectorMU_activeSinkP, selectorMU_activeCgP] using
      selectorMU_activeSuffix_sinkCoeff_pos_of_gap_nonnegP
        (p := p) (Mcy := Mcy) (κ₀ := κ₀) (g₀ := g₀)
        hκ₀_pos hg₀_nonneg j hτ hdelta_nonneg
  have hq := hr.div hk (ne_of_gt hk_pos)
  simpa [selectorMU_activeQSSP, selectorMU_activeQSSDerivRHSP, pow_two] using hq

theorem selectorMU_activeCg_continuousP
    {p : DynGateParams} (Mcy : ℕ) (g₀ : ℚ) :
    Continuous fun τ : ℝ => selectorMU_activeCgP (p := p) Mcy g₀ τ := by
  dsimp [selectorMU_activeCgP]
  fun_prop

theorem selectorMU_activeCgDeriv_continuousP
    {p : DynGateParams} (Mcy : ℕ) (g₀ : ℚ) :
    Continuous fun τ : ℝ => selectorMU_activeCgDerivP (p := p) Mcy g₀ τ := by
  have hcd :
      ContDiff ℝ 1
        (fun τ : ℝ => selectorMU_activeCgP (p := p) Mcy g₀ τ) := by
    dsimp [selectorMU_activeCgP]
    fun_prop
  simpa [selectorMU_activeCgDerivP] using hcd.continuous_deriv le_rfl

theorem selectorMU_activeSink_continuousP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) :
    Continuous fun τ : ℝ => selectorMU_activeSinkP eta heta sol w c v τ := by
  have hcr := selectorMU_activeCr_continuous Mcy κ₀
  have hcg := selectorMU_activeCg_continuousP (p := p) Mcy g₀
  have hdelta :
      Continuous fun τ : ℝ =>
        universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ) :=
    (universalPval_continuous_of_cont_u
      eta heta c (fun i => (sol w).cont_u i)).sub
      (universalPval_continuous_of_cont_u
        eta heta v (fun i => (sol w).cont_u i))
  simpa [selectorMU_activeSinkP] using hcr.add (hcg.mul hdelta)

theorem selectorMU_activeSinkDerivRHS_continuousP
    {p : DynGateParams} (eta : ℚ) (heta : 0 < eta)
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) :
    Continuous fun τ : ℝ =>
      selectorMU_activeSinkDerivRHSP eta heta sol w c v τ := by
  have hcrD := selectorMU_activeCrDeriv_continuous Mcy κ₀
  have hcgD := selectorMU_activeCgDeriv_continuousP (p := p) Mcy g₀
  have hcg := selectorMU_activeCg_continuousP (p := p) Mcy g₀
  have hdelta :
      Continuous fun τ : ℝ =>
        universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ) :=
    (universalPval_continuous_of_cont_u
      eta heta c (fun i => (sol w).cont_u i)).sub
      (universalPval_continuous_of_cont_u
        eta heta v (fun i => (sol w).cont_u i))
  have hdeltaD :
      Continuous fun τ : ℝ =>
        selectorMU_universalPvalDerivRHSP eta heta sol w c τ -
          selectorMU_universalPvalDerivRHSP eta heta sol w v τ :=
    (selectorMU_universalPvalDerivRHS_continuousP eta heta sol w c).sub
      (selectorMU_universalPvalDerivRHS_continuousP eta heta sol w v)
  simpa [selectorMU_activeSinkDerivRHSP, add_assoc] using
    hcrD.add ((hcgD.mul hdelta).add (hcg.mul hdeltaD))

section SanityCheck

variable {p : DynGateParams}

example (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamilyP p eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ) :
    selectorMU_activeQSSP eta heta sol w c v τ =
      selectorMU_activeQSSP eta heta sol w c v τ := rfl

example (Mcy : ℕ) (g₀ : ℚ) (τ : ℝ) :
    selectorMU_activeCgP (p := bgpParams38) Mcy g₀ τ =
      selectorMU_activeCg Mcy g₀ τ := rfl

end SanityCheck

end Ripple.BoundedUniversality.BGP

/-
  Ripple.LPP.LiftedStability — Lifted z-Space Stability via Graph Contraction

  The z-side contraction uses `GraphContractingOn` — contraction along the
  reference path ψ(t) = φ(x_MF(t)), NOT full pairwise contraction between
  arbitrary z, z' (which may be false for Stage-4 PLPP drifts).

  Two construction routes:
  1. `lifted_iss_from_graph_contracting`: direct graph contraction
  2. `lifted_iss_from_quadratic_lyapunov`: joint Lyapunov V(z, z̃)

  The final product is `LiftedISSCertificate`, which the composition
  theorem (MeanFieldLogHorizon.lean) consumes as a black box.
-/

import Ripple.Analysis.StableGronwall
import Ripple.LPP.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Ripple.LPP

open Set Real Ripple.Analysis Filter

private lemma gronwallBound_neg_eq_local {δ η ε x : ℝ} (hη : 0 < η) :
    gronwallBound δ (-η) ε x =
      δ * exp (-η * x) + (ε / η) * (1 - exp (-η * x)) := by
  unfold gronwallBound
  rw [if_neg (by linarith : (-η : ℝ) ≠ 0)]
  ring

private lemma hasDerivWithinAt_norm_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : ℝ → E} {g' : E} {t : ℝ}
    (hg : HasDerivWithinAt g g' (Ici t) t) (hgt : g t ≠ 0) :
    HasDerivWithinAt (fun s => ‖g s‖)
      (@inner ℝ E _ (g t) g' / ‖g t‖) (Ici t) t := by
  have hsq : HasDerivWithinAt (fun s => ‖g s‖ ^ 2)
      (2 * @inner ℝ E _ (g t) g') (Ici t) t := by
    simpa using hg.norm_sq
  have hsq_ne : ‖g t‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hgt)
  have hsqrt := hsq.sqrt hsq_ne
  convert hsqrt using 1
  · ext s
    exact (Real.sqrt_sq (norm_nonneg (g s))).symm
  · rw [Real.sqrt_sq (norm_nonneg (g t))]
    field_simp [norm_ne_zero_iff.mpr hgt]

/-! ## Graph contraction predicate -/

/-- Contraction of drift bZ along a reference trajectory ψ.
    ⟨z - ψ(t), bZ(z) - bZ(ψ(t))⟩ ≤ -η · ‖z - ψ(t)‖²
    for all z in S, for all t in [a, T). -/
def GraphContractingOn
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (bZ : Z → Z) (ψ : ℝ → Z) (S : Set Z) (η : ℝ) (a T : ℝ) : Prop :=
  ∀ t ∈ Ico a T, ∀ z ∈ S,
    @inner ℝ Z _ (z - ψ t) (bZ z - bZ (ψ t)) ≤ -η * ‖z - ψ t‖ ^ 2

/-! ## Auxiliary predicates -/

/-- The reference trajectory ψ satisfies ψ'(t) = bZ(ψ(t)). -/
def IsReferenceSolution
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (bZ : Z → Z) (ψ : ℝ → Z) (a T : ℝ) : Prop :=
  ContinuousOn ψ (Icc a T) ∧
  ∀ t ∈ Ico a T, HasDerivWithinAt ψ (bZ (ψ t)) (Ici t) t

/-- A trajectory y with residual e: (y - e)' = bZ(y). -/
def ResidualTrajectory
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (bZ : Z → Z) (y e : ℝ → Z) (a T : ℝ) : Prop :=
  ContinuousOn (fun t => y t - e t) (Icc a T) ∧
  e a = 0 ∧
  ∀ t ∈ Ico a T,
    HasDerivWithinAt (fun s => y s - e s) (bZ (y t)) (Ici t) t

private theorem graph_shadowing_with_residual
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ Z]
    {bZ : Z → Z} {ψ : ℝ → Z} {S : Set Z}
    {y e : ℝ → Z} {a T η L δ : ℝ}
    (hη : 0 < η) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hcontract : GraphContractingOn bZ ψ S η a T)
    (hLip : ∀ u ∈ S, ∀ v ∈ S, ‖bZ u - bZ v‖ ≤ L * ‖u - v‖)
    (hy_mem : ∀ t ∈ Icc a T, y t ∈ S)
    (hw_mem : ∀ t ∈ Icc a T, y t - e t ∈ S)
    (hψ_cont : ContinuousOn ψ (Icc a T))
    (hw_cont : ContinuousOn (fun t => y t - e t) (Icc a T))
    (hψ_deriv : ∀ t ∈ Ico a T,
      HasDerivWithinAt ψ (bZ (ψ t)) (Ici t) t)
    (hw_deriv : ∀ t ∈ Ico a T,
      HasDerivWithinAt (fun s => y s - e s) (bZ (y t)) (Ici t) t)
    (he0 : e a = 0)
    (he_bound : ∀ t ∈ Icc a T, ‖e t‖ ≤ δ) :
    ∀ t ∈ Icc a T,
      ‖y t - ψ t‖ ≤
        exp (-η * (t - a)) * ‖y a - ψ a‖ + (1 + L / η) * δ := by
  set w := fun t => y t - e t with hw_def
  set g := fun t => w t - ψ t with hg_def
  set v := fun t => ‖g t‖ with hv_def
  have hw_cont' : ContinuousOn w (Icc a T) := by
    simpa [hw_def] using hw_cont
  have hv_cont : ContinuousOn v (Icc a T) := by
    exact ContinuousOn.norm (hw_cont'.sub hψ_cont)
  have hga : g a = y a - ψ a := by
    simp [hg_def, hw_def, he0]
  have hv_gronwall : ∀ t ∈ Icc a T,
      v t ≤ gronwallBound ‖y a - ψ a‖ (-η) (L * δ) (t - a) := by
    apply le_gronwallBound_of_liminf_deriv_right_le hv_cont
      (f' := fun t => -η * v t + L * δ)
    · intro t ht r hr
      have htcc : t ∈ Icc a T := ⟨ht.1, le_of_lt ht.2⟩
      have hg_deriv : HasDerivWithinAt g (bZ (y t) - bZ (ψ t)) (Ici t) t := by
        have hw_d : HasDerivWithinAt w (bZ (y t)) (Ici t) t := by
          simpa [hw_def] using hw_deriv t ht
        exact hw_d.sub (hψ_deriv t ht)
      by_cases hzero : g t = 0
      · have hvt_zero : v t = 0 := by simp [hv_def, hzero]
        have hw_eq_ψ : w t = ψ t := by
          exact sub_eq_zero.mp hzero
        have hgprime_eq : bZ (y t) - bZ (ψ t) = bZ (y t) - bZ (w t) := by
          rw [hw_eq_ψ]
        have hyw_norm : ‖y t - w t‖ = ‖e t‖ := by
          simp [hw_def]
        have h_lip :=
          hLip (y t) (hy_mem t htcc) (w t) (by simpa [hw_def] using hw_mem t htcc)
        have h_lip_delta : ‖bZ (y t) - bZ (w t)‖ ≤ L * δ := by
          calc ‖bZ (y t) - bZ (w t)‖
              ≤ L * ‖y t - w t‖ := h_lip
            _ = L * ‖e t‖ := by rw [hyw_norm]
            _ ≤ L * δ := mul_le_mul_of_nonneg_left (he_bound t htcc) hL
        have hgprime_norm_le : ‖bZ (y t) - bZ (ψ t)‖ ≤ L * δ := by
          simpa [hgprime_eq] using h_lip_delta
        have hgprime_lt : ‖bZ (y t) - bZ (ψ t)‖ < r := by
          apply lt_of_le_of_lt hgprime_norm_le
          simpa [hvt_zero] using hr
        simpa [hv_def] using hg_deriv.liminf_right_slope_norm_le hgprime_lt
      · have hnorm_pos : 0 < ‖g t‖ := norm_pos_iff.mpr hzero
        have hv_deriv : HasDerivWithinAt v
            (@inner ℝ Z _ (g t) (bZ (y t) - bZ (ψ t)) / ‖g t‖) (Ici t) t := by
          simpa [hv_def] using hasDerivWithinAt_norm_of_ne_zero hg_deriv hzero
        have hwS : w t ∈ S := by simpa [hw_def] using hw_mem t htcc
        have hcontract_t := hcontract t ht (w t) hwS
        have hcontract_g :
            @inner ℝ Z _ (g t) (bZ (w t) - bZ (ψ t)) ≤ -η * ‖g t‖ ^ 2 := by
          simpa [hg_def] using hcontract_t
        have h_lip := hLip (y t) (hy_mem t htcc) (w t) hwS
        have hyw_norm : ‖y t - w t‖ = ‖e t‖ := by
          simp [hw_def]
        have h_lip_delta : ‖bZ (y t) - bZ (w t)‖ ≤ L * δ := by
          calc ‖bZ (y t) - bZ (w t)‖
              ≤ L * ‖y t - w t‖ := h_lip
            _ = L * ‖e t‖ := by rw [hyw_norm]
            _ ≤ L * δ := mul_le_mul_of_nonneg_left (he_bound t htcc) hL
        have hres_inner :
            @inner ℝ Z _ (g t) (bZ (y t) - bZ (w t)) ≤ ‖g t‖ * (L * δ) := by
          calc @inner ℝ Z _ (g t) (bZ (y t) - bZ (w t))
              ≤ ‖g t‖ * ‖bZ (y t) - bZ (w t)‖ := real_inner_le_norm _ _
            _ ≤ ‖g t‖ * (L * δ) :=
                mul_le_mul_of_nonneg_left h_lip_delta (norm_nonneg _)
        have hsplit : bZ (y t) - bZ (ψ t) =
            (bZ (w t) - bZ (ψ t)) + (bZ (y t) - bZ (w t)) := by
          abel
        have hinner_total :
            @inner ℝ Z _ (g t) (bZ (y t) - bZ (ψ t)) ≤
              -η * ‖g t‖ ^ 2 + ‖g t‖ * (L * δ) := by
          rw [hsplit, inner_add_right]
          exact add_le_add hcontract_g hres_inner
        have hv_slope_le :
            @inner ℝ Z _ (g t) (bZ (y t) - bZ (ψ t)) / ‖g t‖ ≤
              -η * v t + L * δ := by
          calc @inner ℝ Z _ (g t) (bZ (y t) - bZ (ψ t)) / ‖g t‖
              ≤ (-η * ‖g t‖ ^ 2 + ‖g t‖ * (L * δ)) / ‖g t‖ :=
                  div_le_div_of_nonneg_right hinner_total (le_of_lt hnorm_pos)
            _ = -η * v t + L * δ := by
              rw [hv_def]
              field_simp [ne_of_gt hnorm_pos]
        exact hv_deriv.liminf_right_slope_le (lt_of_le_of_lt hv_slope_le hr)
    · simp [hv_def, hga]
    · intro t _ht
      exact le_refl _
  intro t ht
  have hgt_bound := hv_gronwall t ht
  rw [gronwallBound_neg_eq_local hη] at hgt_bound
  have het := he_bound t ht
  have hye : y t - ψ t = g t + e t := by
    simp [hg_def, hw_def]
    abel
  rw [hye]
  have hta : a ≤ t := ht.1
  have hexp_le : exp (-η * (t - a)) ≤ 1 :=
    exp_le_one_iff.mpr (by nlinarith)
  have hLdη : 0 ≤ L * δ / η := by
    exact div_nonneg (mul_nonneg hL hδ) (le_of_lt hη)
  have h_1mexp :
      0 ≤ 1 - exp (-η * (t - a)) ∧ 1 - exp (-η * (t - a)) ≤ 1 :=
    ⟨by linarith [exp_nonneg (-η * (t - a)), hexp_le],
      by linarith [exp_nonneg (-η * (t - a))]⟩
  calc ‖g t + e t‖
      ≤ ‖g t‖ + ‖e t‖ := norm_add_le _ _
    _ ≤ v t + δ := add_le_add (le_refl _) het
    _ ≤ (‖y a - ψ a‖ * exp (-η * (t - a))
        + L * δ / η * (1 - exp (-η * (t - a)))) + δ := by
        linarith [hgt_bound]
    _ ≤ (‖y a - ψ a‖ * exp (-η * (t - a)) + L * δ / η) + δ := by
        have h_mono : L * δ / η * (1 - exp (-η * (t - a))) ≤ L * δ / η := by
          calc L * δ / η * (1 - exp (-η * (t - a)))
              ≤ L * δ / η * 1 := mul_le_mul_of_nonneg_left h_1mexp.2 hLdη
            _ = L * δ / η := mul_one _
        linarith [h_mono]
    _ = exp (-η * (t - a)) * ‖y a - ψ a‖ + (1 + L / η) * δ := by
        ring

/-! ## Lifted ISS certificate -/

/-- The central abstraction: input-to-state stability for the z-side
    dynamics around a reference trajectory ψ.

    Given:
    - ψ is a reference solution of bZ
    - y = w + e where w satisfies w' = bZ(y)
    - y and w = y - e remain in the certified tube S
    - ‖e(t)‖ ≤ δ for all t

    Then:
      ‖y(t) - ψ(t)‖ ≤ e^{-ηISS·(t-a)} · ‖y(a) - ψ(a)‖ + Cstab · δ -/
structure LiftedISSCertificate
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ Z]
    (bZ : Z → Z) (ψ : ℝ → Z) (S : Set Z) (ηISS Cstab : ℝ) where
  eta_pos : 0 < ηISS
  Cstab_nonneg : 0 ≤ Cstab
  shadowing :
    ∀ {a T δ : ℝ} {y e : ℝ → Z},
      a ≤ T → 0 ≤ δ →
      IsReferenceSolution bZ ψ a T →
      ResidualTrajectory bZ y e a T →
      y a ∈ S →
      (∀ t ∈ Icc a T, y t ∈ S) →
      (∀ t ∈ Icc a T, y t - e t ∈ S) →
      (∀ t ∈ Icc a T, ‖e t‖ ≤ δ) →
      ∀ t ∈ Icc a T,
        ‖y t - ψ t‖ ≤
          exp (-ηISS * (t - a)) * ‖y a - ψ a‖
          + Cstab * δ

/-- Route 1: Construct LiftedISSCertificate from GraphContractingOn. -/
theorem lifted_iss_from_graph_contracting
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ Z]
    {bZ : Z → Z} {ψ : ℝ → Z} {S : Set Z} {η L : ℝ}
    (hη : 0 < η) (hL : 0 ≤ L)
    (hcontract : ∀ a T, a ≤ T → GraphContractingOn bZ ψ S η a T)
    (hLip : ∀ u ∈ S, ∀ v ∈ S, ‖bZ u - bZ v‖ ≤ L * ‖u - v‖)
    (_hψ_mem : ∀ t, ψ t ∈ S) :
    LiftedISSCertificate bZ ψ S η (1 + L / η) := by
  constructor
  · exact hη
  · positivity
  · intro a T δ y e _hT _hδ href hres _hy0 hy_mem hw_mem he_bound
    rcases href with ⟨hψ_cont, hψ_deriv⟩
    rcases hres with ⟨hw_cont, he0, hw_deriv⟩
    exact graph_shadowing_with_residual hη hL _hδ (hcontract a T _hT) hLip
      hy_mem hw_mem hψ_cont hw_cont hψ_deriv hw_deriv he0 he_bound

/-! ## Route 2: Joint Lyapunov (for Stage-3 normal hyperbolicity) -/

/-- Quadratic Lyapunov certificate: V(z, ref) sandwiched between
    c_low‖z - ref‖² and c_high‖z - ref‖², with drift derivative
    ≤ -2η·V along bZ. -/
structure QuadraticLyapunovISS
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (bZ : Z → Z) (ψ : ℝ → Z)
    (S : Set Z) (V : Z → Z → ℝ)
    (η cLow cHigh : ℝ) where
  eta_pos : 0 < η
  cLow_pos : 0 < cLow
  cHigh_pos : 0 < cHigh
  cond_ge_one : 1 ≤ Real.sqrt (cHigh / cLow)
  lower : ∀ z ∈ S, ∀ ref ∈ S, cLow * ‖z - ref‖ ^ 2 ≤ V z ref
  upper : ∀ z ∈ S, ∀ ref ∈ S, V z ref ≤ cHigh * ‖z - ref‖ ^ 2
  deriv_drift : ∀ t, ∀ z ∈ S, ψ t ∈ S →
    @inner ℝ Z _ (z - ψ t) (bZ z - bZ (ψ t)) ≤ -2 * η * V z (ψ t)

/-- Route 2: Construct LiftedISSCertificate from QuadraticLyapunovISS. -/
theorem lifted_iss_from_quadratic_lyapunov
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ Z]
    {bZ : Z → Z} {ψ : ℝ → Z} {S : Set Z}
    {V : Z → Z → ℝ} {η cLow cHigh L : ℝ}
    (hV : QuadraticLyapunovISS bZ ψ S V η cLow cHigh)
    (hL : 0 ≤ L)
    (hLip : ∀ u ∈ S, ∀ v ∈ S, ‖bZ u - bZ v‖ ≤ L * ‖u - v‖)
    (hψ_mem : ∀ t, ψ t ∈ S) :
    LiftedISSCertificate bZ ψ S (2 * η * cLow)
      (Real.sqrt (cHigh / cLow) * (1 + L / (2 * η * cLow))) := by
  have hη' : 0 < 2 * η * cLow := by
    exact mul_pos (mul_pos (by norm_num) hV.eta_pos) hV.cLow_pos
  have hcontract :
      ∀ a T, a ≤ T → GraphContractingOn bZ ψ S (2 * η * cLow) a T := by
    intro a T _hT t ht z hz
    have hderiv := hV.deriv_drift t z hz (hψ_mem t)
    have hlower := hV.lower z hz (ψ t) (hψ_mem t)
    have hcoef_nonpos : -2 * η ≤ 0 := by nlinarith [hV.eta_pos]
    have hmul := mul_le_mul_of_nonpos_left hlower hcoef_nonpos
    calc @inner ℝ Z _ (z - ψ t) (bZ z - bZ (ψ t))
        ≤ (-2 * η) * V z (ψ t) := by simpa [mul_assoc] using hderiv
      _ ≤ (-2 * η) * (cLow * ‖z - ψ t‖ ^ 2) := hmul
      _ = -(2 * η * cLow) * ‖z - ψ t‖ ^ 2 := by ring
  let baseCert := lifted_iss_from_graph_contracting hη' hL hcontract hLip hψ_mem
  constructor
  · exact baseCert.eta_pos
  ·
    have hCbase_nonneg : 0 ≤ 1 + L / (2 * η * cLow) := by
      have hfrac : 0 ≤ L / (2 * η * cLow) := div_nonneg hL (le_of_lt hη')
      linarith
    exact mul_nonneg (Real.sqrt_nonneg _) hCbase_nonneg
  · intro a T δ y e hT hδ href hres hy0 hy_mem hw_mem he_bound t ht
    have hbase := baseCert.shadowing hT hδ href hres hy0 hy_mem hw_mem he_bound t ht
    have hCbase_nonneg : 0 ≤ 1 + L / (2 * η * cLow) := by
      have hfrac : 0 ≤ L / (2 * η * cLow) := div_nonneg hL (le_of_lt hη')
      linarith
    have hCmono :
        (1 + L / (2 * η * cLow)) * δ ≤
          (Real.sqrt (cHigh / cLow) * (1 + L / (2 * η * cLow))) * δ := by
      have hscale :
          1 + L / (2 * η * cLow) ≤
            Real.sqrt (cHigh / cLow) * (1 + L / (2 * η * cLow)) := by
        calc 1 + L / (2 * η * cLow)
            = 1 * (1 + L / (2 * η * cLow)) := by ring
          _ ≤ Real.sqrt (cHigh / cLow) * (1 + L / (2 * η * cLow)) :=
              mul_le_mul_of_nonneg_right hV.cond_ge_one hCbase_nonneg
      exact mul_le_mul_of_nonneg_right hscale hδ
    have htail :
        exp (-(2 * η * cLow) * (t - a)) * ‖y a - ψ a‖
            + (1 + L / (2 * η * cLow)) * δ ≤
          exp (-(2 * η * cLow) * (t - a)) * ‖y a - ψ a‖
            + (Real.sqrt (cHigh / cLow) * (1 + L / (2 * η * cLow))) * δ :=
      add_le_add (le_refl _) hCmono
    exact hbase.trans htail

/-! ## Graph contraction: sufficient conditions -/

/-- Simple sufficient condition: if bZ is globally one-sided contracting
    on S, then GraphContractingOn holds along any reference trajectory
    ψ with values in S. This bypasses the tangent/transverse decomposition
    at the cost of a stronger hypothesis. -/
theorem graph_contracting_of_oneSided
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    {bZ : Z → Z} {ψ : ℝ → Z} {S : Set Z} {η : ℝ}
    (hψ_mem : ∀ t, ψ t ∈ S)
    (hcontract : OneSidedContractingOn bZ S η) :
    ∀ a T, a ≤ T → GraphContractingOn bZ ψ S η a T := by
  intro a T _ t _ht z hz
  exact hcontract hz (hψ_mem t)

/-- Tangent + transverse decomposition: derive GraphContractingOn from
    x-side contraction (via readout R and embedding φ) and an explicit
    transverse contraction certificate. The transverse hypothesis is the
    quantitative normal-hyperbolicity estimate from the PLPP structure. -/
theorem graph_contracting_from_tangent_and_transverse
    {Z X : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {bZ : Z → Z} {bX : X → X}
    {φ : X → Z} {R : Z → X}
    {ψ : ℝ → Z} {xMF : ℝ → X}
    {SZ : Set Z} {SX : Set X}
    {η_x η_transverse : ℝ}
    (_hη_x : 0 < η_x) (_hη_t : 0 < η_transverse)
    (hφ_lip : ∃ C, ∀ x₁ ∈ SX, ∀ x₂ ∈ SX,
      ‖φ x₁ - φ x₂‖ ≤ C * ‖x₁ - x₂‖)
    (hR_lip : ∃ C, ∀ z₁ ∈ SZ, ∀ z₂ ∈ SZ,
      ‖R z₁ - R z₂‖ ≤ C * ‖z₁ - z₂‖)
    (_hcomm : ∀ z ∈ SZ, bZ (φ (R z)) = φ (bX (R z)))
    (_hx_contract : OneSidedContractingOn bX SX η_x)
    (hψ_eq : ∀ t, ψ t = φ (xMF t))
    (_hxMF_mem : ∀ t, xMF t ∈ SX)
    (h_graph_contract : ∀ t, ∀ z ∈ SZ,
      @inner ℝ Z _ (z - φ (xMF t)) (bZ z - bZ (φ (xMF t)))
        ≤ -(min η_x η_transverse) * ‖z - φ (xMF t)‖ ^ 2) :
    ∀ a T, a ≤ T →
      GraphContractingOn bZ ψ SZ (min η_x η_transverse) a T := by
  intro a T _ t ht z hz
  rw [hψ_eq t]
  exact h_graph_contract t z hz

end Ripple.LPP

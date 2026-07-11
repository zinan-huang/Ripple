/-
  Ripple.Kurtz.MeanFieldLogHorizon — Log-Horizon Tube for PLPP Kurtz Convergence

  The final composition theorem: assembles
  - StableGronwall (Round 1): deterministic shadowing with residual
  - FreedmanBound (Round 2): martingale concentration
  - LiftedStability (Round 3): z-side ISS certificate

  into the target theorem:

    P(sup_{t ∈ [0, log(N)/(2η)]} ‖Z^N(t) - ψ(t)‖_∞ > C_K·log(N)/√N) ≤ N^{-p}

  This file is intentionally small (~50 lines of proof). All hard mathematics
  lives in StableGronwall, FreedmanBound, and LiftedStability. This file
  only composes them via event inclusion.
-/

import Ripple.Analysis.StableGronwall
import Ripple.Probability.FreedmanBound
import Ripple.LPP.LiftedStability
import Ripple.Kurtz.JumpBracket

namespace Ripple.Kurtz

open Set Real MeasureTheory Ripple.Probability Ripple.LPP

/-! ## Event definitions -/

/-- Log-horizon time: T_N = log(N) / (2η). -/
noncomputable def Tlog (η : ℝ) (N : ℕ) : ℝ := log (N : ℝ) / (2 * η)

/-- Martingale threshold: δ_mart = K · log(N) / √N. -/
noncomputable def deltaMart (K : ℝ) (N : ℕ) : ℝ :=
  K * log (N : ℝ) / sqrt (N : ℝ)

/-- Tube radius: ρ = C_K · log(N) / √N. -/
noncomputable def rhoTube (CK : ℝ) (N : ℕ) : ℝ :=
  CK * log (N : ℝ) / sqrt (N : ℝ)

/-! ## Constants structure -/

/-- All constants for the log-horizon tube theorem, packaged so that
    "for sufficiently large N" algebra is localized in the construction. -/
structure PLPPLogHorizonConstants where
  etaT : ℝ
  etaISS : ℝ
  Cstab : ℝ
  CQ : ℝ
  Jjump : ℝ
  Kmart : ℝ
  C0 : ℝ
  CK : ℝ
  p : ℝ
  rTubeRadius : ℝ
  N0 : ℕ
  -- Positivity
  etaT_pos : 0 < etaT
  etaISS_pos : 0 < etaISS
  Cstab_nonneg : 0 ≤ Cstab
  CQ_pos : 0 < CQ
  Jjump_nonneg : 0 ≤ Jjump
  Kmart_pos : 0 < Kmart
  C0_pos : 0 < C0
  CK_pos : 0 < CK
  p_pos : 0 < p
  rTube_pos : 0 < rTubeRadius
  N0_pos : 0 < N0
  -- Key constraints
  Kmart_large : p + 1 < (etaT / (2 * CQ)) * Kmart ^ 2
  -- "For sufficiently large N" absorption lemmas
  CK_absorb : ∀ N : ℕ, N0 ≤ N →
    C0 / (N : ℝ) + Cstab * deltaMart Kmart N < rhoTube CK N
  tube_small : ∀ N : ℕ, N0 ≤ N →
    rhoTube CK N ≤ rTubeRadius / 2

/-! ## Bad events -/

variable {Ω : Type*} [MeasurableSpace Ω]
  {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The bad martingale event: some coordinate exceeds the threshold. -/
def MartingaleBad
    (M : ι → ℝ → Ω → ℝ) (c : PLPPLogHorizonConstants) (N : ℕ) : Set Ω :=
  {ω | ∃ t ∈ Icc 0 (Tlog c.etaT N),
    deltaMart c.Kmart N ≤ supNormFin (fun i => M i t ω)}

/-- The bad tube event: process deviates from reference by more than ρ. -/
def TubeBad
    (Z : ℝ → Ω → ι → ℝ) (ψ : ℝ → ι → ℝ)
    (c : PLPPLogHorizonConstants) (N : ℕ) : Set Ω :=
  {ω | ∃ t ∈ Icc 0 (Tlog c.etaT N),
    rhoTube c.CK N ≤ supNormFin (fun i => Z t ω i - ψ t i)}

/-! ## Pathwise ISS handshake -/

/-- The bridge from deterministic ISS to the stochastic process.
    "On the good martingale event, the shadowing bound holds." -/
structure PathwiseLogHorizonISS
    (Z : ℕ → ℝ → Ω → ι → ℝ) (M : ℕ → ι → ℝ → Ω → ℝ)
    (ψ : ℝ → ι → ℝ)
    (c : PLPPLogHorizonConstants) where
  init : ∀ N : ℕ, c.N0 ≤ N → ∀ ω : Ω,
    supNormFin (fun i => Z N 0 ω i - ψ 0 i) ≤ c.C0 / (N : ℝ)
  shadow : ∀ N : ℕ, c.N0 ≤ N → ∀ ω : Ω,
    (∀ t ∈ Icc 0 (Tlog c.etaT N),
      supNormFin (fun i => M N i t ω) ≤ deltaMart c.Kmart N) →
    ∀ t ∈ Icc 0 (Tlog c.etaT N),
      supNormFin (fun i => Z N t ω i - ψ t i)
        ≤ c.C0 / (N : ℝ) + c.Cstab * deltaMart c.Kmart N

/-! ## The final theorem -/

/-- **Log-horizon Kurtz tube for PLPP.**

    The composition: on the complement of the bad martingale event,
    PathwiseLogHorizonISS gives the tube bound; the bad martingale
    event has probability ≤ N^{-p} by Freedman. Therefore the tube
    event has probability ≤ N^{-p}.

    This is a ~50-line event-inclusion proof. -/
theorem plpp_kurtz_tube_log_horizon
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → ℝ → Ω → ι → ℝ) (M : ℕ → ι → ℝ → Ω → ℝ)
    (ψ : ℝ → ι → ℝ)
    (c : PLPPLogHorizonConstants)
    (hISS : PathwiseLogHorizonISS Z M ψ c)
    (hFreedman : ∀ N : ℕ, c.N0 ≤ N →
      prob μ (MartingaleBad (M N) c N) ≤ (N : ℝ) ^ (-c.p)) :
    ∀ N : ℕ, c.N0 ≤ N →
      prob μ (TubeBad (Z N) ψ c N) ≤ (N : ℝ) ^ (-c.p) := by
  intro N hN
  suffices hsub : TubeBad (Z N) ψ c N ⊆ MartingaleBad (M N) c N by
    have hmono : prob μ (TubeBad (Z N) ψ c N) ≤ prob μ (MartingaleBad (M N) c N) := by
      unfold prob
      exact ENNReal.toReal_mono (ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
        (μ.mono (Set.subset_univ _))) (μ.mono hsub)
    exact hmono.trans (hFreedman N hN)
  intro ω hTube
  by_contra hNotBad
  simp only [MartingaleBad, Set.mem_setOf_eq, not_exists] at hNotBad
  push_neg at hNotBad
  have hMart_good : ∀ t ∈ Icc 0 (Tlog c.etaT N),
      supNormFin (fun i => M N i t ω) ≤ deltaMart c.Kmart N :=
    fun t ht => le_of_lt (hNotBad t ht)
  have hShadow := hISS.shadow N hN ω hMart_good
  simp only [TubeBad, Set.mem_setOf_eq] at hTube
  obtain ⟨t, ht, htube_large⟩ := hTube
  have hbound := hShadow t ht
  have habsorb := c.CK_absorb N hN
  linarith

/-- Readout-correctness corollary: if the readout R is L_R-Lipschitz,
    then the finite-N output is within L_R · ρ of the target. -/
theorem plpp_finiteN_readout_correct_log_horizon
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → ℝ → Ω → ι → ℝ) (M : ℕ → ι → ℝ → Ω → ℝ)
    (ψ : ℝ → ι → ℝ)
    (R : (ι → ℝ) → ℝ) (LR : ℝ)
    (hR_lip : ∀ x y : ι → ℝ, |R x - R y| ≤ LR * supNormFin (fun i => x i - y i))
    (ν : ℝ) (hν : ∀ t, R (ψ t) = ν)
    (c : PLPPLogHorizonConstants)
    (hISS : PathwiseLogHorizonISS Z M ψ c)
    (hFreedman : ∀ N : ℕ, c.N0 ≤ N →
      prob μ (MartingaleBad (M N) c N) ≤ (N : ℝ) ^ (-c.p)) :
    ∀ N : ℕ, c.N0 ≤ N →
      prob μ
        {ω | |R (Z N (Tlog c.etaT N) ω) - ν| > LR * rhoTube c.CK N}
        ≤ (N : ℝ) ^ (-c.p) := by
  intro N hN
  suffices hsub :
      {ω | |R (Z N (Tlog c.etaT N) ω) - ν| > LR * rhoTube c.CK N}
        ⊆ TubeBad (Z N) ψ c N by
    have hmono :
        prob μ
          {ω | |R (Z N (Tlog c.etaT N) ω) - ν| > LR * rhoTube c.CK N}
          ≤ prob μ (TubeBad (Z N) ψ c N) := by
      unfold prob
      exact ENNReal.toReal_mono (ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
        (μ.mono (Set.subset_univ _))) (μ.mono hsub)
    exact hmono.trans (plpp_kurtz_tube_log_horizon μ Z M ψ c hISS hFreedman N hN)
  intro ω hread_bad
  simp only [Set.mem_setOf_eq] at hread_bad
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le c.N0_pos hN
  have hT_nonneg : 0 ≤ Tlog c.etaT N := by
    unfold Tlog
    have hN_one : 1 ≤ (N : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hN_pos)
    have hlog_nonneg : 0 ≤ log (N : ℝ) := Real.log_nonneg hN_one
    have heta_nonneg : 0 ≤ 2 * c.etaT := by linarith [c.etaT_pos]
    exact div_nonneg hlog_nonneg heta_nonneg
  by_contra hnot_tube
  simp only [TubeBad, Set.mem_setOf_eq, not_exists] at hnot_tube
  push_neg at hnot_tube
  have hsup_lt :
      supNormFin (fun i => Z N (Tlog c.etaT N) ω i - ψ (Tlog c.etaT N) i)
        < rhoTube c.CK N := by
    exact hnot_tube (Tlog c.etaT N) ⟨hT_nonneg, le_rfl⟩
  have hLR_nonneg : 0 ≤ LR := by
    have hlip0 := hR_lip (fun _ : ι => 0) (fun _ : ι => 1)
    have hsup_pos :
        0 < supNormFin (fun i : ι => (fun _ : ι => 0) i - (fun _ : ι => 1) i) := by
      simp [supNormFin, Finset.sup'_const]
    have hmul_nonneg :
        0 ≤ LR * supNormFin (fun i : ι => (fun _ : ι => 0) i - (fun _ : ι => 1) i) := by
      exact (abs_nonneg _).trans hlip0
    have hmul_nonneg' :
        0 ≤ supNormFin (fun i : ι => (fun _ : ι => 0) i - (fun _ : ι => 1) i) * LR := by
      rwa [mul_comm] at hmul_nonneg
    exact nonneg_of_mul_nonneg_right hmul_nonneg' hsup_pos
  have hlip :=
    hR_lip (Z N (Tlog c.etaT N) ω) (ψ (Tlog c.etaT N))
  rw [hν (Tlog c.etaT N)] at hlip
  have hmul_le :
      LR *
          supNormFin (fun i => Z N (Tlog c.etaT N) ω i - ψ (Tlog c.etaT N) i)
        ≤ LR * rhoTube c.CK N :=
    mul_le_mul_of_nonneg_left (le_of_lt hsup_lt) hLR_nonneg
  linarith

end Ripple.Kurtz

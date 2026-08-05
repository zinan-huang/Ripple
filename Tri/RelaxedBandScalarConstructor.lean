/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBandAdaptiveError

/-!
# Scalar constructor for the relaxed adaptive schedule

For every positive firing rate and every fixed odds certificate `beta > 1`,
Archimedean choices of the productive scale and clock factor discharge all
analytic side conditions.  The population-dependent obligations are exactly
the room and adverse-corner inequalities.
-/

namespace Tri

/-- Schedule constants that depend only on the fixed physical firing rate and
the fixed strict odds certificate, not on the population or rung scale. -/
structure RelaxedScheduleScalars (r : RelaxedRate) (beta : NNReal) where
  R₀ : ℕ
  C : ℕ
  hR₀ : 1 ≤ R₀
  hC : 1 ≤ C
  hmargin : (1 : NNReal) + 1 / (R₀ : NNReal) ≤ beta
  hclock : (1 : ℝ) ≤ (r.fire : ℝ) * (C : ℝ)
  habsorb :
    -Real.log (relaxedDirW beta : ℝ) ≤
      32 * (R₀ : ℝ) * Real.log (relaxedDirEta beta : ℝ)
  hrate :
    (1 : ℝ) ≤
      32 * (R₀ : ℝ) * Real.log (relaxedDirEta beta : ℝ)

/-- Positive fixed firing rate and a strict odds certificate suffice to
choose all schedule-only scalar multipliers. -/
theorem exists_relaxedScheduleScalars
    (r : RelaxedRate) (beta : NNReal)
    (hfire : 0 < r.fire)
    (hbeta : 1 < beta) :
    Nonempty (RelaxedScheduleScalars r beta) := by
  let w := relaxedDirW beta
  let eta := relaxedDirEta beta
  have hfireR : (0 : ℝ) < (r.fire : ℝ) := by
    exact_mod_cast hfire
  have hbetaR : (1 : ℝ) < (beta : ℝ) := by
    exact_mod_cast hbeta
  have hdelta : (0 : ℝ) < (beta : ℝ) - 1 := sub_pos.mpr hbetaR
  have hwR : (0 : ℝ) < (w : ℝ) := by
    dsimp only [w, relaxedDirW]
    positivity
  have hwOne : (w : ℝ) < 1 := by
    exact_mod_cast relaxedDir_w_lt_one hbeta
  have hnegLog : 0 ≤ -Real.log (w : ℝ) :=
    neg_nonneg.mpr (Real.log_nonpos hwR.le hwOne.le)
  have hetaOne : (1 : ℝ) < (eta : ℝ) := by
    exact_mod_cast relaxedDir_eta_gt_one hbeta
  have hlogEta : 0 < Real.log (eta : ℝ) :=
    Real.log_pos hetaOne
  have hden : 0 < 32 * Real.log (eta : ℝ) := by positivity
  let K : ℝ :=
    1 / ((beta : ℝ) - 1) +
      1 / (32 * Real.log (eta : ℝ)) +
      (-Real.log (w : ℝ)) /
        (32 * Real.log (eta : ℝ)) + 1
  obtain ⟨R₀, hR₀K⟩ := exists_nat_gt K
  have hKnonneg : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hR₀pos : 0 < R₀ := by
    have : (0 : ℝ) < (R₀ : ℝ) := hKnonneg.trans_lt hR₀K
    exact_mod_cast this
  have hR₀ : 1 ≤ R₀ := by omega
  have hmarginBound :
      1 / ((beta : ℝ) - 1) < (R₀ : ℝ) := by
    have h₁ : 0 ≤ 1 / (32 * Real.log (eta : ℝ)) := by positivity
    have h₂ :
        0 ≤ (-Real.log (w : ℝ)) /
          (32 * Real.log (eta : ℝ)) := by positivity
    dsimp only [K] at hR₀K
    linarith
  have hrateBound :
      1 / (32 * Real.log (eta : ℝ)) < (R₀ : ℝ) := by
    have h₀ : 0 ≤ 1 / ((beta : ℝ) - 1) := by positivity
    have h₂ :
        0 ≤ (-Real.log (w : ℝ)) /
          (32 * Real.log (eta : ℝ)) := by positivity
    dsimp only [K] at hR₀K
    linarith
  have habsorbBound :
      (-Real.log (w : ℝ)) /
          (32 * Real.log (eta : ℝ)) < (R₀ : ℝ) := by
    have h₀ : 0 ≤ 1 / ((beta : ℝ) - 1) := by positivity
    have h₁ : 0 ≤ 1 / (32 * Real.log (eta : ℝ)) := by positivity
    dsimp only [K] at hR₀K
    linarith
  have hmarginReal :
      (1 : ℝ) + 1 / (R₀ : ℝ) ≤ (beta : ℝ) := by
    have hR₀R : (0 : ℝ) < (R₀ : ℝ) := by exact_mod_cast hR₀pos
    have hmul :
        1 < ((beta : ℝ) - 1) * (R₀ : ℝ) := by
      have := (div_lt_iff₀ hdelta).mp hmarginBound
      nlinarith
    have hdiv :
        1 / (R₀ : ℝ) < (beta : ℝ) - 1 := by
      rw [div_lt_iff₀ hR₀R]
      nlinarith
    linarith
  have hmargin :
      (1 : NNReal) + 1 / (R₀ : NNReal) ≤ beta := by
    exact_mod_cast hmarginReal
  have hrate :
      (1 : ℝ) ≤
        32 * (R₀ : ℝ) * Real.log (eta : ℝ) := by
    have hmul := (div_lt_iff₀ hden).mp hrateBound
    nlinarith
  have habsorb :
      -Real.log (w : ℝ) ≤
        32 * (R₀ : ℝ) * Real.log (eta : ℝ) := by
    have hmul := (div_lt_iff₀ hden).mp habsorbBound
    nlinarith
  obtain ⟨C, hCbound⟩ :=
    exists_nat_gt (1 / (r.fire : ℝ) + 1)
  have hCpos : 0 < C := by
    have hrecip : 0 < 1 / (r.fire : ℝ) := by positivity
    have : (0 : ℝ) < (C : ℝ) := by linarith
    exact_mod_cast this
  have hC : 1 ≤ C := by omega
  have hclock :
      (1 : ℝ) ≤ (r.fire : ℝ) * (C : ℝ) := by
    have hbound : 1 / (r.fire : ℝ) < (C : ℝ) := by
      linarith
    have hmul := (div_lt_iff₀ hfireR).mp hbound
    nlinarith
  exact ⟨
    { R₀ := R₀
      C := C
      hR₀ := hR₀
      hC := hC
      hmargin := hmargin
      hclock := hclock
      habsorb := by simpa only [w, eta] using habsorb
      hrate := by simpa only [eta] using hrate }⟩

/-- Fixed schedule constants instantiate the full adaptive error certificate
at any population and initial scale satisfying the two finite corner
conditions. -/
def relaxedDyadicAdaptiveErrorDataOfScalars
    (r : RelaxedRate) (n P L : ℕ) (beta : NNReal)
    (S : RelaxedScheduleScalars r beta)
    (hP : 1 ≤ P) (hL : 1 ≤ L)
    (hroom : 2 * (P + L) ≤ n)
    (hbeta : 1 < beta)
    (hcorner :
      beta * (relaxedDyadicBHi P L + 1 : NNReal) ≤
        r.fire * (relaxedDyadicLower n P L + 1 : NNReal)) :
    RelaxedDyadicAdaptiveErrorData r n P :=
  { base :=
      { L := L
        R₀ := S.R₀
        C := S.C
        beta := beta
        hP := hP
        hL := hL
        hR₀ := S.hR₀
        hC := S.hC
        hroom := hroom
        hbeta1 := le_of_lt hbeta
        hmargin := S.hmargin
        hcorner := hcorner }
    hbeta := hbeta
    hclock := S.hclock
    habsorb := S.habsorb
    hrate := S.hrate }

/-- Population-dependent room and corner conditions, together with a positive
fixed firing rate and strict odds certificate, produce adaptive error data. -/
theorem exists_relaxedDyadicAdaptiveErrorData
    (r : RelaxedRate) (n P L : ℕ) (beta : NNReal)
    (hfire : 0 < r.fire)
    (hP : 1 ≤ P) (hL : 1 ≤ L)
    (hroom : 2 * (P + L) ≤ n)
    (hbeta : 1 < beta)
    (hcorner :
      beta * (relaxedDyadicBHi P L + 1 : NNReal) ≤
        r.fire * (relaxedDyadicLower n P L + 1 : NNReal)) :
    ∃ E : RelaxedDyadicAdaptiveErrorData r n P, E.base.L = L := by
  obtain ⟨S⟩ :=
    exists_relaxedScheduleScalars r beta hfire hbeta
  exact ⟨
    relaxedDyadicAdaptiveErrorDataOfScalars
      r n P L beta S hP hL hroom hbeta hcorner,
    rfl⟩

end Tri

#print axioms Tri.exists_relaxedScheduleScalars
#print axioms Tri.relaxedDyadicAdaptiveErrorDataOfScalars
#print axioms Tri.exists_relaxedDyadicAdaptiveErrorData

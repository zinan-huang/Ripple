/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedTheorem3

/-!
# Paper parameters for the relaxed protocol

The paper assumes a fixed firing rate `α`, a fixed `0 < ξ < α`, and initial
gap at least

```
(1 + ξ) * (1 - α) / (1 + α) * n.
```

We encode that condition without division, using `r.idle = 1 - r.fire`.  The
fixed odds certificate

```
beta = 1 + ξ * (1 - α) / 4
```

leaves enough constant slack to absorb a logarithmic buffer.
-/

namespace Tri

open scoped ENNReal

/-- A simple fixed strict-odds certificate below the limiting initial odds. -/
noncomputable def relaxedPaperBeta
    (r : RelaxedRate) (xi : NNReal) : NNReal :=
  1 + xi * r.idle / 4

/-- Real algebra behind the paper's buffered initial corner. -/
theorem relaxedPaper_buffered_corner_real
    (a q t n x y d L : ℝ)
    (ha0 : 0 < a) (hq0 : 0 < q)
    (ht0 : 0 < t) (hta : t < a)
    (hunit : a + q = 1)
    (hn0 : 0 ≤ n) (hL0 : 0 ≤ L)
    (hpop : x + y = n)
    (hgap : y + d ≤ x)
    (hgapScale :
      (1 + t) * q * n ≤ (1 + a) * d)
    (hbuffer : 12 * L ≤ t * q * n) :
    (1 + t * q / 4) * (y + L) ≤
      a * (x - L) := by
  let beta : ℝ := 1 + t * q / 4
  have ha1 : a ≤ 1 := by linarith
  have hq1 : q ≤ 1 := by linarith
  have ht1 : t ≤ 1 := le_trans (le_of_lt hta) ha1
  have htq0 : 0 ≤ t * q := mul_nonneg ht0.le hq0.le
  have htq1 : t * q ≤ 1 := by
    calc
      t * q ≤ 1 * 1 :=
        mul_le_mul ht1 hq1 hq0.le (by norm_num)
      _ = 1 := by norm_num
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  have habeta0 : 0 ≤ a + beta := add_nonneg ha0.le hbeta0
  have hgapD : d ≤ x - y := by linarith
  have hscaledGap :
      (a + beta) * (1 + t) * q * n ≤
        (a + beta) * (1 + a) * (x - y) := by
    calc
      (a + beta) * (1 + t) * q * n =
          (a + beta) * ((1 + t) * q * n) := by ring
      _ ≤ (a + beta) * ((1 + a) * d) :=
        mul_le_mul_of_nonneg_left hgapScale habeta0
      _ ≤ (a + beta) * ((1 + a) * (x - y)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hgapD (by linarith)
        · exact habeta0
      _ = (a + beta) * (1 + a) * (x - y) := by ring
  have hfactor : 4 ≤ 6 - 2 * q + q * t := by
    have hqt0 : 0 ≤ q * t := mul_nonneg hq0.le ht0.le
    nlinarith
  have hfactorQuarter : 1 ≤ (6 - 2 * q + q * t) / 4 := by
    linarith
  have hleftLower :
      t * q * n ≤
        (t * q * (6 - 2 * q + q * t) / 4) * n := by
    calc
      t * q * n = 1 * (t * q * n) := by ring
      _ ≤ ((6 - 2 * q + q * t) / 4) *
          (t * q * n) :=
        mul_le_mul_of_nonneg_right hfactorQuarter
          (mul_nonneg htq0 hn0)
      _ = (t * q * (6 - 2 * q + q * t) / 4) * n := by
        ring
  have halgebra :
      ((a - beta) * (1 + a) +
          (a + beta) * (1 + t) * q) * n =
        (t * q * (6 - 2 * q + q * t) / 4) * n := by
    have ha : a = 1 - q := by linarith
    rw [ha]
    dsimp only [beta]
    ring
  have hmaster :
      t * q * n ≤
        2 * (1 + a) * (a * x - beta * y) := by
    calc
      t * q * n ≤
          (t * q * (6 - 2 * q + q * t) / 4) * n :=
        hleftLower
      _ = ((a - beta) * (1 + a) +
          (a + beta) * (1 + t) * q) * n := halgebra.symm
      _ ≤ ((a - beta) * (1 + a)) * n +
          (a + beta) * (1 + a) * (x - y) := by
        calc
          _ = ((a - beta) * (1 + a)) * n +
              (a + beta) * (1 + t) * q * n := by ring
          _ ≤ ((a - beta) * (1 + a)) * n +
              (a + beta) * (1 + a) * (x - y) :=
            by
              simpa only [add_comm] using
                add_le_add_left hscaledGap
                  (((a - beta) * (1 + a)) * n)
      _ = 2 * (1 + a) * (a * x - beta * y) := by
        rw [← hpop]
        ring
  have hcoefPos : 0 < 2 * (1 + a) := by positivity
  have hslack0 : 0 ≤ a * x - beta * y := by
    apply nonneg_of_mul_nonneg_right
      (le_trans (mul_nonneg htq0 hn0) hmaster)
      hcoefPos
  have hcoefUpper : 2 * (1 + a) ≤ 4 := by linarith
  have hslackLower :
      3 * L ≤ a * x - beta * y := by
    have hfour :
        t * q * n ≤ 4 * (a * x - beta * y) := by
      exact hmaster.trans
        (mul_le_mul_of_nonneg_right hcoefUpper hslack0)
    linarith
  have habetaUpper : a + beta ≤ 3 := by
    dsimp only [beta]
    nlinarith
  have hbufferCost :
      (a + beta) * L ≤ 3 * L :=
    mul_le_mul_of_nonneg_right habetaUpper hL0
  dsimp only [beta] at hslackLower hbufferCost ⊢
  nlinarith

/-- The paper's cross-multiplied initial gap and a logarithmic-buffer size
condition imply both finite obligations used by the dyadic schedule. -/
theorem relaxedPaper_room_and_corner
    (r : RelaxedRate) (xi : NNReal)
    (n x y d L : ℕ)
    (hfire : 0 < r.fire) (hidle : 0 < r.idle)
    (hxi : 0 < xi) (hxiFire : xi < r.fire)
    (hpop : x + y = n) (hgap : y + d ≤ x)
    (hgapScale :
      (1 + xi) * r.idle * (n : NNReal) ≤
        (1 + r.fire) * (d : NNReal))
    (hbuffer :
      ((12 * L : ℕ) : NNReal) ≤
        xi * r.idle * (n : NNReal)) :
    2 * (y + L) ≤ n ∧
      relaxedPaperBeta r xi * (y + L - 1 : NNReal) ≤
        r.fire * (x - L + 1 : NNReal) := by
  have hfire1 : r.fire ≤ 1 := by
    rw [← r.add_eq_one]
    exact le_add_right le_rfl
  have hxi1 : xi ≤ 1 :=
    (le_of_lt hxiFire).trans hfire1
  have hbufferR :
      (12 : ℝ) * L ≤
        (xi : ℝ) * (r.idle : ℝ) * n := by
    exact_mod_cast hbuffer
  have hgapScaleR :
      (1 + (xi : ℝ)) * (r.idle : ℝ) * n ≤
        (1 + (r.fire : ℝ)) * d := by
    exact_mod_cast hgapScale
  have hunitR :
      (r.fire : ℝ) + (r.idle : ℝ) = 1 := by
    exact_mod_cast r.add_eq_one
  have hcornerR :=
    relaxedPaper_buffered_corner_real
      (r.fire : ℝ) (r.idle : ℝ) (xi : ℝ)
      n x y d L
      (by exact_mod_cast hfire)
      (by exact_mod_cast hidle)
      (by exact_mod_cast hxi)
      (by exact_mod_cast hxiFire)
      hunitR
      (by positivity) (by positivity)
      (by exact_mod_cast hpop)
      (by exact_mod_cast hgap)
      hgapScaleR hbufferR
  have hroom : 2 * (y + L) ≤ n := by
    have htqGap :
        (xi : ℝ) * (r.idle : ℝ) * n ≤
          (1 + (xi : ℝ)) * (r.idle : ℝ) * n := by
      have hqn :
          0 ≤ (r.idle : ℝ) * n := by positivity
      nlinarith
    have honeFire :
        (1 + (r.fire : ℝ)) * d ≤ 2 * d := by
      have : (r.fire : ℝ) ≤ 1 := by exact_mod_cast hfire1
      nlinarith
    have hLdR : (2 : ℝ) * L ≤ d := by
      linarith [hbufferR, htqGap,
        hgapScaleR, honeFire]
    have hLd : 2 * L ≤ d := by
      exact_mod_cast hLdR
    omega
  refine ⟨hroom, ?_⟩
  have hLx : L ≤ x := by
    have hnonneg :
        0 ≤ (1 + (xi : ℝ) * (r.idle : ℝ) / 4) *
          ((y : ℝ) + L) := by positivity
    have hfireR : (0 : ℝ) < (r.fire : ℝ) := by
      exact_mod_cast hfire
    by_contra h
    have hxLR : (x : ℝ) < (L : ℝ) := by
      exact_mod_cast (show x < L by omega)
    have hdiff : (x : ℝ) - L < 0 := by linarith
    have : (r.fire : ℝ) * ((x : ℝ) - L) < 0 :=
      mul_neg_of_pos_of_neg hfireR hdiff
    linarith
  have hstrong :
      relaxedPaperBeta r xi * (y + L : NNReal) ≤
        r.fire * (x - L : NNReal) := by
    exact_mod_cast hcornerR
  calc
    relaxedPaperBeta r xi * (y + L - 1 : NNReal) ≤
        relaxedPaperBeta r xi * (y + L : NNReal) := by
      gcongr
      exact_mod_cast Nat.sub_le (y + L) 1
    _ ≤ r.fire * (x - L : NNReal) := hstrong
    _ ≤ r.fire * (x - L + 1 : NNReal) := by
      gcongr
      exact_mod_cast
        (show x - L ≤ x - L + 1 by omega)

/-- Fixed schedule constants and the paper's initial gap instantiate the
complete finite raw-chain theorem. -/
theorem theorem3_relaxed_paper_finite
    (r : RelaxedRate) (xi : NNReal)
    (S : RelaxedScheduleScalars r (relaxedPaperBeta r xi))
    (n x y d L : ℕ)
    (hfire : 0 < r.fire) (hidle : 0 < r.idle)
    (hxi : 0 < xi) (hxiFire : xi < r.fire)
    (hpop : x + y = n) (hgap : y + d ≤ x)
    (hgapScale :
      (1 + xi) * r.idle * (n : NNReal) ≤
        (1 + r.fire) * (d : NNReal))
    (hy : 1 ≤ y) (hL : 1 ≤ L)
    (hbuffer :
      ((12 * L : ℕ) : NNReal) ≤
        xi * r.idle * (n : NNReal)) :
    ∃ E : RelaxedDyadicAdaptiveErrorData r n y,
      E.base.R₀ = S.R₀ ∧ E.base.C = S.C ∧ E.base.L = L ∧
      E.base.beta = relaxedPaperBeta r xi ∧
      terminalFailureMass
          (iter
            (freeze (fun z : ℕ => z = n)
              (relaxedTriChain r n))
            (relaxedDyadicAdaptiveHorizon r n y E.base)
            x)
          (fun z : ℕ => z = n) ≤
        (relaxedDyadicStageCount y : ℝ≥0∞) *
          relaxedDyadicAdaptiveRungEnvelope r n y E ∧
      relaxedDyadicAdaptiveHorizon r n y E.base ≤
        4096 * S.C * S.R₀ * n *
          (relaxedDyadicStageCount y + 2 * L) := by
  have hbeta : 1 < relaxedPaperBeta r xi := by
    unfold relaxedPaperBeta
    have hprod : 0 < xi * r.idle :=
      mul_pos hxi hidle
    have hfour : (0 : NNReal) < 4 := by norm_num
    have hdiv : 0 < xi * r.idle / 4 :=
      div_pos hprod hfour
    exact lt_add_of_pos_right 1 hdiv
  obtain ⟨hroom, hcorner⟩ :=
    relaxedPaper_room_and_corner
      r xi n x y d L hfire hidle hxi hxiFire
      hpop hgap hgapScale hbuffer
  have hbHi :
      relaxedDyadicBHi y L + 1 = y + L - 1 := by
    unfold relaxedDyadicBHi
    omega
  have hlower :
      relaxedDyadicLower n y L + 1 = x - L + 1 := by
    unfold relaxedDyadicLower
    omega
  have hcorner' :
      relaxedPaperBeta r xi *
          (relaxedDyadicBHi y L + 1 : NNReal) ≤
        r.fire *
          (relaxedDyadicLower n y L + 1 : NNReal) := by
    have hbHiNN :
        (relaxedDyadicBHi y L + 1 : NNReal) =
          (y + L - 1 : NNReal) := by
      exact_mod_cast hbHi
    have hlowerNN :
        (relaxedDyadicLower n y L + 1 : NNReal) =
          (x - L + 1 : NNReal) := by
      exact_mod_cast hlower
    rw [hbHiNN, hlowerNN]
    exact hcorner
  let E : RelaxedDyadicAdaptiveErrorData r n y :=
    relaxedDyadicAdaptiveErrorDataOfScalars
      r n y L (relaxedPaperBeta r xi) S
      hy hL hroom hbeta hcorner'
  refine ⟨E, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hstart : relaxedDyadicStart n y = x := by
      unfold relaxedDyadicStart
      omega
    simpa only [hstart] using
      relaxedDyadicAdaptive_raw_consensus_exp r n y E
  · simpa only [E] using
      relaxedDyadicAdaptiveHorizon_le r n y E.base

/-- Explicit error envelope in the paper's logarithmic buffer scale. -/
noncomputable def relaxedPaperHeadlineError
    (r : RelaxedRate) (xi : NNReal)
    (n gamma : ℕ) : ℝ≥0∞ :=
  ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) *
    (ENNReal.ofReal
        (Real.exp
          (-(((gamma * Nat.log 2 n : ℕ) : ℝ) *
            Real.log (relaxedPaperBeta r xi : ℝ)))) +
      ENNReal.ofReal
        (Real.exp (-((gamma * Nat.log 2 n : ℕ) : ℝ))) +
      ENNReal.ofReal
        (Real.exp (-((gamma * Nat.log 2 n : ℕ) : ℝ))))

/-- Paper-facing relaxed-protocol theorem with a fixed raw-interaction
constant.  The explicit buffer hypothesis is the usual sufficiently-large
population condition for fixed `r`, `xi`, and `gamma`. -/
theorem theorem3_relaxed
    (r : RelaxedRate) (xi : NNReal)
    (hfire : 0 < r.fire) (hidle : 0 < r.idle)
    (hxi : 0 < xi) (hxiFire : xi < r.fire) :
    ∃ C : ℕ, 0 < C ∧
      ∀ n gamma x y d : ℕ,
        2 ≤ n →
        1 ≤ gamma →
        x + y = n →
        y + d ≤ x →
        (1 + xi) * r.idle * (n : NNReal) ≤
          (1 + r.fire) * (d : NNReal) →
        ((12 * (gamma * Nat.log 2 n) : ℕ) : NNReal) ≤
          xi * r.idle * (n : NNReal) →
        terminalFailureMass
            (iter
              (freeze (fun z : ℕ => z = n)
                (relaxedTriChain r n))
              (C * gamma * n * Nat.log 2 n)
              x)
            (fun z : ℕ => z = n) ≤
          relaxedPaperHeadlineError r xi n gamma := by
  have hbeta : 1 < relaxedPaperBeta r xi := by
    unfold relaxedPaperBeta
    have hprod : 0 < xi * r.idle :=
      mul_pos hxi hidle
    have hfour : (0 : NNReal) < 4 := by norm_num
    exact lt_add_of_pos_right 1 (div_pos hprod hfour)
  obtain ⟨S⟩ :=
    exists_relaxedScheduleScalars
      r (relaxedPaperBeta r xi) hfire hbeta
  let C := 16384 * S.C * S.R₀
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    exact Nat.mul_pos
      (Nat.mul_pos (by norm_num)
        (lt_of_lt_of_le Nat.zero_lt_one S.hC))
      (lt_of_lt_of_le Nat.zero_lt_one S.hR₀)
  · intro n gamma x y d hn hgamma hpop hgap
      hgapScale hbuffer
    have hlog : 1 ≤ Nat.log 2 n :=
      Nat.log_pos (by norm_num) (by omega)
    by_cases hy0 : y = 0
    · have hx : x = n := by omega
      subst x
      rw [iter_targetFreeze_of_mem
        (fun z : ℕ => z = n)
        (relaxedTriChain r n) n rfl]
      rw [terminalFailureMass_eq_expect, expect_pure]
      simp
    · have hy : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy0
      let L := gamma * Nat.log 2 n
      have hL : 1 ≤ L := by
        dsimp only [L]
        exact Nat.mul_pos
          (lt_of_lt_of_le Nat.zero_lt_one hgamma)
          (lt_of_lt_of_le Nat.zero_lt_one hlog)
      obtain ⟨E, hER, hEC, hEL, hEB, hfailure, hhorizon⟩ :=
        theorem3_relaxed_paper_finite
          r xi S n x y d L hfire hidle hxi hxiFire
          hpop hgap hgapScale hy hL (by
            simpa only [L] using hbuffer)
      have hyN : y ≤ n := by omega
      have hstage :
          relaxedDyadicStageCount y ≤ Nat.log 2 n + 1 := by
        unfold relaxedDyadicStageCount
        exact Nat.add_le_add_right
          (Nat.log_mono_right (b := 2) hyN) 1
      have hfactor :
          relaxedDyadicStageCount y + 2 * L ≤
            4 * gamma * Nat.log 2 n := by
        have hlogL : Nat.log 2 n ≤ L := by
          dsimp only [L]
          simpa only [one_mul] using
            Nat.mul_le_mul_right (Nat.log 2 n) hgamma
        calc
          relaxedDyadicStageCount y + 2 * L ≤ 4 * L := by
            omega
          _ = 4 * gamma * Nat.log 2 n := by
            dsimp only [L]
            ring
      have hTU :
          relaxedDyadicAdaptiveHorizon r n y E.base ≤
            C * gamma * n * Nat.log 2 n := by
        calc
          relaxedDyadicAdaptiveHorizon r n y E.base ≤
              4096 * S.C * S.R₀ * n *
                (relaxedDyadicStageCount y + 2 * L) :=
            hhorizon
          _ ≤ 4096 * S.C * S.R₀ * n *
                (4 * gamma * Nat.log 2 n) :=
            Nat.mul_le_mul_left
              (4096 * S.C * S.R₀ * n) hfactor
          _ = C * gamma * n * Nat.log 2 n := by
            dsimp only [C]
            ring
      have hpadded :=
        terminalFailureMass_iter_freeze_antitone_of_subset
          (fun z : ℕ => z = n) (fun z : ℕ => z = n)
          (relaxedTriChain r n) (fun _ hz => hz)
          (relaxedDyadicAdaptiveHorizon r n y E.base)
          (C * gamma * n * Nat.log 2 n) hTU x
      have hstageE :
          (relaxedDyadicStageCount y : ℝ≥0∞) ≤
            ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hstage
      calc
        terminalFailureMass
            (iter
              (freeze (fun z : ℕ => z = n)
                (relaxedTriChain r n))
              (C * gamma * n * Nat.log 2 n)
              x)
            (fun z : ℕ => z = n) ≤
            terminalFailureMass
              (iter
                (freeze (fun z : ℕ => z = n)
                  (relaxedTriChain r n))
                (relaxedDyadicAdaptiveHorizon r n y E.base)
                x)
              (fun z : ℕ => z = n) :=
          hpadded
        _ ≤ (relaxedDyadicStageCount y : ℝ≥0∞) *
              relaxedDyadicAdaptiveRungEnvelope r n y E :=
          hfailure
        _ ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) *
              relaxedDyadicAdaptiveRungEnvelope r n y E :=
          mul_le_mul_right' hstageE _
        _ = relaxedPaperHeadlineError r xi n gamma := by
          unfold relaxedPaperHeadlineError
          unfold relaxedDyadicAdaptiveRungEnvelope
          rw [hEL, hEB]

end Tri

#print axioms Tri.relaxedPaper_buffered_corner_real
#print axioms Tri.relaxedPaper_room_and_corner
#print axioms Tri.theorem3_relaxed_paper_finite
#print axioms Tri.theorem3_relaxed

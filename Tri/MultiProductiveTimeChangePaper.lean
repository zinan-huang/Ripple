/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveTimeChange
import Tri.MultiProductiveClockConstants

/-!
# Paper phase-0 specialization of the productive time change

This file instantiates the generic stopped countdown at the paper's
`1/(108m)` productive-mass floor and the raw deadline used by Lemma 13.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- Configuration-only form of the phase-0 clock boundary. -/
def PaperPhase0ConfigBoundary
    (X : Species m) (D : ℕ) (c : Config m n) : Prop :=
  ¬ (IsMaxSpecies c X ∧ count c X ≤ zSum c X + D)

noncomputable instance paperPhase0ConfigBoundaryDecidable
    (X : Species m) (D : ℕ) :
    DecidablePred (PaperPhase0ConfigBoundary (n := n) X D) :=
  Classical.decPred _

theorem paperPhase0ConfigBoundary_iff
    (X : Species m) (D : ℕ) (q : Config m n × ℕ) :
    PaperPhase0ConfigBoundary X D q.1 ↔
      PaperPhase0ClockBoundary X D q :=
  Iff.rfl

/-- Reciprocal identity used to reuse the scalar clock estimate. -/
theorem two_pow_eq_one_div_half_pow (M : ℕ) :
    (2 : ℝ≥0∞) ^ M =
      1 / (((1 : ℝ≥0∞) / 2) ^ M) := by
  rw [one_div, ENNReal.inv_pow]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff'
    (by finiteness) (ENNReal.inv_ne_top.mpr (by norm_num))).mp
  norm_num

/-- The paper phase-0 floor holds at every live configuration. -/
theorem paperPhase0Config_productiveFloor
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (hD : 3 * D ≤ n) (hnm : 6 * m ≤ n) :
    ∀ c, ¬ PaperPhase0ConfigBoundary X D c →
      (1 : ℝ≥0∞) / (108 * m : ℕ) ≤ productiveMass c h3 := by
  intro c hc
  have hlive :
      IsMaxSpecies c X ∧ count c X ≤ zSum c X + D :=
    Classical.not_not.mp hc
  exact one_div_108_species_le_productiveMass
    c X D h3 hlive.1 hlive.2 hD hnm

/-- Lemma 13's exponential raw deadline remains valid after enlarging the
phase-0 stopping boundary. -/
theorem paperPhase0Countdown_live_deadline_of_boundary
    (B : Config m n → Prop) [DecidablePred B]
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (hboundary :
      ∀ c, PaperPhase0ConfigBoundary X D c → B c)
    (hD : 3 * D ≤ n) (hnm : 6 * m ≤ n)
    (M L : ℕ) (c0 : Config m n) :
    (∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then
      iter (productiveCountdownStop B h3)
        (multiPaperPhase0ClockHorizon m M L) (c0, M) q
      else 0) ≤
      ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  let p : ℝ≥0∞ := (1 : ℝ≥0∞) / (108 * m : ℕ)
  let p' : ℝ≥0∞ := 1 - p
  have hm : 1 ≤ m := by
    have := X.isLt
    omega
  have hpLe : p ≤ 1 := by
    dsimp only [p]
    have hdenNat : 1 ≤ 108 * m := by omega
    have hden : (1 : ℝ≥0∞) ≤ ((108 * m : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hdenNat
    exact ENNReal.div_le_of_le_mul (by simpa using hden)
  have hp : p + p' = 1 := by
    dsimp only [p']
    rw [add_comm]
    exact tsub_add_cancel_of_le hpLe
  have htail :=
    productiveCountdownStop_live_tail B h3 p p' hp
      (fun c hc =>
        paperPhase0Config_productiveFloor h3 X D hD hnm c
          (fun hphase => hc (hboundary c hphase)))
      (multiPaperPhase0ClockHorizon m M L) M c0
  calc
    (∑' q, if ¬ B q.1 ∧ q.2 ≠ 0 then
      iter (productiveCountdownStop B h3)
        (multiPaperPhase0ClockHorizon m M L) (c0, M) q
      else 0) ≤
      (p' + p * ((1 : ℝ≥0∞) / 2)) ^
          multiPaperPhase0ClockHorizon m M L *
        (2 : ℝ≥0∞) ^ M := htail
    _ =
      ((1 - (1 : ℝ≥0∞) / (108 * m : ℕ)) +
          ((1 : ℝ≥0∞) / (108 * m : ℕ)) *
            ((1 : ℝ≥0∞) / 2)) ^
          multiPaperPhase0ClockHorizon m M L /
        ((1 : ℝ≥0∞) / 2) ^ M := by
          rw [two_pow_eq_one_div_half_pow]
          simp only [p, p']
          simp only [div_eq_mul_inv, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(L : ℝ))) :=
      multiPaperPhase0_clock_error_le m M L hm

/-- Lemma 13's exponential raw deadline, now on the same decreasing countdown
that embeds the conditioned productive chain. -/
theorem paperPhase0Countdown_live_deadline
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (hD : 3 * D ≤ n) (hnm : 6 * m ≤ n)
    (M L : ℕ) (c0 : Config m n) :
    (∑' q, if
        ¬ PaperPhase0ConfigBoundary X D q.1 ∧ q.2 ≠ 0 then
      iter
        (productiveCountdownStop
          (PaperPhase0ConfigBoundary X D) h3)
        (multiPaperPhase0ClockHorizon m M L) (c0, M) q
      else 0) ≤
      ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  let p : ℝ≥0∞ := (1 : ℝ≥0∞) / (108 * m : ℕ)
  let p' : ℝ≥0∞ := 1 - p
  have hm : 1 ≤ m := by
    have := X.isLt
    omega
  have hpLe : p ≤ 1 := by
    dsimp only [p]
    have hdenNat : 1 ≤ 108 * m := by omega
    have hden : (1 : ℝ≥0∞) ≤ ((108 * m : ℕ) : ℝ≥0∞) := by
      exact_mod_cast hdenNat
    exact ENNReal.div_le_of_le_mul (by simpa using hden)
  have hp : p + p' = 1 := by
    dsimp only [p']
    rw [add_comm]
    exact tsub_add_cancel_of_le hpLe
  have htail :=
    productiveCountdownStop_live_tail
      (PaperPhase0ConfigBoundary X D)
      h3 p p' hp
      (paperPhase0Config_productiveFloor h3 X D hD hnm)
      (multiPaperPhase0ClockHorizon m M L) M c0
  calc
    (∑' q, if
        ¬ PaperPhase0ConfigBoundary X D q.1 ∧ q.2 ≠ 0 then
      iter
        (productiveCountdownStop
          (PaperPhase0ConfigBoundary X D) h3)
        (multiPaperPhase0ClockHorizon m M L) (c0, M) q
      else 0) ≤
      (p' + p * ((1 : ℝ≥0∞) / 2)) ^
          multiPaperPhase0ClockHorizon m M L *
        (2 : ℝ≥0∞) ^ M := htail
    _ =
      ((1 - (1 : ℝ≥0∞) / (108 * m : ℕ)) +
          ((1 : ℝ≥0∞) / (108 * m : ℕ)) *
            ((1 : ℝ≥0∞) / 2)) ^
          multiPaperPhase0ClockHorizon m M L /
        ((1 : ℝ≥0∞) / 2) ^ M := by
          rw [two_pow_eq_one_div_half_pow]
          simp only [p, p']
          simp only [div_eq_mul_inv, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(L : ℝ))) :=
      multiPaperPhase0_clock_error_le m M L hm

/-- One paper phase-0 raw block is bounded by the corresponding
boundary-stopped productive block plus Lemma 13's clock error. -/
theorem paperPhase0Countdown_failure_le
    (A : Config m n → Prop) [DecidablePred A]
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (hD : 3 * D ≤ n) (hnm : 6 * m ≤ n)
    (M L : ℕ) (c0 : Config m n) :
    terminalFailureMass
        (iter
          (productiveCountdownStop
            (PaperPhase0ConfigBoundary X D) h3)
          (multiPaperPhase0ClockHorizon m M L) (c0, M))
        (fun q => A q.1) ≤
      terminalFailureMass
          (iter
            (freeze (PaperPhase0ConfigBoundary X D)
              (productiveStep h3))
            M c0)
          A +
        ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  exact
    (productiveCountdownStop_failure_le
      A (PaperPhase0ConfigBoundary X D) h3
      (multiPaperPhase0ClockHorizon m M L) M c0).trans
      (add_le_add le_rfl
        (paperPhase0Countdown_live_deadline
          h3 X D hD hnm M L c0))

/-- Direct Lemma-12/Lemma-13 time-change interface at the paper's explicit
`288n` productive quota and `129472mn` raw deadline.  The remaining
mathematical input is precisely the failure estimate for the productive chain
stopped on the same phase-0 boundary. -/
theorem paperPhase0Countdown_failure_lemma13
    (A : Config m n → Prop) [DecidablePred A]
    (h3 : 3 ≤ n) (X : Species m) (D gamma : ℕ)
    (_hgamma : 1 ≤ gamma)
    (hD : 3 * D ≤ n)
    (hscale : 6 ≤ gamma * Nat.log 2 n)
    (hm : m * (gamma * Nat.log 2 n) ≤ n)
    (c0 : Config m n) :
    terminalFailureMass
        (iter
          (productiveCountdownStop
            (PaperPhase0ConfigBoundary X D) h3)
          (129472 * m * n) (c0, 288 * n))
        (fun q => A q.1) ≤
      terminalFailureMass
          (iter
            (freeze (PaperPhase0ConfigBoundary X D)
              (productiveStep h3))
            (288 * n) c0)
          A +
        ENNReal.ofReal
          (Real.exp (-((gamma * Nat.log 2 n : ℕ) : ℝ))) := by
  have hmPos : 1 ≤ m := by
    have := X.isLt
    omega
  have h6m : 6 * m ≤ n := by
    calc
      6 * m = m * 6 := by omega
      _ ≤ m * (gamma * Nat.log 2 n) :=
        Nat.mul_le_mul_left m hscale
      _ ≤ n := hm
  have hlog : gamma * Nat.log 2 n ≤ n := by
    calc
      gamma * Nat.log 2 n =
          1 * (gamma * Nat.log 2 n) := by omega
      _ ≤ m * (gamma * Nat.log 2 n) :=
        Nat.mul_le_mul_right (gamma * Nat.log 2 n) hmPos
      _ ≤ n := hm
  have hbridge :=
    paperPhase0Countdown_failure_le
      A h3 X D hD h6m (288 * n) n c0
  have hHorizon :
      multiPaperPhase0ClockHorizon m (288 * n) n =
        129472 * m * n := by
    simp only [multiPaperPhase0ClockHorizon, multiPhase0ClockHorizon]
    ring
  rw [hHorizon] at hbridge
  exact hbridge.trans <| add_le_add le_rfl <|
    ENNReal.ofReal_le_ofReal <| Real.exp_le_exp.mpr <| by
      have hlogR :
          ((gamma * Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hlog
      linarith

/-- Physical-chain form of the Lemma-13 bridge.  One raw phase-0 block fails
to hit `A` with at most the failure of the same-boundary productive block plus
the explicit clock error. -/
theorem paperPhase0_multiStep_failure_lemma13
    (A : Config m n → Prop) [DecidablePred A]
    (h3 : 3 ≤ n) (X : Species m) (D gamma : ℕ)
    (hgamma : 1 ≤ gamma)
    (hD : 3 * D ≤ n)
    (hscale : 6 ≤ gamma * Nat.log 2 n)
    (hm : m * (gamma * Nat.log 2 n) ≤ n)
    (c0 : Config m n) :
    terminalFailureMass
        (iter
          (freeze A (fun c => multiStep c h3))
          (129472 * m * n) c0)
        A ≤
      terminalFailureMass
          (iter
            (freeze (PaperPhase0ConfigBoundary X D)
              (productiveStep h3))
            (288 * n) c0)
          A +
        ENNReal.ofReal
          (Real.exp (-((gamma * Nat.log 2 n : ℕ) : ℝ))) := by
  exact
    (multiStep_targetFailure_le_productiveCountdownStop
      A (PaperPhase0ConfigBoundary X D) h3
      (129472 * m * n) (288 * n) c0).trans
      (paperPhase0Countdown_failure_lemma13
        A h3 X D gamma hgamma hD hscale hm c0)

end Tri.Multi

#print axioms Tri.Multi.two_pow_eq_one_div_half_pow
#print axioms Tri.Multi.paperPhase0Countdown_live_deadline_of_boundary
#print axioms Tri.Multi.paperPhase0Countdown_live_deadline
#print axioms Tri.Multi.paperPhase0Countdown_failure_le
#print axioms Tri.Multi.paperPhase0Countdown_failure_lemma13
#print axioms Tri.Multi.paperPhase0_multiStep_failure_lemma13

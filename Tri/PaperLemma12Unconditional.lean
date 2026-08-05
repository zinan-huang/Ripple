/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PaperLemma12
import Tri.MultiProductiveAmplificationUnconditional
import Tri.HitProbMono

/-!
# Unconditional paper Lemma 12

The state-dependent all-competitor estimate proves the printed proper-stage
conclusion without the coefficient-absorption hypothesis used by the older
wrapper.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- **Paper Lemma 12, unconditional in the printed species range.**

Starting from the square-root-scale global plurality gap, the productive
chain reaches the paper target `min (2Δ) n` within `288n` productive events.
The stronger internal checkpoint is `min (4Δ) n`. -/
theorem lemma12_unconditional
    (h3 : 3 ≤ n) (X : Species m) (Δ gamma : ℕ)
    (hgLarge :
      properStageHeadlineThreshold ≤ gamma * Nat.log 2 n)
    (hΔ4 : 4 ≤ Δ) (hΔn : Δ ≤ n)
    (hm : m * (gamma * Nat.log 2 n) ≤ n)
    (hscale : gamma * n * Nat.log 2 n ≤ Δ ^ 2)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ) :
    terminalFailureMass
        (iter
          (freeze (Lemma12RetainedGap X Δ) (productiveStep h3))
          (288 * n) c0)
        (Lemma12RetainedGap X Δ) ≤
      (432 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(((gamma * Nat.log 2 n : ℕ) : ℝ) /
              properStageHeadlineDenominator))) := by
  let A : Config m n → Prop := Lemma12RetainedGap X Δ
  let B : Config m n → Prop := Lemma12HitGap X Δ
  have hBA : ∀ c, B c → A c := by
    intro c hc
    exact hasPairwiseGap_of_le (by omega) hc
  have hmono :=
    targetFreeze_failure_mono_target
      (K := productiveStep h3) (B := B) (C := A) hBA
      (288 * n) c0
  have hhit :=
    productiveStep_properAmplification_hitting_headline
      h3 X (gamma * Nat.log 2 n) Δ hgLarge hΔ4 hm
      (by
        calc
          (gamma * Nat.log 2 n) * n =
              gamma * n * Nat.log 2 n := by ring
          _ ≤ Δ ^ 2 := hscale)
      hΔn c0 hinit
  calc
    terminalFailureMass
        (iter
          (freeze (Lemma12RetainedGap X Δ) (productiveStep h3))
          (288 * n) c0)
        (Lemma12RetainedGap X Δ) ≤
      terminalFailureMass
        (iter (freeze B (productiveStep h3)) (288 * n) c0) B := by
          simpa only [A] using hmono
    _ ≤ (144 : ℝ≥0∞) *
        productiveAmplificationHeadlineError
          (gamma * Nat.log 2 n) := by
      simpa only [B, Lemma12HitGap] using hhit
    _ = (432 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(((gamma * Nat.log 2 n : ℕ) : ℝ) /
              properStageHeadlineDenominator))) :=
      productiveAmplificationHeadlineError_144 _

end Tri.Multi

#print axioms Tri.Multi.lemma12_unconditional

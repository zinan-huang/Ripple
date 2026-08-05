/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBEarlyLadder

/-!
# Heavy-B handoff to the middle constant-gap regime

Two more early Heavy-B stages, at fixed scales `n/320` and `2 * (n/320)`,
raise the exported gap from `8 * (n/320)` to `32 * (n/320)`.  In the middle
regime this dominates the public entry gap `n/12`.
-/

namespace Tri

open scoped ENNReal

/-- Fixed scale used to leave the Heavy-B early regime. -/
def heavyConstantGapScale (n : ℕ) : ℕ :=
  n / 320

/-- Raw horizon of the two-stage constant-gap handoff. -/
def heavyConstantGapHorizon (n : ℕ) : ℕ :=
  heavyEarlyStageHorizon n (heavyConstantGapScale n) +
    heavyEarlyStageHorizon n (2 * heavyConstantGapScale n)

/-- Exact error of the two-stage constant-gap handoff. -/
noncomputable def heavyConstantGapError (n : ℕ) : ℝ≥0∞ :=
  heavyEarlyStageError n (heavyConstantGapScale n) +
    heavyEarlyStageError n (2 * heavyConstantGapScale n)

/-- First Gaussian exponent of the constant-gap handoff. -/
noncomputable def heavyConstantGapEnvelopeScale (n : ℕ) : ℝ :=
  (heavyConstantGapScale n : ℝ) ^ 2 / (4 * (n : ℝ))

/-- In the large-size regime, both fixed handoff stages satisfy the early
joint-clock width guard. -/
theorem heavyConstantGapScale_guards
    {n : ℕ} (hn : 1920 ≤ n) :
    0 < heavyConstantGapScale n ∧
      160 * heavyConstantGapScale n ≤ n ∧
      160 * (2 * heavyConstantGapScale n) ≤ n := by
  unfold heavyConstantGapScale
  constructor
  · omega
  constructor
  · calc
      160 * (n / 320) ≤ 320 * (n / 320) := by omega
      _ ≤ n := Nat.mul_div_le n 320
  · calc
      160 * (2 * (n / 320)) = 320 * (n / 320) := by ring
      _ ≤ n := Nat.mul_div_le n 320

/-- The fixed handoff gap dominates the Heavy-B middle entry gap. -/
theorem heavyGap_to_middle
    {n : ℕ} (hn : 1920 ≤ n) :
    n / 12 ≤ 32 * (n / 320) :=
  heavyMiddle_entry_gap_le_handoff_gap hn

/-- The final fixed early checkpoint implies `HeavyMiddleStart`. -/
theorem heavyConstantGap_checkpoint_to_middle
    {n : ℕ} (hn : 1920 ≤ n) {s : HeavyState n}
    (hs : HeavyEarlyCheckpoint n (4 * heavyConstantGapScale n) 0 s) :
    HeavyMiddleStart n s := by
  have hgap := heavyGap_to_middle hn
  unfold HeavyEarlyCheckpoint heavyEarlyGap at hs
  unfold HeavyMiddleStart
  unfold heavyConstantGapScale at hs hgap
  omega

/-- Two final joint-clock stages carry the early target into the middle
constant-gap regime. -/
theorem heavyConstantGap_reaches
    (n : ℕ) (hn : 3 ≤ n) (hsize : 1920 ≤ n) :
    Reaches (heavyStateStep n) (heavyConstantGapHorizon n)
      (HeavyEarlyTarget n)
      (HeavyMiddleStart n)
      (heavyConstantGapError n) := by
  let q := heavyConstantGapScale n
  have hguards := heavyConstantGapScale_guards hsize
  have hq : 0 < q := by simpa only [q] using hguards.1
  have hqSmall : 160 * q ≤ n := by
    simpa only [q] using hguards.2.1
  have h2qSmall : 160 * (2 * q) ≤ n := by
    simpa only [q] using hguards.2.2
  have hfirst := heavyEarly_stage n hn q hq hqSmall
  have hsecond :=
    heavyEarly_stage n hn (2 * q) (by omega) h2qSmall
  have hchain := hfirst.comp hsecond
  have hstart :
      HeavyEarlyTarget n = HeavyEarlyCheckpoint n q 0 := by
    funext s
    unfold HeavyEarlyTarget HeavyEarlyCheckpoint heavyEarlyGap
    dsimp only [q, heavyConstantGapScale]
    apply propext
    omega
  have hpost := hchain.mono_post (by
    intro s hs
    change HeavyEarlyCheckpoint n (2 * (2 * q)) 0 s at hs
    exact heavyConstantGap_checkpoint_to_middle hsize (by
      have hscale : 2 * (2 * q) = 4 * heavyConstantGapScale n := by
        dsimp only [q]
        ring
      rwa [hscale] at hs))
  simpa only [q, hstart, heavyConstantGapHorizon,
    heavyConstantGapError, two_mul] using hpost

/-- The two handoff stages cost at most forty copies of the first fixed-scale
Gaussian envelope. -/
theorem heavyConstantGapError_le_gaussian
    (n : ℕ) (hsize : 1920 ≤ n) :
    heavyConstantGapError n ≤
      40 * ENNReal.ofReal
        (Real.exp (-heavyConstantGapEnvelopeScale n)) := by
  let q := heavyConstantGapScale n
  have hnNat : 0 < n := by omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hguards := heavyConstantGapScale_guards hsize
  have hq : 0 < q := by simpa only [q] using hguards.1
  have hqSmall : 160 * q ≤ n := by
    simpa only [q] using hguards.2.1
  have h2qSmall : 160 * (2 * q) ≤ n := by
    simpa only [q] using hguards.2.2
  let E : ℝ≥0∞ :=
    ENNReal.ofReal
      (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ)))))
  have hfirst :=
    heavyEarlyStageError_le n q hq hqSmall
  have hsecond :=
    heavyEarlyStageError_le n (2 * q) (by omega) h2qSmall
  have hexp :
      ENNReal.ofReal
          (Real.exp
            (-(((2 * q : ℕ) : ℝ) ^ 2 / (4 * (n : ℝ))))) ≤ E := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    change
      -(((2 * q : ℕ) : ℝ) ^ 2 / (4 * (n : ℝ))) ≤
        -((q : ℝ) ^ 2 / (4 * (n : ℝ)))
    rw [neg_le_neg_iff]
    push_cast
    apply (div_le_div_iff_of_pos_right
      (mul_pos (by norm_num : (0 : ℝ) < 4) hnReal)).2
    nlinarith [sq_nonneg (q : ℝ)]
  have hsecond' : heavyEarlyStageError n (2 * q) ≤ 20 * E :=
    hsecond.trans (by gcongr)
  unfold heavyConstantGapError
  change heavyEarlyStageError n q +
      heavyEarlyStageError n (2 * q) ≤ _
  calc
    heavyEarlyStageError n q + heavyEarlyStageError n (2 * q)
        ≤ 20 * E + 20 * E := add_le_add hfirst hsecond'
    _ = 40 * E := by ring
    _ = 40 * ENNReal.ofReal
        (Real.exp (-heavyConstantGapEnvelopeScale n)) := by
      congr 3

/-! ## Inhabitation gate -/

example :
    Reaches (heavyStateStep 3200) (heavyConstantGapHorizon 3200)
      (HeavyEarlyTarget 3200)
      (HeavyMiddleStart 3200)
      (heavyConstantGapError 3200) := by
  exact heavyConstantGap_reaches 3200 (by norm_num) (by norm_num)

end Tri

#print axioms Tri.heavyConstantGapScale_guards
#print axioms Tri.heavyGap_to_middle
#print axioms Tri.heavyConstantGap_checkpoint_to_middle
#print axioms Tri.heavyConstantGap_reaches
#print axioms Tri.heavyConstantGapError_le_gaussian

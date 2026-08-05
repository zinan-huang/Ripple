/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Assembly
import Tri.ProdBound

/-!
# The phase-3 endgame for the Tri CRN

This module connects the scalar absorption lemmas to the actual three-atom
transition kernel.  The minority potential is `2 ^ y - 1`; its uncorrected
one-step moment first contracts at a rate proportional to `y / n`, and
`absorption_uniformise` then turns that rate into a uniform contraction of the
corrected potential.

The sharp constant used under the guard `8 * y <= n` is `105 / 128`.  The
phase-2 exit condition supplies only `6 * y <= n`; this mismatch, together with
the fact that neither small-minority guard is forward invariant, is made
explicit in the hypotheses of `phase3_reaches` rather than hidden.
-/

namespace Tri

open scoped ENNReal

/-- The two numerical losses in the phase-3 estimate multiply to `105 / 128`. -/
theorem phase3_constant_check : (21 / 8 : ℝ) * (5 / 16) = 105 / 128 := by
  norm_num

/-- The real three-atom moment of the next minority count.  The three summands
correspond respectively to increasing, preserving, and decreasing `y`. -/
noncomputable def phase3Moment (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 1)) : ℝ :=
  ENNReal.toReal (triStep (a + 1) (b + 1) h a) * (2 : ℝ) ^ (b + 2) +
    ENNReal.toReal (triStep (a + 1) (b + 1) h (a + 1)) * (2 : ℝ) ^ (b + 1) +
    ENNReal.toReal (triStep (a + 1) (b + 1) h (a + 2)) * (2 : ℝ) ^ b

/-- **The CRN-specific phase-3 one-step bound.**

At the interior state `x = a + 1`, `y = b + 1`, the three displayed terms are
exactly `E[2 ^ y']`: an `X`-down step raises `y`, a lazy step preserves it, and
an `X`-up step lowers it.  Under the subtraction-free guard `8 * y <= n`, the
productive mass is at least `(21 / 8) * y / n`, while the productive direction
gives the bracket loss `5 / 16`.  Thus the exact advertised constant
`(21 / 8) * (5 / 16) = 105 / 128` is retained. -/
theorem phase3_corrected_step (a b n : ℕ) (h3 : 3 ≤ n)
    (hpop : a + b + 2 = n) (hsmall : 8 * (b + 1) ≤ n) :
    phase3Moment a b (by omega) ≤
      (2 : ℝ) ^ (b + 1) *
        (1 - (105 / 128 : ℝ) * (b + 1 : ℝ) / n) := by
  unfold phase3Moment
  let p0 : ℝ := ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a)
  let p1 : ℝ := ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 1))
  let p2 : ℝ := ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 2))
  have f0 : triStep (a + 1) (b + 1) (by omega) a ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have f1 : triStep (a + 1) (b + 1) (by omega) (a + 1) ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have f2 : triStep (a + 1) (b + 1) (by omega) (a + 2) ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have hsum : p0 + p1 + p2 = 1 := by
    have hmass := triStep_masses_sum a (b + 1) (by omega)
    have hreal := congrArg ENNReal.toReal hmass
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨f0, f1⟩) f2,
      ENNReal.toReal_add f0 f1, ENNReal.toReal_one] at hreal
    exact hreal
  have hab : 7 * b ≤ a := by omega
  have hcounts : 7 * downCount a b ≤ upCount a b := by
    have ha := two_mul_choose_two_succ a
    have hb := two_mul_choose_two_succ b
    simp only [downCount, upCount]
    nlinarith [Nat.mul_le_mul_left ((a + 1) * (b + 1)) hab]
  have hcountsE :
      (7 : ℝ≥0∞) * (((a + 1) * Nat.choose (b + 1) 2 : ℕ) : ℝ≥0∞) ≤
        ((Nat.choose (a + 1) 2 * (b + 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hcounts
  push_cast at hcountsE
  have hdirE : (7 : ℝ≥0∞) * triStep (a + 1) (b + 1) (by omega) a ≤
      triStep (a + 1) (b + 1) (by omega) (a + 2) := by
    rw [triStep_down, triStep_up]
    push_cast
    simpa only [div_eq_mul_inv, mul_assoc] using
      mul_le_mul_left hcountsE
        (Nat.choose ((a + 1) + (b + 1)) 3 : ℝ≥0∞)⁻¹
  have hdir : 7 * p0 ≤ p2 := by
    have hreal := ENNReal.toReal_mono f2 hdirE
    rw [ENNReal.toReal_mul] at hreal
    simpa [p0, p2] using hreal
  have hqeq : p0 + p2 =
      (3 * ((a + 1 : ℕ) * (b + 1)) : ℝ) /
        ((n : ℝ) * (a + b + 1 : ℝ)) := by
    have hmass := productive_mass_closed a b n h3 hpop
    have hreal := congrArg ENNReal.toReal hmass
    rw [ENNReal.toReal_add f0 f2, ENNReal.toReal_div] at hreal
    simpa [p0, p2] using hreal
  have hcross : 21 * (a + b + 1) ≤ 24 * (a + 1) := by omega
  have hratio : (21 / 8 : ℝ) ≤
      3 * (a + 1 : ℝ) / (a + b + 1 : ℝ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (a + b + 1 : ℝ))]
    have hcrossR : (21 : ℝ) * (a + b + 1 : ℝ) ≤
        24 * (a + 1 : ℝ) := by exact_mod_cast hcross
    nlinarith
  have hq : (21 / 8 : ℝ) * (b + 1 : ℝ) / n ≤ p0 + p2 := by
    rw [hqeq]
    have hn : (0 : ℝ) ≤ (b + 1 : ℝ) / n := by positivity
    calc
      (21 / 8 : ℝ) * (b + 1 : ℝ) / n =
          ((b + 1 : ℝ) / n) * (21 / 8) := by ring
      _ ≤ ((b + 1 : ℝ) / n) *
          (3 * (a + 1 : ℝ) / (a + b + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio hn
      _ = (3 * ((a + 1 : ℕ) * (b + 1)) : ℝ) /
          ((n : ℝ) * (a + b + 1 : ℝ)) := by
        push_cast
        field_simp
  have hbracket : 2 * p0 + p1 + p2 / 2 ≤
      1 - (5 / 16 : ℝ) * (p0 + p2) := by
    nlinarith
  have hrate : 1 - (5 / 16 : ℝ) * (p0 + p2) ≤
      1 - (105 / 128 : ℝ) * (b + 1 : ℝ) / n := by
    have hscaled := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 5 / 16)
    calc
      1 - (5 / 16 : ℝ) * (p0 + p2) ≤
          1 - (5 / 16 : ℝ) * ((21 / 8 : ℝ) * (b + 1 : ℝ) / n) :=
        sub_le_sub_left hscaled 1
      _ = 1 - (105 / 128 : ℝ) * (b + 1 : ℝ) / n := by ring
  dsimp [p0, p1, p2] at *
  calc
    ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a) * (2 : ℝ) ^ (b + 2)
          + ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 1)) *
              (2 : ℝ) ^ (b + 1)
          + ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 2)) *
              (2 : ℝ) ^ b
        = (2 : ℝ) ^ (b + 1) *
            (2 * ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a)
              + ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 1))
              + ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 2)) / 2) := by
          rw [show b + 2 = (b + 1) + 1 by omega, pow_succ, pow_succ]
          ring
    _ ≤ (2 : ℝ) ^ (b + 1) *
        (1 - (5 / 16 : ℝ) *
          (ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a) +
           ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 2)))) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ (2 : ℝ) ^ (b + 1) *
        (1 - (105 / 128 : ℝ) * (b + 1 : ℝ) / n) :=
      mul_le_mul_of_nonneg_left hrate (by positivity)

/-- The absorption correction turns the state-dependent `105 / 128` rate into
the same uniform rate for `2 ^ y - 1`. -/
theorem phase3_corrected_step_uniform (a b n : ℕ) (h3 : 3 ≤ n)
    (hpop : a + b + 2 = n) (hsmall : 8 * (b + 1) ≤ n) :
    phase3Moment a b (by omega) - 1 ≤
      (1 - ((105 : ℝ) / 128) / (n : ℝ)) *
        ((2 : ℝ) ^ (b + 1) - 1) := by
  refine absorption_uniformise (E := phase3Moment a b (by omega))
    (ρ := 2) (c := (105 : ℝ) / 128) (n := (n : ℝ)) (b + 1)
    (by norm_num) (by positivity) ?_
  simpa using phase3_corrected_step a b n h3 hpop hsmall

/-- **Conditional phase-3 reachability for the actual chain.**

Starting in `Phase2Exit`, after the single block `C * n * lg n`, the displayed
corrected-potential bound controls failure to reach all-`X` consensus.  The
hypothesis `hVstep` is deliberately explicit: it is the missing stopped-chain
bridge from the guarded local theorem `phase3_corrected_step_uniform` to a
global recurrence.  The local guard is not forward invariant, and
`Phase2Exit` supplies only the weaker guard `6 * y <= n`, so that bridge cannot
be inferred from the theorem above.  Likewise, `hfail` explicitly carries the
escape/Markov conversion from the corrected moment to the actual failure mass,
including possible absorption at all-`Y` consensus.

No per-minority-state block is introduced: `absorption_iterate` applies the
uniform scalar factor to this one `Theta(n * lg n)` block. -/
theorem phase3_reaches
    (C n γ : ℕ) (h3 : 3 ≤ n) (V : ℕ → ℕ → ℝ)
    (hV0 : ∀ x, Phase2Exit n γ x →
      V x 0 ≤ (2 : ℝ) ^ (γ * Nat.log 2 n) - 1)
    (hVstep : ∀ x, Phase2Exit n γ x → ∀ t,
      V x (t + 1) ≤
        (1 - ((105 : ℝ) / 128) / (n : ℝ)) * V x t)
    (hfail : ∀ x, Phase2Exit n γ x →
      ∑' z, (if IsXMajority n z then 0
        else iter (triChain n) (C * n * Nat.log 2 n) x z) ≤
          ENNReal.ofReal (V x (C * n * Nat.log 2 n))) :
    Reaches (triChain n) (C * n * Nat.log 2 n) (Phase2Exit n γ)
      (IsXMajority n)
      (ENNReal.ofReal (((2 : ℝ) ^ (γ * Nat.log 2 n) - 1) *
        (1 - ((105 : ℝ) / 128) / (n : ℝ)) ^
          (C * n * Nat.log 2 n))) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hcn : (105 : ℝ) / 128 ≤ n := by
    calc
      (105 : ℝ) / 128 ≤ 1 := by norm_num
      _ ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hfactor : 0 ≤ 1 - ((105 : ℝ) / 128) / (n : ℝ) :=
    sub_nonneg.mpr ((div_le_one hnpos).2 hcn)
  intro x hx
  calc
    ∑' z, (if IsXMajority n z then 0
        else iter (triChain n) (C * n * Nat.log 2 n) x z) ≤
        ENNReal.ofReal (V x (C * n * Nat.log 2 n)) := hfail x hx
    _ ≤ ENNReal.ofReal (V x 0 *
        (1 - ((105 : ℝ) / 128) / (n : ℝ)) ^
          (C * n * Nat.log 2 n)) :=
      ENNReal.ofReal_le_ofReal
        (absorption_iterate (fun t => V x t) hfactor (hVstep x hx)
          (C * n * Nat.log 2 n))
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ (γ * Nat.log 2 n) - 1) *
        (1 - ((105 : ℝ) / 128) / (n : ℝ)) ^
          (C * n * Nat.log 2 n)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hV0 x hx)
        (pow_nonneg hfactor _))

end Tri

/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PhaseGlue

/-!
# The stopped phase-3 chain

This module weakens the local phase-3 guard from `8 * y <= n` to
`6 * y <= n`, constructs the corresponding stopped chain, and lifts its
corrected-potential contraction through arbitrary finite horizons.

The constant `105 / 128` is false for the uncorrected geometric moment under
the weaker guard: the uniform uncorrected constant is `5 / 8`.  The corrected
potential `2 ^ y - 1` nevertheless retains `105 / 128`, because every live
state has `y >= 1` and the subtraction of the absorbing value leaves additional
slack.

The stopped recurrence itself is unconditional.  Terminal transfer exposes one
real obstruction: a potential killed on frozen escape states contracts, but no
longer dominates those failures; retaining the positive potential restores
domination but makes strict contraction at a pure frozen state false.  The
unconditional conclusion is therefore an expectation bound plus the explicit
`phase3EscapeMass`.  `Phase3EscapeSlack` is the sole residual needed by the
existing no-additive-error `Phase3Bridge` interface, and both sides of the
obstruction are proved false below on a concrete state.
-/

namespace Tri

open scoped ENNReal

/-- Under `6 * y <= n`, the uncorrected geometric moment contracts with the
uniform state-dependent constant `5 / 8`. -/
theorem phase3_step_six (a b n : ℕ) (h3 : 3 ≤ n)
    (hpop : a + b + 2 = n) (hsmall : 6 * (b + 1) ≤ n) :
    phase3Moment a b (by omega) ≤
      (2 : ℝ) ^ (b + 1) *
        (1 - (5 / 8 : ℝ) * (b + 1 : ℝ) / n) := by
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
  have hab : 5 * b ≤ a := by omega
  have hcounts : 5 * downCount a b ≤ upCount a b := by
    have ha := two_mul_choose_two_succ a
    have hb := two_mul_choose_two_succ b
    simp only [downCount, upCount]
    nlinarith [Nat.mul_le_mul_left ((a + 1) * (b + 1)) hab]
  have hcountsE :
      (5 : ℝ≥0∞) * (((a + 1) * Nat.choose (b + 1) 2 : ℕ) : ℝ≥0∞) ≤
        ((Nat.choose (a + 1) 2 * (b + 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hcounts
  push_cast at hcountsE
  have hdirE : (5 : ℝ≥0∞) * triStep (a + 1) (b + 1) (by omega) a ≤
      triStep (a + 1) (b + 1) (by omega) (a + 2) := by
    rw [triStep_down, triStep_up]
    push_cast
    simpa only [div_eq_mul_inv, mul_assoc] using
      mul_le_mul_left hcountsE
        (Nat.choose ((a + 1) + (b + 1)) 3 : ℝ≥0∞)⁻¹
  have hdir : 5 * p0 ≤ p2 := by
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
  have hcross : 5 * (a + b + 1) ≤ 6 * (a + 1) := by omega
  have hratio : (5 / 2 : ℝ) ≤
      3 * (a + 1 : ℝ) / (a + b + 1 : ℝ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (a + b + 1 : ℝ))]
    have hcrossR : (5 : ℝ) * (a + b + 1 : ℝ) ≤
        6 * (a + 1 : ℝ) := by exact_mod_cast hcross
    nlinarith
  have hq : (5 / 2 : ℝ) * (b + 1 : ℝ) / n ≤ p0 + p2 := by
    rw [hqeq]
    have hn : (0 : ℝ) ≤ (b + 1 : ℝ) / n := by positivity
    calc
      (5 / 2 : ℝ) * (b + 1 : ℝ) / n =
          ((b + 1 : ℝ) / n) * (5 / 2) := by ring
      _ ≤ ((b + 1 : ℝ) / n) *
          (3 * (a + 1 : ℝ) / (a + b + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio hn
      _ = (3 * ((a + 1 : ℕ) * (b + 1)) : ℝ) /
          ((n : ℝ) * (a + b + 1 : ℝ)) := by
        push_cast
        field_simp
  have hbracket : 2 * p0 + p1 + p2 / 2 ≤
      1 - (1 / 4 : ℝ) * (p0 + p2) := by
    nlinarith
  have hrate : 1 - (1 / 4 : ℝ) * (p0 + p2) ≤
      1 - (5 / 8 : ℝ) * (b + 1 : ℝ) / n := by
    have hscaled := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 1 / 4)
    calc
      1 - (1 / 4 : ℝ) * (p0 + p2) ≤
          1 - (1 / 4 : ℝ) * ((5 / 2 : ℝ) * (b + 1 : ℝ) / n) :=
        sub_le_sub_left hscaled 1
      _ = 1 - (5 / 8 : ℝ) * (b + 1 : ℝ) / n := by ring
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
        (1 - (1 / 4 : ℝ) *
          (ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a) +
           ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 2)))) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ (2 : ℝ) ^ (b + 1) *
        (1 - (5 / 8 : ℝ) * (b + 1 : ℝ) / n) :=
      mul_le_mul_of_nonneg_left hrate (by positivity)

/-- The constant `105 / 128` cannot be retained for the uncorrected moment
under only `6 * y <= n`; `n = 24` and `y = 4` are an explicit counterexample. -/
theorem phase3_step_six_105_false :
    ¬ (phase3Moment 19 3 (by norm_num) ≤
      (2 : ℝ) ^ 4 * (1 - (105 / 128 : ℝ) * (4 : ℝ) / 24)) := by
  unfold phase3Moment
  rw [triStep_down, triStep_stay, triStep_up]
  norm_num [Nat.choose, ENNReal.toReal_add, ENNReal.toReal_div]

/-- For every positive exponent, half of `y * 2^y` already dominates the
absorption correction `2^y - 1`. -/
theorem phase3_pow_sub_one_le_half_mul (y : ℕ) (hy : 1 ≤ y) :
    (2 : ℝ) ^ y - 1 ≤ (1 / 2 : ℝ) * y * (2 : ℝ) ^ y := by
  rcases y with _ | y
  · omega
  rcases y with _ | y
  · norm_num
  have hy2 : (2 : ℝ) ≤ (Nat.succ (Nat.succ y) : ℕ) := by
    exact_mod_cast (by omega : 2 ≤ Nat.succ (Nat.succ y))
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ Nat.succ (Nat.succ y) := by positivity
  have hhalf : (1 : ℝ) ≤
      (1 / 2 : ℝ) * (Nat.succ (Nat.succ y) : ℕ) := by
    nlinarith
  calc
    (2 : ℝ) ^ Nat.succ (Nat.succ y) - 1 ≤
        (2 : ℝ) ^ Nat.succ (Nat.succ y) := sub_le_self _ zero_le_one
    _ ≤ (1 / 2 : ℝ) * (Nat.succ (Nat.succ y) : ℕ) *
        (2 : ℝ) ^ Nat.succ (Nat.succ y) :=
      by simpa only [one_mul] using mul_le_mul_of_nonneg_right hhalf hp

/-- The `5 / 8` uncorrected drift under the weaker guard implies the original
`105 / 128` uniform contraction for the corrected potential. -/
theorem phase3_absorption_six {E n : ℝ} (y : ℕ) (hy : 1 ≤ y)
    (hn : 0 < n)
    (hE : E ≤ (2 : ℝ) ^ y * (1 - (5 / 8 : ℝ) * (y : ℝ) / n)) :
    E - 1 ≤
      (1 - ((105 : ℝ) / 128) / n) * ((2 : ℝ) ^ y - 1) := by
  have hpow := phase3_pow_sub_one_le_half_mul y hy
  have hslack :
      ((105 : ℝ) / 128) * ((2 : ℝ) ^ y - 1) ≤
        (5 / 8 : ℝ) * (y : ℝ) * (2 : ℝ) ^ y := by
    calc
      ((105 : ℝ) / 128) * ((2 : ℝ) ^ y - 1) ≤
          ((105 : ℝ) / 128) *
            ((1 / 2 : ℝ) * y * (2 : ℝ) ^ y) :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ (5 / 8 : ℝ) * (y : ℝ) * (2 : ℝ) ^ y := by
        have hyR : (0 : ℝ) ≤ y := by positivity
        have hp : (0 : ℝ) ≤ (2 : ℝ) ^ y := by positivity
        nlinarith
  calc
    E - 1 ≤
        (2 : ℝ) ^ y * (1 - (5 / 8 : ℝ) * (y : ℝ) / n) - 1 :=
      sub_le_sub_right hE 1
    _ = ((2 : ℝ) ^ y - 1) -
        ((5 / 8 : ℝ) * (y : ℝ) * (2 : ℝ) ^ y) / n := by ring
    _ ≤ ((2 : ℝ) ^ y - 1) -
        (((105 : ℝ) / 128) * ((2 : ℝ) ^ y - 1)) / n :=
      sub_le_sub_left ((div_le_div_iff_of_pos_right hn).2 hslack) _
    _ = (1 - ((105 : ℝ) / 128) / n) * ((2 : ℝ) ^ y - 1) := by ring

/-- The corrected one-step estimate keeps the original `105 / 128` constant
under the weaker phase-2 guard `6 * y <= n`. -/
theorem phase3_corrected_step_uniform_six (a b n : ℕ) (h3 : 3 ≤ n)
    (hpop : a + b + 2 = n) (hsmall : 6 * (b + 1) ≤ n) :
    phase3Moment a b (by omega) - 1 ≤
      (1 - ((105 : ℝ) / 128) / (n : ℝ)) *
        ((2 : ℝ) ^ (b + 1) - 1) := by
  exact phase3_absorption_six (b + 1) (by omega) (by positivity)
    (by simpa only [Nat.cast_add, Nat.cast_one] using
      phase3_step_six a b n h3 hpop hsmall)

/-- The subtraction-free phase-3 live region.  On a physical state `x + y = n`,
its inequalities say exactly `1 ≤ y` and `6 * y ≤ n`. -/
def Phase3Region (n x : ℕ) : Prop :=
  x < n ∧ 5 * n ≤ 6 * x

/-- Membership in the weakened phase-3 live region is decidable. -/
instance (n : ℕ) : DecidablePred (Phase3Region n) := by
  intro x
  unfold Phase3Region
  infer_instance

/-- The subtraction-free successor-coordinate characterization of the live
region used by the local corrected-step theorem. -/
theorem phase3Region_iff_successors (n x : ℕ) (h3 : 3 ≤ n) :
    Phase3Region n x ↔
      ∃ a b : ℕ, x = a + 1 ∧ a + b + 2 = n ∧ 6 * (b + 1) ≤ n := by
  constructor
  · intro hx
    rcases x with _ | a
    · unfold Phase3Region at hx
      omega
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hx.1)
      rcases d with _ | b
      · exfalso
        simp only [add_zero] at hd
        exact (Nat.ne_of_lt hx.1) hd.symm
      · refine ⟨a, b, rfl, ?_, ?_⟩
        · omega
        · unfold Phase3Region at hx
          omega
  · rintro ⟨a, b, rfl, hpop, hsmall⟩
    unfold Phase3Region
    omega

/-- The corrected minority potential, defined without natural subtraction.
The sum has at most one nonzero term, indexed by the unique `y` with
`x + y = n`; states above the physical range receive value zero. -/
noncomputable def phase3Potential (n x : ℕ) : ℝ≥0∞ :=
  ∑' y : ℕ,
    if x + y = n then ENNReal.ofReal ((2 : ℝ) ^ y - 1) else 0

/-- Evaluation of the subtraction-free potential at a physical decomposition. -/
theorem phase3Potential_apply {n x y : ℕ} (hxy : x + y = n) :
    phase3Potential n x = ENNReal.ofReal ((2 : ℝ) ^ y - 1) := by
  unfold phase3Potential
  rw [tsum_eq_single y]
  · simp [hxy]
  · intro z hz
    rw [if_neg]
    intro hxz
    omega

/-- The phase-3 chain stopped as soon as it leaves the weakened live region. -/
noncomputable def phase3Stop (n : ℕ) : ℕ → PMF ℕ :=
  freeze (fun x => ¬ Phase3Region n x) (triChain n)

/-- The killed corrected potential agrees with the physical potential in the
live region and vanishes on every frozen state. -/
noncomputable def phase3StoppedPotential (n x : ℕ) : ℝ≥0∞ :=
  if Phase3Region n x then phase3Potential n x else 0

/-- In the live region the killed potential is the corrected minority
potential. -/
theorem phase3StoppedPotential_of_mem {n x : ℕ} (hx : Phase3Region n x) :
    phase3StoppedPotential n x = phase3Potential n x := by
  simp [phase3StoppedPotential, hx]

/-- Outside the live region the killed potential is zero. -/
theorem phase3StoppedPotential_of_not_mem {n x : ℕ} (hx : ¬ Phase3Region n x) :
    phase3StoppedPotential n x = 0 := by
  simp [phase3StoppedPotential, hx]

/-- Killing outside the live region only decreases the physical corrected
potential. -/
theorem phase3StoppedPotential_le (n x : ℕ) :
    phase3StoppedPotential n x ≤ phase3Potential n x := by
  by_cases hx : Phase3Region n x
  · rw [phase3StoppedPotential_of_mem hx]
  · rw [phase3StoppedPotential_of_not_mem hx]
    exact bot_le

/-- The finite `ℝ≥0∞` contraction factor corresponding to `105 / 128`. -/
noncomputable def phase3Factor (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - ((105 : ℝ) / 128) / (n : ℝ))

/-- The real phase-3 factor is nonnegative at every population of size at
least three. -/
theorem phase3_factor_nonneg (n : ℕ) (h3 : 3 ≤ n) :
    0 ≤ 1 - ((105 : ℝ) / 128) / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hcn : (105 : ℝ) / 128 ≤ n := by
    calc
      (105 : ℝ) / 128 ≤ 1 := by norm_num
      _ ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  exact sub_nonneg.mpr ((div_le_one hnpos).2 hcn)

/-- Converting the finite phase-3 factor back to `ℝ` loses no information. -/
theorem phase3Factor_toReal (n : ℕ) (h3 : 3 ≤ n) :
    (phase3Factor n).toReal =
      1 - ((105 : ℝ) / 128) / (n : ℝ) := by
  exact ENNReal.toReal_ofReal (phase3_factor_nonneg n h3)

/-- The phase-3 factor is finite. -/
theorem phase3Factor_ne_top (n : ℕ) : phase3Factor n ≠ ⊤ := by
  exact ENNReal.ofReal_ne_top

/-- The expectation of the physical corrected potential is exactly the real
three-atom moment minus the absorbing value one. -/
theorem expect_phase3Potential (a b n : ℕ) (h3 : 3 ≤ n)
    (hpop : a + b + 2 = n) :
    expect (triChain n (a + 1)) (phase3Potential n) =
      ENNReal.ofReal (phase3Moment a b (by omega) - 1) := by
  rw [triChain_apply hpop h3, expect_triStep]
  rw [phase3Potential_apply (show a + (b + 2) = n by omega),
    phase3Potential_apply (show a + 1 + (b + 1) = n by omega),
    phase3Potential_apply (show a + 2 + b = n by omega)]
  let p0 : ℝ≥0∞ := triStep (a + 1) (b + 1) (by omega) a
  let p1 : ℝ≥0∞ := triStep (a + 1) (b + 1) (by omega) (a + 1)
  let p2 : ℝ≥0∞ := triStep (a + 1) (b + 1) (by omega) (a + 2)
  have fp0 : p0 ≠ ⊤ := PMF.apply_ne_top _ _
  have fp1 : p1 ≠ ⊤ := PMF.apply_ne_top _ _
  have fp2 : p2 ≠ ⊤ := PMF.apply_ne_top _ _
  have hr0 : 0 ≤ (2 : ℝ) ^ (b + 2) - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  have hr1 : 0 ≤ (2 : ℝ) ^ (b + 1) - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  have hr2 : 0 ≤ (2 : ℝ) ^ b - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  have ft0 : p0 * ENNReal.ofReal ((2 : ℝ) ^ (b + 2) - 1) ≠ ⊤ :=
    ENNReal.mul_ne_top fp0 ENNReal.ofReal_ne_top
  have ft1 : p1 * ENNReal.ofReal ((2 : ℝ) ^ (b + 1) - 1) ≠ ⊤ :=
    ENNReal.mul_ne_top fp1 ENNReal.ofReal_ne_top
  have ft2 : p2 * ENNReal.ofReal ((2 : ℝ) ^ b - 1) ≠ ⊤ :=
    ENNReal.mul_ne_top fp2 ENNReal.ofReal_ne_top
  have htop :
      p0 * ENNReal.ofReal ((2 : ℝ) ^ (b + 2) - 1) +
          p1 * ENNReal.ofReal ((2 : ℝ) ^ (b + 1) - 1) +
          p2 * ENNReal.ofReal ((2 : ℝ) ^ b - 1) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ft0, ft1⟩, ft2⟩
  have hsum : p0.toReal + p1.toReal + p2.toReal = 1 := by
    have hm := triStep_masses_sum a (b + 1) (by omega)
    have hmR := congrArg ENNReal.toReal hm
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨fp0, fp1⟩) fp2,
      ENNReal.toReal_add fp0 fp1, ENNReal.toReal_one] at hmR
    exact hmR
  change
    p0 * ENNReal.ofReal ((2 : ℝ) ^ (b + 2) - 1) +
        p1 * ENNReal.ofReal ((2 : ℝ) ^ (b + 1) - 1) +
        p2 * ENNReal.ofReal ((2 : ℝ) ^ b - 1) =
      ENNReal.ofReal (phase3Moment a b (by omega) - 1)
  calc
    p0 * ENNReal.ofReal ((2 : ℝ) ^ (b + 2) - 1) +
          p1 * ENNReal.ofReal ((2 : ℝ) ^ (b + 1) - 1) +
          p2 * ENNReal.ofReal ((2 : ℝ) ^ b - 1) =
        ENNReal.ofReal
          ((p0 * ENNReal.ofReal ((2 : ℝ) ^ (b + 2) - 1) +
            p1 * ENNReal.ofReal ((2 : ℝ) ^ (b + 1) - 1) +
            p2 * ENNReal.ofReal ((2 : ℝ) ^ b - 1)).toReal) :=
      (ENNReal.ofReal_toReal htop).symm
    _ = ENNReal.ofReal (phase3Moment a b (by omega) - 1) := by
      congr 1
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ft0, ft1⟩) ft2,
        ENNReal.toReal_add ft0 ft1, ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hr0, ENNReal.toReal_ofReal hr1,
        ENNReal.toReal_ofReal hr2]
      unfold phase3Moment
      change
        p0.toReal * ((2 : ℝ) ^ (b + 2) - 1) +
            p1.toReal * ((2 : ℝ) ^ (b + 1) - 1) +
            p2.toReal * ((2 : ℝ) ^ b - 1) =
          p0.toReal * (2 : ℝ) ^ (b + 2) +
            p1.toReal * (2 : ℝ) ^ (b + 1) +
            p2.toReal * (2 : ℝ) ^ b - 1
      linarith

/-- The killed corrected potential contracts in one step at every state of the
stopped chain.  Live states use the weakened local theorem; frozen states have
zero potential. -/
theorem phase3Stop_step (n : ℕ) (h3 : 3 ≤ n) :
    ∀ x, expect (phase3Stop n x) (phase3StoppedPotential n) ≤
      phase3Factor n * phase3StoppedPotential n x := by
  intro x
  by_cases hx : Phase3Region n x
  · rw [phase3Stop, freeze_of_not_mem x (by simpa using hx),
      phase3StoppedPotential_of_mem hx]
    obtain ⟨a, b, rfl, hpop, hsmall⟩ :=
      (phase3Region_iff_successors n x h3).mp hx
    have hlocal := phase3_corrected_step_uniform_six a b n h3 hpop hsmall
    have hq := phase3_factor_nonneg n h3
    calc
      expect (triChain n (a + 1)) (phase3StoppedPotential n) ≤
          expect (triChain n (a + 1)) (phase3Potential n) := by
        unfold expect
        exact ENNReal.tsum_le_tsum fun z =>
          mul_le_mul_right (phase3StoppedPotential_le n z) _
      _ = ENNReal.ofReal (phase3Moment a b (by omega) - 1) :=
        expect_phase3Potential a b n h3 hpop
      _ ≤ ENNReal.ofReal
          ((1 - ((105 : ℝ) / 128) / (n : ℝ)) *
            ((2 : ℝ) ^ (b + 1) - 1)) :=
        ENNReal.ofReal_le_ofReal hlocal
      _ = phase3Factor n * phase3Potential n (a + 1) := by
        rw [phase3Potential_apply
          (show a + 1 + (b + 1) = n by omega)]
        unfold phase3Factor
        exact ENNReal.ofReal_mul hq
  · rw [phase3Stop, freeze_of_mem x hx, expect_pure,
      phase3StoppedPotential_of_not_mem hx]
    simp

/-- Iterating the stopped one-step estimate gives geometric decay of the
killed corrected potential for every finite horizon. -/
theorem phase3Stop_expect_iter_le (n T x : ℕ) (h3 : 3 ≤ n) :
    expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) ≤
      phase3Factor n ^ T * phase3StoppedPotential n x := by
  exact expect_iter_le (phase3Stop n) (phase3StoppedPotential n)
    (phase3Factor n) (phase3Stop_step n h3) T x

/-- The killed corrected potential is finite at every state. -/
theorem phase3StoppedPotential_ne_top (n x : ℕ) :
    phase3StoppedPotential n x ≠ ⊤ := by
  by_cases hx : Phase3Region n x
  · rw [phase3StoppedPotential_of_mem hx]
    rcases (phase3Region_iff_successors n x (by
      unfold Phase3Region at hx
      omega)).mp hx with ⟨a, b, rfl, hpop, _hsmall⟩
    rw [phase3Potential_apply
      (show a + 1 + (b + 1) = n by omega)]
    exact ENNReal.ofReal_ne_top
  · rw [phase3StoppedPotential_of_not_mem hx]
    exact ENNReal.zero_ne_top

/-- Every stopped-chain corrected expectation is finite. -/
theorem phase3Stop_expect_ne_top (n T x : ℕ) (h3 : 3 ≤ n) :
    expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) ≠ ⊤ := by
  have hbound := phase3Stop_expect_iter_le n T x h3
  have hright : phase3Factor n ^ T * phase3StoppedPotential n x ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (phase3Factor_ne_top n))
      (phase3StoppedPotential_ne_top n x)
  exact ne_top_of_le_ne_top hright hbound

/-- The real corrected moment of the stopped chain after `T` interactions. -/
noncomputable def phase3StoppedMoment (n x T : ℕ) : ℝ :=
  ENNReal.toReal
    (expect (iter (phase3Stop n) T x) (phase3StoppedPotential n))

/-- Real form of the stopped-chain geometric estimate. -/
theorem phase3StoppedMoment_le (n T x : ℕ) (h3 : 3 ≤ n) :
    phase3StoppedMoment n x T ≤
      (1 - ((105 : ℝ) / 128) / (n : ℝ)) ^ T *
        (phase3StoppedPotential n x).toReal := by
  have hbound := phase3Stop_expect_iter_le n T x h3
  have hright : phase3Factor n ^ T * phase3StoppedPotential n x ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (phase3Factor_ne_top n))
      (phase3StoppedPotential_ne_top n x)
  have hreal := ENNReal.toReal_mono hright hbound
  simpa only [phase3StoppedMoment, ENNReal.toReal_mul, ENNReal.toReal_pow,
    phase3Factor_toReal n h3] using hreal

/-- The stopped corrected expectation contracts from time `t` to time `t+1`. -/
theorem phase3Stop_expect_step (n t x : ℕ) (h3 : 3 ≤ n) :
    expect (iter (phase3Stop n) (t + 1) x) (phase3StoppedPotential n) ≤
      phase3Factor n *
        expect (iter (phase3Stop n) t x) (phase3StoppedPotential n) := by
  rw [iter_succ', expect_bind]
  calc
    ∑' a, iter (phase3Stop n) t x a *
          expect (phase3Stop n a) (phase3StoppedPotential n) ≤
        ∑' a, iter (phase3Stop n) t x a *
          (phase3Factor n * phase3StoppedPotential n a) :=
      ENNReal.tsum_le_tsum fun a =>
        mul_le_mul_right (phase3Stop_step n h3 a) _
    _ = phase3Factor n *
        ∑' a, iter (phase3Stop n) t x a * phase3StoppedPotential n a := by
      rw [← ENNReal.tsum_mul_left]
      congr 1
      funext a
      ring

/-- Real per-time recurrence required by the phase-3 bridge, proved for the
actual expectation along the stopped chain. -/
theorem phase3StoppedMoment_step (n x t : ℕ) (h3 : 3 ≤ n) :
    phase3StoppedMoment n x (t + 1) ≤
      (1 - ((105 : ℝ) / 128) / (n : ℝ)) *
        phase3StoppedMoment n x t := by
  have hstep := phase3Stop_expect_step n t x h3
  have hright : phase3Factor n *
      expect (iter (phase3Stop n) t x) (phase3StoppedPotential n) ≠ ⊤ :=
    ENNReal.mul_ne_top (phase3Factor_ne_top n)
      (phase3Stop_expect_ne_top n t x h3)
  have hreal := ENNReal.toReal_mono hright hstep
  simpa only [phase3StoppedMoment, ENNReal.toReal_mul,
    phase3Factor_toReal n h3] using hreal

/-- Every live stopped state has corrected potential at least one. -/
theorem one_le_phase3StoppedPotential {n x : ℕ} (h3 : 3 ≤ n)
    (hx : Phase3Region n x) :
    1 ≤ phase3StoppedPotential n x := by
  rw [phase3StoppedPotential_of_mem hx]
  obtain ⟨a, b, rfl, hpop, _hsmall⟩ :=
    (phase3Region_iff_successors n x h3).mp hx
  rw [phase3Potential_apply
    (show a + 1 + (b + 1) = n by omega), ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  nlinarith

/-- Markov's inequality bounds the stopped mass which is still live and has
not reached all-`X` consensus by its corrected expectation. -/
theorem phase3Stop_live_mass_le_expect (n T x : ℕ) (h3 : 3 ≤ n) :
    (∑' z, if Phase3Region n z then iter (phase3Stop n) T x z else 0) ≤
      expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) := by
  calc
    (∑' z, if Phase3Region n z then iter (phase3Stop n) T x z else 0) ≤
        ∑' z, if 1 ≤ phase3StoppedPotential n z then
          iter (phase3Stop n) T x z else 0 := by
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hz : Phase3Region n z
      · simp [hz, one_le_phase3StoppedPotential h3 hz]
      · simp [hz]
    _ ≤ expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) / 1 :=
      markov_div (iter (phase3Stop n) T x) (phase3StoppedPotential n) 1
        one_ne_zero ENNReal.one_ne_top
    _ = expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) := by simp

/-- A `Phase2Exit` state is either all-`X` consensus or belongs to the weakened
phase-3 live region, under the headline size guard. -/
theorem phase2Exit_eq_consensus_or_phase3Region (n γ x : ℕ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) (hx : Phase2Exit n γ x) :
    x = n ∨ Phase3Region n x := by
  rcases eq_or_lt_of_le hx.1 with hxn | hxn
  · exact Or.inl hxn
  · right
    unfold Phase3Region
    constructor
    · exact hxn
    · unfold Phase2Exit at hx
      have hsize' : 6 * (γ * Nat.log 2 n) ≤ n := by
        simpa [Nat.mul_assoc] using hsize
      omega

/-- At time zero, the stopped corrected moment is bounded by the phase-2
minority threshold. -/
theorem phase3StoppedMoment_zero_le (n γ x : ℕ) (h3 : 3 ≤ n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) (hx : Phase2Exit n γ x) :
    phase3StoppedMoment n x 0 ≤
      (2 : ℝ) ^ (γ * Nat.log 2 n) - 1 := by
  rcases phase2Exit_eq_consensus_or_phase3Region n γ x hsize hx with hxn | hregion
  · subst x
    have hnregion : ¬ Phase3Region n n := by
      unfold Phase3Region
      omega
    have hzero : phase3StoppedMoment n n 0 = 0 := by
      simp [phase3StoppedMoment, phase3StoppedPotential_of_not_mem hnregion]
    rw [hzero]
    exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  · obtain ⟨a, b, rfl, hpop, _hsmall⟩ :=
      (phase3Region_iff_successors n x h3).mp hregion
    have hy : b + 1 ≤ γ * Nat.log 2 n := by
      unfold Phase2Exit at hx
      omega
    have hr : 0 ≤ (2 : ℝ) ^ (b + 1) - 1 :=
      sub_nonneg.mpr (one_le_pow₀ (by norm_num))
    simp only [phase3StoppedMoment, iter_zero, expect_pure,
      phase3StoppedPotential_of_mem hregion,
      phase3Potential_apply (show a + 1 + (b + 1) = n by omega),
      ENNReal.toReal_ofReal hr]
    exact sub_le_sub_right (pow_le_pow_right₀ (by norm_num) hy) 1

/-- The stopped mass which remains inside the live phase-3 region. -/
noncomputable def phase3LiveMass (n T x : ℕ) : ℝ≥0∞ :=
  ∑' z, if Phase3Region n z then iter (phase3Stop n) T x z else 0

/-- The stopped mass frozen at a non-consensus escape state.  This includes the
all-`Y` state and every exit through the weakened lower boundary. -/
noncomputable def phase3EscapeMass (n T x : ℕ) : ℝ≥0∞ :=
  ∑' z, if ¬ Phase3Region n z ∧ z ≠ n then
    iter (phase3Stop n) T x z else 0

/-- All-`X` consensus remains fixed under every deterministic iterate of the
actual Tri chain. -/
theorem iter_triChain_consensus (n T : ℕ) (h3 : 3 ≤ n) :
    iter (triChain n) T n = PMF.pure n := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [iter_succ, triChain_consensus h3, PMF.pure_bind, ih]

/-- Freezing outside the phase-3 region can only increase terminal failure of
all-`X` consensus.  Freezing all-`X` itself is harmless because it is already
absorbing for the actual chain. -/
theorem phase3_failure_le_stopped_failure (n T x : ℕ) (h3 : 3 ≤ n) :
    (∑' z, if IsXMajority n z then 0 else iter (triChain n) T x z) ≤
      ∑' z, if IsXMajority n z then 0 else iter (phase3Stop n) T x z := by
  have hreturn : ∀ s, (¬ Phase3Region n s) → IsXMajority n s → ∀ U,
      (∑' z, if IsXMajority n z then 0 else iter (triChain n) U s z) ≤ 0 := by
    intro s _hsB hsA U
    unfold IsXMajority at hsA
    subst s
    rw [iter_triChain_consensus n U h3]
    simp [IsXMajority, PMF.pure_apply]
  simpa [phase3Stop] using
    (failure_le_failure_freeze_add
      (B := fun s : ℕ => ¬ Phase3Region n s)
      (A := IsXMajority n) (K := triChain n) (δ := 0) hreturn T x)

/-- Stopped failure is exactly the disjoint sum of live non-consensus mass and
escaped mass. -/
theorem phase3_stopped_failure_eq_live_add_escape (n T x : ℕ) :
    (∑' z, if IsXMajority n z then 0 else iter (phase3Stop n) T x z) =
      phase3LiveMass n T x + phase3EscapeMass n T x := by
  unfold phase3LiveMass phase3EscapeMass
  calc
    (∑' z, if IsXMajority n z then 0 else iter (phase3Stop n) T x z) =
        ∑' z, ((if Phase3Region n z then iter (phase3Stop n) T x z else 0) +
          if ¬ Phase3Region n z ∧ z ≠ n then
            iter (phase3Stop n) T x z else 0) := by
      apply tsum_congr
      intro z
      by_cases hz : Phase3Region n z
      · have hzn : z ≠ n := by
          unfold Phase3Region at hz
          omega
        simp [IsXMajority, hz, hzn]
      · by_cases hzn : z = n
        · subst z
          have hnregion : ¬ Phase3Region n n := by
            unfold Phase3Region
            omega
          simp [IsXMajority, hnregion]
        · simp [IsXMajority, hz, hzn]
    _ = (∑' z, if Phase3Region n z then iter (phase3Stop n) T x z else 0) +
        ∑' z, if ¬ Phase3Region n z ∧ z ≠ n then
          iter (phase3Stop n) T x z else 0 := ENNReal.tsum_add

/-- The exact unconditional result of stopped-chain transfer and Markov: the
actual failure mass is bounded by the corrected expectation plus one explicit
escape term. -/
theorem phase3_failure_le_expect_add_escape (n T x : ℕ) (h3 : 3 ≤ n) :
    (∑' z, if IsXMajority n z then 0 else iter (triChain n) T x z) ≤
      expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) +
        phase3EscapeMass n T x := by
  calc
    (∑' z, if IsXMajority n z then 0 else iter (triChain n) T x z) ≤
        ∑' z, if IsXMajority n z then 0 else iter (phase3Stop n) T x z :=
      phase3_failure_le_stopped_failure n T x h3
    _ = phase3LiveMass n T x + phase3EscapeMass n T x :=
      phase3_stopped_failure_eq_live_add_escape n T x
    _ ≤ expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) +
        phase3EscapeMass n T x :=
      add_le_add_left (phase3Stop_live_mass_le_expect n T x h3) _

/-- The single genuine transfer residual: escaped stopped mass must fit inside
the slack between the corrected expectation and the live mass controlled by
Markov.  No recurrence or terminal failure statement is hidden in this
hypothesis. -/
def Phase3EscapeSlack (n T x : ℕ) : Prop :=
  phase3EscapeMass n T x ≤
    expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) -
      phase3LiveMass n T x

/-- If the explicit escape residual is supplied, stopped-chain transfer and
Markov give the terminal `hfail` inequality with no further hypothesis. -/
theorem phase3_failure_le_expect_of_escapeSlack (n T x : ℕ) (h3 : 3 ≤ n)
    (hescape : Phase3EscapeSlack n T x) :
    (∑' z, if IsXMajority n z then 0 else iter (triChain n) T x z) ≤
      expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) := by
  have hlive := phase3Stop_live_mass_le_expect n T x h3
  calc
    (∑' z, if IsXMajority n z then 0 else iter (triChain n) T x z) ≤
        phase3LiveMass n T x + phase3EscapeMass n T x := by
      exact (phase3_failure_le_stopped_failure n T x h3).trans_eq
        (phase3_stopped_failure_eq_live_add_escape n T x)
    _ ≤ phase3LiveMass n T x +
        (expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) -
          phase3LiveMass n T x) := add_le_add_right hescape _
    _ = expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) :=
      add_tsub_cancel_of_le hlive

/-- `hfail` in the exact `ENNReal.ofReal` form consumed by `Phase3Bridge`. -/
theorem phase3_hfail_of_escapeSlack (n T x : ℕ) (h3 : 3 ≤ n)
    (hescape : Phase3EscapeSlack n T x) :
    (∑' z, if IsXMajority n z then 0 else iter (triChain n) T x z) ≤
      ENNReal.ofReal (phase3StoppedMoment n x T) := by
  rw [phase3StoppedMoment,
    ENNReal.ofReal_toReal (phase3Stop_expect_ne_top n T x h3)]
  exact phase3_failure_le_expect_of_escapeSlack n T x h3 hescape

/-- A `Phase3Bridge` whose recurrence and Markov conversion are discharged.
The sole remaining premise is the explicitly isolated escape-slack transfer
condition; it is not a renamed `hVstep` or `hfail`. -/
noncomputable def phase3Bridge_of_escapeSlack
    (C₃ n γ : ℕ) (h3 : 3 ≤ n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (hescape : ∀ x, Phase2Exit n γ x →
      Phase3EscapeSlack n (phase3Horizon C₃ n) x) :
    Phase3Bridge C₃ n γ where
  V := phase3StoppedMoment n
  hV0 := fun x hx => phase3StoppedMoment_zero_le n γ x h3 hsize hx
  hVstep := fun x _hx t => phase3StoppedMoment_step n x t h3
  hfail := fun x hx => phase3_hfail_of_escapeSlack n
    (phase3Horizon C₃ n) x h3 (hescape x hx)

/-- The killed potential cannot pointwise dominate every stopped failure state:
`x = 19` is an escaped non-consensus state at population `24`, but its killed
potential is zero. -/
theorem phase3_killed_potential_all_failure_false :
    ¬ (∀ z : ℕ, ¬ IsXMajority 24 z →
      1 ≤ phase3StoppedPotential 24 z) := by
  intro h
  have hnregion : ¬ Phase3Region 24 19 := by
    unfold Phase3Region
    omega
  have hbad := h 19 (by simp [IsXMajority])
  rw [phase3StoppedPotential_of_not_mem hnregion] at hbad
  norm_num at hbad

/-- Keeping the ordinary positive corrected potential on a frozen escape state
does not repair the problem: at `n = 24`, `x = 19`, a pure frozen step cannot
contract it by the strict factor `1 - (105/128)/24`. -/
theorem phase3_full_potential_frozen_step_false :
    ¬ (expect (phase3Stop 24 19) (phase3Potential 24) ≤
      phase3Factor 24 * phase3Potential 24 19) := by
  have hnregion : ¬ Phase3Region 24 19 := by
    unfold Phase3Region
    omega
  rw [phase3Stop, freeze_of_mem 19 hnregion, expect_pure,
    phase3Potential_apply (show 19 + 5 = 24 by norm_num)]
  intro hbad
  have hright : phase3Factor 24 *
      ENNReal.ofReal ((2 : ℝ) ^ 5 - 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (phase3Factor_ne_top 24) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hright hbad
  rw [ENNReal.toReal_mul, phase3Factor_toReal 24 (by norm_num),
    ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 : ℝ) ^ 5 - 1)] at hreal
  norm_num at hreal

/-- The phase-3 reachability theorem follows from the proved stopped recurrence
and Markov conversion once the single escape-slack family is supplied. -/
theorem hphase3_proved_of_escapeSlack
    (C₃ n₀ : ℕ) (hn₀ : 3 ≤ n₀)
    (hescape : ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → Phase2Exit n γ x →
      Phase3EscapeSlack n (phase3Horizon C₃ n) x) :
    ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      Reaches (triChain n) (phase3Horizon C₃ n) (Phase2Exit n γ)
        (IsXMajority n) (phase3Error C₃ n γ) := by
  apply hphase3_proved C₃ n₀ hn₀
  intro n γ hn hγ hsize
  exact phase3Bridge_of_escapeSlack C₃ n γ (hn₀.trans hn) hsize
    (fun x hx => hescape n γ x hn hγ hsize hx)

#print axioms phase3_step_six
#print axioms phase3_step_six_105_false
#print axioms phase3_pow_sub_one_le_half_mul
#print axioms phase3_absorption_six
#print axioms phase3_corrected_step_uniform_six
#print axioms phase3Region_iff_successors
#print axioms phase3Potential_apply
#print axioms phase3StoppedPotential_of_mem
#print axioms phase3StoppedPotential_of_not_mem
#print axioms phase3StoppedPotential_le
#print axioms phase3_factor_nonneg
#print axioms phase3Factor_toReal
#print axioms phase3Factor_ne_top
#print axioms expect_phase3Potential
#print axioms phase3Stop_step
#print axioms phase3Stop_expect_iter_le
#print axioms phase3StoppedPotential_ne_top
#print axioms phase3Stop_expect_ne_top
#print axioms phase3StoppedMoment_le
#print axioms phase3Stop_expect_step
#print axioms phase3StoppedMoment_step
#print axioms one_le_phase3StoppedPotential
#print axioms phase3Stop_live_mass_le_expect
#print axioms phase2Exit_eq_consensus_or_phase3Region
#print axioms phase3StoppedMoment_zero_le
#print axioms iter_triChain_consensus
#print axioms phase3_failure_le_stopped_failure
#print axioms phase3_stopped_failure_eq_live_add_escape
#print axioms phase3_failure_le_expect_add_escape
#print axioms phase3_failure_le_expect_of_escapeSlack
#print axioms phase3_hfail_of_escapeSlack
#print axioms phase3_killed_potential_all_failure_false
#print axioms phase3_full_potential_frozen_step_false
#print axioms hphase3_proved_of_escapeSlack

end Tri

/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Assembly
import Tri.Ladder
import Tri.ProdBound

/-!
# The phase-2 halving ladder for the Tri CRN

This module proves the CRN-specific one-step estimate used in phase 2.  In the
two-sided live region, the subtraction-free guard `4 * y <= n` makes the
productive direction at least `3 / 4`.  At base two the bracket is therefore at
most `7 / 8`, and `xy_ge_phase2` supplies the stage-dependent productive mass.
The resulting whole-interaction contraction factor is

    1 - 3 / 2^(s+5).

The exact-time stage theorem deliberately exposes the remaining stopped-chain
bridge.  The live region is not forward invariant, and freezing at the success
boundary does not transfer an exact-time success statement back to the original
chain.  Its hypotheses therefore state the global recurrence and the final
Markov/escape conversion explicitly, as `phase3_reaches` does for phase 3.

Finally, `phase2_reaches` composes these conditional halving stages with
`Reaches.chain`.  Its last arithmetic hypothesis says that the final dyadic
threshold lies below `gamma * lg n`.
-/

namespace Tri

open scoped ENNReal

/-- The dyadic phase-2 checkpoint saying `y <= n / 2^s`, written on the
`X`-coordinate without natural subtraction or division. -/
def Phase2Stage (n s x : ℕ) : Prop :=
  x ≤ n ∧ 2 ^ s * n ≤ 2 ^ s * x + n

/-- Membership in a dyadic phase-2 checkpoint is decidable. -/
instance (n s : ℕ) : DecidablePred (Phase2Stage n s) := by
  intro x
  unfold Phase2Stage
  infer_instance

/-- The subtraction-free form of the phase-2 direction guard `4 * y <= n`. -/
def Phase2Guard (n x : ℕ) : Prop :=
  x ≤ n ∧ 4 * n ≤ 4 * x + n

/-- Membership in the phase-2 direction guard is decidable. -/
instance (n : ℕ) : DecidablePred (Phase2Guard n) := by
  intro x
  unfold Phase2Guard
  infer_instance

/-- The two-sided live region for halving stage `s`: the run has not crossed
the `y <= n / 4` ruin guard and has not yet reached the next checkpoint. -/
def Phase2Live (n s x : ℕ) : Prop :=
  Phase2Guard n x ∧ ¬ Phase2Stage n (s + 1) x

/-- Membership in a phase-2 live region is decidable. -/
instance (n s : ℕ) : DecidablePred (Phase2Live n s) := by
  intro x
  unfold Phase2Live
  infer_instance

/-- The phase-2 bracket constants are exact: at success probability `3 / 4`,
base two has multiplier `7 / 8`, which is strictly below one. -/
theorem phase2_bracket_check :
    bracket 2 (3 / 4) = 7 / 8 ∧ bracket 2 (3 / 4) < 1 := by
  constructor
  · rw [bracket_two]
    norm_num
  · exact (bracket_two_lt_one_iff (3 / 4)).2 (by norm_num)

/-- Multiplying the bracket loss `1 / 8` by the productive-mass lower bound
`3 / 2^(s+2)` gives the advertised stage loss `3 / 2^(s+5)`. -/
theorem phase2_loss_check (s : ℕ) :
    (1 / 8 : ℝ) * (3 / (2 : ℝ) ^ (s + 2)) =
      3 / (2 : ℝ) ^ (s + 5) := by
  rw [show s + 5 = (s + 2) + 3 by omega, pow_add]
  norm_num
  ring

/-- A dyadic checkpoint gives the usual floor bound on the minority count,
when the physical population is written without subtraction. -/
theorem phase2_stage_minority_bound {n s a b : ℕ}
    (hpop : a + b + 2 = n) (hstage : Phase2Stage n s (a + 1)) :
    b + 1 ≤ n / 2 ^ s := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ s)).2
  have hs := hstage.2
  nlinarith

/-- Every checkpoint with `s >= 2` lies inside the subtraction-free phase-2
direction guard. -/
theorem phase2_stage_guard {n s x : ℕ} (hs : 2 ≤ s)
    (hstage : Phase2Stage n s x) : Phase2Guard n x := by
  rcases hstage with ⟨hxn, hstage⟩
  have hk : 4 ≤ 2 ^ s := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hs
  have hxnZ : (x : ℤ) ≤ n := by exact_mod_cast hxn
  have hkZ : (4 : ℤ) ≤ (2 ^ s : ℕ) := by exact_mod_cast hk
  have hstageZ : ((2 ^ s : ℕ) : ℤ) * n ≤
      ((2 ^ s : ℕ) : ℤ) * x + n := by exact_mod_cast hstage
  have hnonneg : 0 ≤ (((2 ^ s : ℕ) : ℤ) - 4) * ((n : ℤ) - x) :=
    mul_nonneg (sub_nonneg.mpr hkZ) (sub_nonneg.mpr hxnZ)
  constructor
  · exact hxn
  · exact_mod_cast (show (4 : ℤ) * n ≤ 4 * x + n by nlinarith)

/-- On a physical interior state, the two-sided live predicate gives exactly
the two arithmetic facts consumed by the local phase-2 estimate. -/
theorem phase2_live_bounds {n s a b : ℕ} (hpop : a + b + 2 = n)
    (hlive : Phase2Live n s (a + 1)) :
    4 * (b + 1) ≤ n ∧ 2 ^ (s + 1) * (b + 1) > n := by
  rcases hlive with ⟨hguard, hnot⟩
  have hsmall : 4 * (b + 1) ≤ n := by
    unfold Phase2Guard at hguard
    nlinarith
  have hx : a + 1 ≤ n := by omega
  have hcross : 2 ^ (s + 1) * (a + 1) + n <
      2 ^ (s + 1) * n := by
    apply Nat.lt_of_not_ge
    intro h
    exact hnot ⟨hx, h⟩
  constructor
  · exact hsmall
  · nlinarith

/-- The real three-atom moment of the next phase-2 minority potential. -/
noncomputable def phase2Moment (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 1)) : ℝ :=
  ENNReal.toReal (triStep (a + 1) (b + 1) h a) * (2 : ℝ) ^ (b + 2) +
    ENNReal.toReal (triStep (a + 1) (b + 1) h (a + 1)) *
      (2 : ℝ) ^ (b + 1) +
    ENNReal.toReal (triStep (a + 1) (b + 1) h (a + 2)) * (2 : ℝ) ^ b

/-- The paper's phase-2 product bound implies that a live stage-`s`
interaction is productive with probability at least `3 / 2^(s+2)`. -/
theorem phase2_productive_lower (a b n s : ℕ) (h3 : 3 ≤ n)
    (hpop : a + b + 2 = n) (hstage : 2 ^ (s + 1) * (b + 1) > n)
    (hmajor : 2 * (a + 1) ≥ n) :
    (3 : ℝ) / (2 : ℝ) ^ (s + 2) ≤
      ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a) +
        ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 2)) := by
  have f0 : triStep (a + 1) (b + 1) (by omega) a ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have f2 : triStep (a + 1) (b + 1) (by omega) (a + 2) ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have hqeq :
      ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a) +
          ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 2)) =
        (3 * ((a + 1 : ℕ) * (b + 1)) : ℝ) /
          ((n : ℝ) * (a + b + 1 : ℝ)) := by
    have hmass := productive_mass_closed a b n h3 hpop
    have hreal := congrArg ENNReal.toReal hmass
    rw [ENNReal.toReal_add f0 f2, ENNReal.toReal_div] at hreal
    simpa using hreal
  have hxy := xy_ge_phase2 hstage (by omega : (a + 1) + (b + 1) = n) hmajor
  rw [show 2 * s + 2 = (s + 1) + (s + 1) by omega, pow_add] at hxy
  let k : ℕ := 2 ^ (s + 1)
  change k * k * ((a + 1) * (b + 1)) + n * n > k * n * n at hxy
  have hk : 2 ≤ k := by
    dsimp [k]
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
      (show 1 ≤ s + 1 by omega)
  have htwo : 2 * (n * n) ≤ k * (n * n) := Nat.mul_le_mul_right (n * n) hk
  have hone : n * n ≤ k * k * ((a + 1) * (b + 1)) := by
    nlinarith
  have hscaled : k * (n * n) ≤
      k * (2 * k * ((a + 1) * (b + 1))) := by
    calc
      k * (n * n) ≤ k * k * ((a + 1) * (b + 1)) + n * n := by
        simpa [mul_assoc] using hxy.le
      _ ≤ k * k * ((a + 1) * (b + 1)) +
          k * k * ((a + 1) * (b + 1)) :=
        Nat.add_le_add_left hone _
      _ = k * (2 * k * ((a + 1) * (b + 1))) := by ring
  have hsq : n * n ≤ 2 * k * ((a + 1) * (b + 1)) := by
    exact Nat.le_of_mul_le_mul_left hscaled (by omega)
  have hden : n * (a + b + 1) ≤
      2 ^ (s + 2) * ((a + 1) * (b + 1)) := by
    calc
      n * (a + b + 1) ≤ n * n := Nat.mul_le_mul_left n (by omega)
      _ ≤ 2 * k * ((a + 1) * (b + 1)) := hsq
      _ = 2 ^ (s + 2) * ((a + 1) * (b + 1)) := by
        rw [show s + 2 = (s + 1) + 1 by omega, pow_add]
        simp [k]
        ring
  have hdenR : (n : ℝ) * (a + b + 1 : ℝ) ≤
      (2 : ℝ) ^ (s + 2) * ((a + 1 : ℝ) * (b + 1 : ℝ)) := by
    exact_mod_cast hden
  rw [hqeq]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (s + 2))
    (by positivity : (0 : ℝ) < (n : ℝ) * (a + b + 1 : ℝ))]
  calc
    (3 : ℝ) * ((n : ℝ) * (a + b + 1 : ℝ)) ≤
        3 * ((2 : ℝ) ^ (s + 2) *
          ((a + 1 : ℝ) * (b + 1 : ℝ))) :=
      mul_le_mul_of_nonneg_left hdenR (by norm_num)
    _ = (3 * ((a + 1 : ℕ) * (b + 1)) : ℝ) *
        (2 : ℝ) ^ (s + 2) := by
      push_cast
      ring

/-- **The CRN-specific phase-2 one-step contraction.**

On the explicitly two-sided live region, the down-probability conditional on a
productive step is at least `3 / 4`, while `xy_ge_phase2` gives productive mass
at least `3 / 2^(s+2)`.  Consequently the actual three-atom interaction kernel
contracts `2^y` by the factor `1 - 3 / 2^(s+5)`. -/
theorem phase2_halving_step (a b n s : ℕ) (h3 : 3 ≤ n)
    (hpop : a + b + 2 = n) (hlive : Phase2Live n s (a + 1)) :
    phase2Moment a b (by omega) ≤
      (2 : ℝ) ^ (b + 1) * (1 - 3 / (2 : ℝ) ^ (s + 5)) := by
  unfold phase2Moment
  let p0 : ℝ := ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a)
  let p1 : ℝ := ENNReal.toReal
    (triStep (a + 1) (b + 1) (by omega) (a + 1))
  let p2 : ℝ := ENNReal.toReal
    (triStep (a + 1) (b + 1) (by omega) (a + 2))
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
  obtain ⟨hsmall, hstage⟩ := phase2_live_bounds hpop hlive
  have hab : 3 * b ≤ a := by omega
  have hcounts : 3 * downCount a b ≤ upCount a b := by
    have ha := two_mul_choose_two_succ a
    have hb := two_mul_choose_two_succ b
    simp only [downCount, upCount]
    nlinarith [Nat.mul_le_mul_left ((a + 1) * (b + 1)) hab]
  have hcountsE :
      (3 : ℝ≥0∞) * (((a + 1) * Nat.choose (b + 1) 2 : ℕ) : ℝ≥0∞) ≤
        ((Nat.choose (a + 1) 2 * (b + 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hcounts
  push_cast at hcountsE
  have hdirE : (3 : ℝ≥0∞) * triStep (a + 1) (b + 1) (by omega) a ≤
      triStep (a + 1) (b + 1) (by omega) (a + 2) := by
    rw [triStep_down, triStep_up]
    push_cast
    simpa only [div_eq_mul_inv, mul_assoc] using
      mul_le_mul_left hcountsE
        (Nat.choose ((a + 1) + (b + 1)) 3 : ℝ≥0∞)⁻¹
  have hdir : 3 * p0 ≤ p2 := by
    have hreal := ENNReal.toReal_mono f2 hdirE
    rw [ENNReal.toReal_mul] at hreal
    simpa [p0, p2] using hreal
  have hq : (3 : ℝ) / (2 : ℝ) ^ (s + 2) ≤ p0 + p2 := by
    simpa [p0, p2] using phase2_productive_lower a b n s h3 hpop hstage
      (by omega)
  have hbracket : 2 * p0 + p1 + p2 / 2 ≤
      1 - (1 / 8 : ℝ) * (p0 + p2) := by
    nlinarith
  have hrate : 1 - (1 / 8 : ℝ) * (p0 + p2) ≤
      1 - 3 / (2 : ℝ) ^ (s + 5) := by
    have hscaled := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 1 / 8)
    calc
      1 - (1 / 8 : ℝ) * (p0 + p2) ≤
          1 - (1 / 8 : ℝ) * (3 / (2 : ℝ) ^ (s + 2)) :=
        sub_le_sub_left hscaled 1
      _ = 1 - 3 / (2 : ℝ) ^ (s + 5) := by rw [phase2_loss_check]
  dsimp [p0, p1, p2] at *
  calc
    ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a) *
          (2 : ℝ) ^ (b + 2) +
        ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 1)) *
          (2 : ℝ) ^ (b + 1) +
        ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 2)) *
          (2 : ℝ) ^ b =
        (2 : ℝ) ^ (b + 1) *
          (2 * ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a) +
            ENNReal.toReal
              (triStep (a + 1) (b + 1) (by omega) (a + 1)) +
            ENNReal.toReal
              (triStep (a + 1) (b + 1) (by omega) (a + 2)) / 2) := by
      rw [show b + 2 = (b + 1) + 1 by omega, pow_succ, pow_succ]
      ring
    _ ≤ (2 : ℝ) ^ (b + 1) *
        (1 - (1 / 8 : ℝ) *
          (ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a) +
            ENNReal.toReal
              (triStep (a + 1) (b + 1) (by omega) (a + 2)))) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ (2 : ℝ) ^ (b + 1) *
        (1 - 3 / (2 : ℝ) ^ (s + 5)) :=
      mul_le_mul_of_nonneg_left hrate (by positivity)

/-- The real contraction factor used by phase-2 stage `s`. -/
noncomputable def phase2Decay (s : ℕ) : ℝ :=
  1 - 3 / (2 : ℝ) ^ (s + 5)

/-- The explicit failure mass for a four-population-size interaction block in
one phase-2 halving stage. -/
noncomputable def phase2StageError (n s : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 : ℝ) ^ (n / 2 ^ s) * phase2Decay s ^ (4 * n)) /
    (2 : ℝ) ^ (n / 2 ^ (s + 1) + 1))

/-- **One conditional phase-2 halving stage for the actual Tri chain.**

Starting from `y <= n / 2^s`, a block of exactly `4 * n` interactions reaches
`y <= n / 2^(s+1)` with the displayed failure mass.  `hVstep` is the explicit
stopped-chain bridge from `phase2_halving_step` to a global recurrence; the
initial guard is supplied to make its domain visible.  `hfail` is the explicit
escape/Markov conversion at threshold `2^(floor(n/2^(s+1))+1)`. -/
theorem phase2_halving_stage (n s : ℕ) (hs : 2 ≤ s) (V : ℕ → ℕ → ℝ)
    (hV0 : ∀ x, Phase2Stage n s x →
      V x 0 ≤ (2 : ℝ) ^ (n / 2 ^ s))
    (hVstep : ∀ x, Phase2Stage n s x → Phase2Guard n x → ∀ t,
      V x (t + 1) ≤ phase2Decay s * V x t)
    (hfail : ∀ x, Phase2Stage n s x →
      ∑' z, (if Phase2Stage n (s + 1) z then 0
        else iter (triChain n) (4 * n) x z) ≤
          ENNReal.ofReal
            (V x (4 * n) / (2 : ℝ) ^ (n / 2 ^ (s + 1) + 1))) :
    Reaches (triChain n) (4 * n) (Phase2Stage n s)
      (Phase2Stage n (s + 1)) (phase2StageError n s) := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
  have hfactor : 0 ≤ phase2Decay s := by
    unfold phase2Decay
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (s + 5))).2
    rw [pow_add]
    norm_num
    nlinarith
  intro x hx
  have hiter : V x (4 * n) ≤
      V x 0 * phase2Decay s ^ (4 * n) := by
    have h := absorption_iterate (fun t => V x t) hfactor
      (hVstep x hx (phase2_stage_guard hs hx)) (4 * n)
    simpa [mul_comm] using h
  have hupper : V x (4 * n) ≤
      (2 : ℝ) ^ (n / 2 ^ s) * phase2Decay s ^ (4 * n) := by
    exact hiter.trans (mul_le_mul_of_nonneg_right (hV0 x hx)
      (pow_nonneg hfactor _))
  have hquot :
      V x (4 * n) / (2 : ℝ) ^ (n / 2 ^ (s + 1) + 1) ≤
        ((2 : ℝ) ^ (n / 2 ^ s) * phase2Decay s ^ (4 * n)) /
          (2 : ℝ) ^ (n / 2 ^ (s + 1) + 1) := by
    exact div_le_div_of_nonneg_right hupper (by positivity)
  calc
    ∑' z, (if Phase2Stage n (s + 1) z then 0
        else iter (triChain n) (4 * n) x z) ≤
        ENNReal.ofReal
          (V x (4 * n) / (2 : ℝ) ^ (n / 2 ^ (s + 1) + 1)) := hfail x hx
    _ ≤ ENNReal.ofReal
        (((2 : ℝ) ^ (n / 2 ^ s) * phase2Decay s ^ (4 * n)) /
          (2 : ℝ) ^ (n / 2 ^ (s + 1) + 1)) :=
      ENNReal.ofReal_le_ofReal hquot
    _ = phase2StageError n s := rfl

/-- A proper phase-1 exit lies in the first dyadic phase-2 checkpoint
`y <= n / 4`. -/
theorem phase1_exit_to_phase2_stage {n x : ℕ} (hx : Phase1Exit n x) :
    Phase2Stage n 2 x := by
  rcases hx with ⟨hxn, hx⟩
  constructor
  · exact hxn
  · norm_num
    nlinarith

/-- Once the final dyadic threshold is below `gamma * lg n`, its checkpoint is
contained in `Phase2Exit`. -/
theorem phase2_stage_to_phase2_exit {n γ s x : ℕ}
    (hthreshold : n / 2 ^ s ≤ γ * Nat.log 2 n)
    (hx : Phase2Stage n s x) : Phase2Exit n γ x := by
  constructor
  · exact hx.1
  · have hk : 0 < 2 ^ s := by positivity
    have hxnZ : (x : ℤ) ≤ n := by exact_mod_cast hx.1
    have hstageZ : ((2 ^ s : ℕ) : ℤ) * n ≤
        ((2 ^ s : ℕ) : ℤ) * x + n := by exact_mod_cast hx.2
    have hmulZ : ((2 ^ s : ℕ) : ℤ) * ((n : ℤ) - x) ≤ n := by
      nlinarith
    have hmul : 2 ^ s * (n - x) ≤ n := by
      have hsubZ : (((n - x : ℕ) : ℤ)) = (n : ℤ) - x :=
        Nat.cast_sub hx.1
      exact_mod_cast (show ((2 ^ s : ℕ) : ℤ) * ((n - x : ℕ) : ℤ) ≤ n by
        rw [hsubZ]
        exact hmulZ)
    have hminority : n - x ≤ n / 2 ^ s := by
      apply (Nat.le_div_iff_mul_le hk).2
      simpa [mul_comm] using hmul
    calc
      n ≤ x + n / 2 ^ s := by omega
      _ ≤ x + γ * Nat.log 2 n := Nat.add_le_add_left hthreshold x

/-- **Conditional composition of the complete phase-2 halving ladder.**

There are `k` stages, numbered `s = 2, ..., 2+k-1`, each using the explicit
`4*n` horizon and `phase2StageError`.  The three families of hypotheses are the
same stopped-recurrence and Markov/escape bridges exposed by
`phase2_halving_stage`.  `Reaches.chain` adds their horizons and failure masses.
-/
theorem phase2_reaches
    (n γ k : ℕ) (V : ℕ → ℕ → ℕ → ℝ)
    (hV0 : ∀ i < k, ∀ x, Phase2Stage n (2 + i) x →
      V i x 0 ≤ (2 : ℝ) ^ (n / 2 ^ (2 + i)))
    (hVstep : ∀ i < k, ∀ x, Phase2Stage n (2 + i) x →
      Phase2Guard n x → ∀ t,
        V i x (t + 1) ≤ phase2Decay (2 + i) * V i x t)
    (hfail : ∀ i < k, ∀ x, Phase2Stage n (2 + i) x →
      ∑' z, (if Phase2Stage n (2 + i + 1) z then 0
        else iter (triChain n) (4 * n) x z) ≤
          ENNReal.ofReal
            (V i x (4 * n) /
              (2 : ℝ) ^ (n / 2 ^ (2 + i + 1) + 1)))
    (hthreshold : n / 2 ^ (2 + k) ≤ γ * Nat.log 2 n) :
    Reaches (triChain n) (k * (4 * n)) (Phase1Exit n) (Phase2Exit n γ)
      (∑ i ∈ Finset.range k, phase2StageError n (2 + i)) := by
  have hrungs : ∀ i < k,
      Reaches (triChain n) (4 * n) (Phase2Stage n (2 + i))
        (Phase2Stage n (2 + (i + 1))) (phase2StageError n (2 + i)) := by
    intro i hi
    simpa [Nat.add_assoc] using
      phase2_halving_stage n (2 + i) (by omega) (V i)
        (hV0 i hi) (hVstep i hi) (hfail i hi)
  have hchain := Reaches.chain
    (K := triChain n) (P := fun i => Phase2Stage n (2 + i))
    (T := fun _ => 4 * n) (ε := fun i => phase2StageError n (2 + i)) hrungs
  have hchain' :
      Reaches (triChain n) (k * (4 * n)) (Phase2Stage n 2)
        (Phase2Stage n (2 + k))
        (∑ i ∈ Finset.range k, phase2StageError n (2 + i)) := by
    simpa using hchain
  have hpost := hchain'.mono_post (fun z hz =>
    phase2_stage_to_phase2_exit (s := 2 + k) hthreshold hz)
  intro x hx
  exact hpost x (phase1_exit_to_phase2_stage hx)

end Tri

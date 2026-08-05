/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PhaseGlue

/-!
# Inhabiting the phase-1 band bridge

This module constructs `Phase1BandBridge` with a fixed subtraction-free band:

* the lower boundary is `floor(n/2)`;
* the upper boundary is `ceil(5n/6)`, exactly the first `Phase1Exit` state;
* the return threshold is one state below that upper boundary.

The first-coordinate marginal of `bandCount` is `bandChain`, definitionally the
same doubly stopped kernel as `directionStop`.  Consequently the true signed
progress theorem `DirectionProgress.phase1_direction_progress` supplies the
substantive `Phase1BandBridge.hband` field.  The Feller term inside that theorem
pays for the lower boundary; `Phase1BandBridge.herror` adds the separate upper
return term required by `Reaches.of_bandCount_upper`.

## Residual

Every structure field is filled.  The only genuinely unproved probabilistic
input is `hdir`, the uniform live-band three-mass contraction

    down + stay*w + up*w^2 <= phi*w.

It is stated exactly in `phase1_bridge`.  `odds_cross_mul` fixes the direction
ratio and `band_rung_bound` proves the productive-clock estimate, but neither
alone proves this signed contraction.  No unsigned productive count is treated
as directional progress, and the proved-false
`phase1_productive_direction_false` is not used.
-/

namespace Tri

open scoped ENNReal

/-- The lower phase-1 safety boundary, `floor(n/2)`. -/
def phase1BandLo (n : ℕ) : ℕ := n / 2

/-- The complementary interior parameter at `phase1BandLo`. -/
def phase1BandMinority (n : ℕ) : ℕ := n - phase1BandLo n - 2

/-- The first integer `x` satisfying the phase-1 upper threshold
`5*n <= 6*x`, namely `ceil(5n/6)`. -/
def phase1Target (n : ℕ) : ℕ := (5 * n + 5) / 6

/-- The return threshold immediately below `phase1Target`. -/
def phase1ReturnLo (n : ℕ) : ℕ := phase1Target n - 1

/-- The complementary interior parameter at `phase1ReturnLo`. -/
def phase1ReturnMinority (n : ℕ) : ℕ := n - phase1ReturnLo n - 2

/-- The initial distance above the lower phase-1 boundary. -/
def phase1InitialRise (n x : ℕ) : ℕ := x - phase1BandLo n

/-- The remaining distance from `x` to the upper phase-1 boundary. -/
def phase1RemainingRise (n x : ℕ) : ℕ := phase1Target n - x

/-- A uniform error for reaching the upper boundary in the doubly stopped
chain.  It uses the worst admissible starting height `phase1BandLo n + 1`. -/
noncomputable def phase1SignedError
    (C₁ n γ : ℕ) (w φ : ℝ≥0∞) : ℝ≥0∞ :=
  ((phase1BandMinority n : ℝ≥0∞) / (phase1BandLo n : ℝ≥0∞)) ^ 1 +
    φ ^ phase1Horizon C₁ n γ * w ^ (phase1BandLo n + 1) /
      w ^ phase1Target n

/-- The full phase-1 bridge error: stopped signed progress plus the one-step
Feller ratio charged when transferring an upper hit back to `triChain`. -/
noncomputable def phase1BridgeError
    (C₁ n γ : ℕ) (w φ : ℝ≥0∞) : ℝ≥0∞ :=
  phase1SignedError C₁ n γ w φ +
    ((phase1ReturnMinority n : ℝ≥0∞) /
      (phase1ReturnLo n : ℝ≥0∞)) ^ 1

/-- The phase assumptions force a population of at least twelve.  This is the
only coarse size fact needed for positivity of all band parameters. -/
theorem phase1_size_ge_twelve {n γ : ℕ} (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) : 12 ≤ n := by
  have hlog1 : 1 ≤ Nat.log 2 n := by
    exact Nat.log_pos (by norm_num) (by omega)
  have hn6 : 6 ≤ n := by
    calc
      6 = 6 * 1 * 1 := by norm_num
      _ ≤ 6 * γ * Nat.log 2 n := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 6 hγ) hlog1
      _ ≤ n := hsize
  have hlog2 : 2 ≤ Nat.log 2 n := by
    exact Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  calc
    12 = 6 * 1 * 2 := by norm_num
    _ ≤ 6 * γ * Nat.log 2 n := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 6 hγ) hlog2
    _ ≤ n := hsize

/-- `phase1Target` is exactly the subtraction-free upper threshold. -/
theorem phase1Target_le_iff (n z : ℕ) :
    phase1Target n ≤ z ↔ 5 * n ≤ 6 * z := by
  unfold phase1Target
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < (6 : ℕ))]
  omega

/-- The phase-1 target is positive for every positive population. -/
theorem phase1Target_pos {n : ℕ} (hn : 0 < n) : 0 < phase1Target n := by
  by_contra h
  have ht : phase1Target n ≤ 0 := by omega
  have := (phase1Target_le_iff n 0).1 ht
  omega

/-- The return threshold is exactly one below the phase-1 target once the
population is positive. -/
theorem phase1ReturnLo_succ {n : ℕ} (hn : 0 < n) :
    phase1ReturnLo n + 1 = phase1Target n := by
  unfold phase1ReturnLo
  have := phase1Target_pos hn
  omega

/-- Arithmetic data for the lower stopped boundary. -/
theorem phase1BandLo_arithmetic {n : ℕ} (hn : 12 ≤ n) :
    phase1BandLo n + phase1BandMinority n + 2 = n ∧
      0 < phase1BandLo n ∧ 0 < phase1BandMinority n ∧
        phase1BandMinority n ≤ phase1BandLo n := by
  have hdecomp : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  have hmod : n % 2 < 2 := Nat.mod_lt n (by norm_num)
  have hhalf : 6 ≤ n / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by omega)
  simp only [phase1BandLo, phase1BandMinority]
  omega

/-- Arithmetic data for the return threshold immediately below the phase-1
target. -/
theorem phase1Return_arithmetic {n : ℕ} (hn : 12 ≤ n) :
    phase1ReturnLo n + phase1ReturnMinority n + 2 = n ∧
      0 < phase1ReturnLo n ∧ 0 < phase1ReturnMinority n ∧
        phase1ReturnMinority n ≤ phase1ReturnLo n ∧
          phase1ReturnLo n + 1 = phase1Target n ∧ phase1Target n ≤ n := by
  have hnpos : 0 < n := by omega
  have hsucc := phase1ReturnLo_succ hnpos
  have htargetThreshold : 5 * n ≤ 6 * phase1Target n :=
    (phase1Target_le_iff n (phase1Target n)).1 le_rfl
  have htargetLe : phase1Target n ≤ n - 2 := by
    unfold phase1Target
    rw [Nat.div_le_iff_le_mul (by norm_num : 0 < (6 : ℕ))]
    omega
  have htargetTwo : 2 ≤ phase1Target n := by
    by_contra h
    have hle : phase1Target n ≤ 1 := by omega
    have hbad := (phase1Target_le_iff n 1).1 hle
    omega
  unfold phase1ReturnMinority
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · have hn2 : n ≤ 2 * phase1Target n := by omega
    omega
  exact ⟨hsucc, by omega⟩

/-- An admissible phase-1 initial state is strictly above `floor(n/2)`. -/
theorem phase1_initial_above_lower {n γ x : ℕ} (h3 : 3 ≤ n)
    (hγ : 1 ≤ γ) (hx : AssemblyInitial n γ x) : phase1BandLo n < x := by
  obtain ⟨gap, hgap, hgapSq⟩ := hx.2
  have hnpos : 0 < n := by omega
  have hlog : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
  have hscale : 0 < γ * n * Nat.log 2 n := by positivity
  have hgapPos : 0 < gap := by
    by_contra hgap
    have hgapZero : gap = 0 := by omega
    subst gap
    exact (not_le_of_gt hscale) (by simpa using hgapSq)
  have hlower : 2 * phase1BandLo n ≤ n := by
    exact Nat.mul_div_le n 2
  omega

/-- Mapping the stopped counting chain to its first coordinate turns its upper
failure mass into the corresponding failure mass for `directionStop`. -/
theorem bandCount_upper_failure_eq_directionStop
    (n lower target T x c₀ : ℕ) :
    (∑' s, if target ≤ s.1 then 0 else
      iter (bandCount n lower target) T (x, c₀) s) =
      ∑' z, if target ≤ z then 0 else
        iter (directionStop n lower target) T x z := by
  let V : ℕ → ℝ≥0∞ := fun z => if target ≤ z then 0 else 1
  have hmap :
      (iter (bandCount n lower target) T (x, c₀)).map Prod.fst =
        iter (bandChain n lower target) T x :=
    iter_map_of_step_map _ _ _ (bandCount_map_fst n lower target) T _
  calc
    (∑' s, if target ≤ s.1 then 0 else
        iter (bandCount n lower target) T (x, c₀) s) =
        expect (iter (bandCount n lower target) T (x, c₀))
          (fun s => V s.1) := by
            unfold expect V
            apply tsum_congr
            intro s
            by_cases hs : target ≤ s.1 <;> simp [hs]
    _ = expect ((iter (bandCount n lower target) T
        (x, c₀)).map Prod.fst) V := by rw [expect_map]
    _ = expect (iter (bandChain n lower target) T x) V := by rw [hmap]
    _ = expect (iter (directionStop n lower target) T x) V := by rfl
    _ = ∑' z, if target ≤ z then 0 else
        iter (directionStop n lower target) T x z := by
          unfold expect V
          apply tsum_congr
          intro z
          by_cases hz : target ≤ z <;> simp [hz]

/-- The exact signed-progress error from an arbitrary admissible start is at
most the uniform error using the lowest possible start. -/
theorem phase1_direction_error_le
    (n x T : ℕ) (w φ : ℝ≥0∞)
    (hlower : phase1BandLo n < x)
    (hb : phase1BandMinority n ≤ phase1BandLo n)
    (hlowerPos : 0 < phase1BandLo n) (hw : w ≤ 1) :
    ((phase1BandMinority n : ℝ≥0∞) /
        (phase1BandLo n : ℝ≥0∞)) ^ phase1InitialRise n x +
      φ ^ T * w ^ x / w ^ phase1Target n ≤
        ((phase1BandMinority n : ℝ≥0∞) /
          (phase1BandLo n : ℝ≥0∞)) ^ 1 +
        φ ^ T * w ^ (phase1BandLo n + 1) / w ^ phase1Target n := by
  have hlower0 : (phase1BandLo n : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hlowerTop : (phase1BandLo n : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hbase : (phase1BandMinority n : ℝ≥0∞) /
      (phase1BandLo n : ℝ≥0∞) ≤ 1 := by
    calc
      (phase1BandMinority n : ℝ≥0∞) /
          (phase1BandLo n : ℝ≥0∞) ≤
          (phase1BandLo n : ℝ≥0∞) /
            (phase1BandLo n : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hb) _
      _ = 1 := ENNReal.div_self hlower0 hlowerTop
  have hrise : 1 ≤ phase1InitialRise n x := by
    unfold phase1InitialRise
    omega
  have hsafe := pow_le_pow_right_of_le_one' hbase hrise
  have hstart : phase1BandLo n + 1 ≤ x := by omega
  have hwpow : w ^ x ≤ w ^ (phase1BandLo n + 1) :=
    pow_le_pow_right_of_le_one' hw hstart
  exact add_le_add hsafe (ENNReal.div_le_div_right
    (mul_le_mul_right hwpow (φ ^ T)) _)

/-- **A concrete inhabitant of `Phase1BandBridge`.**

All arithmetic, projection, lower-safety, upper-return, and uniformisation
fields are proved.  The sole probabilistic premise `hdir` is the live-band
signed contraction consumed by
`DirectionProgress.phase1_direction_progress`. -/
noncomputable def phase1_bridge
    (C₁ n γ x : ℕ) (w φ : ℝ≥0∞)
    (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (hx : AssemblyInitial n γ x)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hdir : x < phase1Target n →
      ∀ (a b : ℕ) (hpop : a + b + 2 = n),
        phase1BandLo n < a + 1 → a + 1 < phase1Target n →
        triStep (a + 1) (b + 1) (by omega) a
            + triStep (a + 1) (b + 1) (by omega) (a + 1) * w
            + triStep (a + 1) (b + 1) (by omega) (a + 2) * w ^ 2
          ≤ φ * w) :
    Phase1BandBridge n x (phase1Horizon C₁ n γ)
      (phase1BridgeError C₁ n γ w φ) := by
  have hn12 := phase1_size_ge_twelve h3 hγ hsize
  obtain ⟨hlowerPop, hlowerPos, hbLowerPos, hbLowerMaj⟩ :=
    phase1BandLo_arithmetic hn12
  obtain ⟨hreturnPop, hreturnPos, hbReturnPos, hbReturnMaj,
      hreturnSucc, htargetN⟩ := phase1Return_arithmetic hn12
  have hxLower := phase1_initial_above_lower h3 hγ hx
  let T := phase1Horizon C₁ n γ
  let εsigned := phase1SignedError C₁ n γ w φ
  have hband : Reaches
      (bandCount n (phase1BandLo n) (phase1Target n)) T
      (fun s => s = (x, 0)) (fun s => 5 * n ≤ 6 * s.1) εsigned := by
    intro s hs
    subst s
    by_cases hxTarget : phase1Target n ≤ x
    · have hiter : iter (directionStop n (phase1BandLo n)
          (phase1Target n)) T x = PMF.pure x := by
        exact iter_freeze_of_mem x (Or.inr hxTarget) T
      calc
        (∑' z, if 5 * n ≤ 6 * z.1 then 0 else
            iter (bandCount n (phase1BandLo n) (phase1Target n)) T
              (x, 0) z) =
            ∑' z, if phase1Target n ≤ z.1 then 0 else
              iter (bandCount n (phase1BandLo n) (phase1Target n)) T
                (x, 0) z := by
                  apply tsum_congr
                  intro z
                  by_cases hz : phase1Target n ≤ z.1
                  · have hz' : 5 * n ≤ 6 * z.1 :=
                      (phase1Target_le_iff n z.1).1 hz
                    simp [hz, hz']
                  · have hz' : ¬ 5 * n ≤ 6 * z.1 := by
                      intro hz'
                      exact hz ((phase1Target_le_iff n z.1).2 hz')
                    simp [hz, hz']
        _ = ∑' z, if phase1Target n ≤ z then 0 else
              iter (directionStop n (phase1BandLo n) (phase1Target n)) T x z :=
          bandCount_upper_failure_eq_directionStop
            n (phase1BandLo n) (phase1Target n) T x 0
        _ = 0 := by
          rw [hiter, ENNReal.tsum_eq_zero]
          intro z
          by_cases hz : phase1Target n ≤ z
          · simp [hz]
          · have hzx : z ≠ x := by
              intro hzx
              subst z
              exact hz hxTarget
            simp [hz, PMF.pure_apply, hzx]
        _ ≤ εsigned := bot_le
    · have hxTarget' : x < phase1Target n := by omega
      have hk : phase1BandLo n + phase1InitialRise n x = x := by
        unfold phase1InitialRise
        omega
      have hkPos : 0 < phase1InitialRise n x := by
        unfold phase1InitialRise
        omega
      have hd : x + phase1RemainingRise n x = phase1Target n := by
        unfold phase1RemainingRise
        omega
      have hdPos : 0 < phase1RemainingRise n x := by
        unfold phase1RemainingRise
        omega
      have htargetSum : phase1BandLo n + phase1InitialRise n x +
          phase1RemainingRise n x = phase1Target n := by omega
      have hprogress := DirectionProgress.phase1_direction_progress
        n (phase1BandLo n) (phase1BandMinority n)
        (phase1InitialRise n x) (phase1RemainingRise n x) T h3 hlowerPop
        hlowerPos hbLowerPos hbLowerMaj hkPos hdPos
        (by simpa [htargetSum] using htargetN) w φ hw1 hw0 (by
          intro a b hpop haLo haHi
          apply hdir hxTarget' a b hpop haLo
          simpa [htargetSum] using haHi)
      have hprogress' :
          (∑' z, if phase1Target n ≤ z then 0 else
            iter (directionStop n (phase1BandLo n) (phase1Target n)) T x z) ≤
            ((phase1BandMinority n : ℝ≥0∞) /
              (phase1BandLo n : ℝ≥0∞)) ^ phase1InitialRise n x +
              φ ^ T * w ^ x / w ^ phase1Target n := by
        simpa only [hk, hd] using hprogress
      calc
        (∑' z, if 5 * n ≤ 6 * z.1 then 0 else
            iter (bandCount n (phase1BandLo n) (phase1Target n)) T
              (x, 0) z) =
            ∑' z, if phase1Target n ≤ z.1 then 0 else
              iter (bandCount n (phase1BandLo n) (phase1Target n)) T
                (x, 0) z := by
                  apply tsum_congr
                  intro z
                  by_cases hz : phase1Target n ≤ z.1
                  · have hz' : 5 * n ≤ 6 * z.1 :=
                      (phase1Target_le_iff n z.1).1 hz
                    simp [hz, hz']
                  · have hz' : ¬ 5 * n ≤ 6 * z.1 := by
                      intro hz'
                      exact hz ((phase1Target_le_iff n z.1).2 hz')
                    simp [hz, hz']
        _ = ∑' z, if phase1Target n ≤ z then 0 else
              iter (directionStop n (phase1BandLo n) (phase1Target n)) T x z :=
          bandCount_upper_failure_eq_directionStop
            n (phase1BandLo n) (phase1Target n) T x 0
        _ ≤ ((phase1BandMinority n : ℝ≥0∞) /
              (phase1BandLo n : ℝ≥0∞)) ^ phase1InitialRise n x +
              φ ^ T * w ^ x / w ^ phase1Target n := hprogress'
        _ ≤ εsigned := by
          exact phase1_direction_error_le n x T w φ hxLower hbLowerMaj
            hlowerPos hw1
  refine
    { bandLo := phase1BandLo n
      aHi := phase1Target n
      returnLo := phase1ReturnLo n
      bHi := phase1ReturnMinority n
      k := 1
      c₀ := 0
      εband := phase1SignedError C₁ n γ w φ
      hpop := hreturnPop
      hreturnLo := hreturnPos
      hbHi := hbReturnPos
      hmaj := hbReturnMaj
      hgap := by simpa using hreturnSucc.le
      hlower := by
        intro z hz
        have htargetZ := (phase1Target_le_iff n z).2 hz
        have hlowerTarget : phase1BandLo n < phase1Target n := by
          have hlowerTwice : 2 * phase1BandLo n ≤ n := Nat.mul_div_le n 2
          have htargetThreshold :=
            (phase1Target_le_iff n (phase1Target n)).1 le_rfl
          omega
        exact hlowerTarget.trans_le htargetZ
      hfailure := by
        intro z hz
        have hzTarget : ¬ phase1Target n ≤ z := by
          intro h
          exact hz ((phase1Target_le_iff n z).1 h)
        omega
      hband := by simpa [T, εsigned] using hband
      herror := by rfl }

/-- The exact phase-1 bridge family required by `theorem1b_of_fewer` is now
discharged from a family of live-band signed contractions. -/
noncomputable def hphase1_bridges_proved
    (C₁ n₀ : ℕ) (w φ : ℕ → ℕ → ℝ≥0∞) (hn₀ : 3 ≤ n₀)
    (hw1 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → w n γ ≤ 1)
    (hw0 : ∀ n γ : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → w n γ ≠ 0)
    (hdir : ∀ n γ x : ℕ, (hn : n₀ ≤ n) → (hγ : 1 ≤ γ) →
      (hsize : 6 * γ * Nat.log 2 n ≤ n) →
      (hx : AssemblyInitial n γ x) →
      x < phase1Target n →
      ∀ (a b : ℕ) (hpop : a + b + 2 = n),
        phase1BandLo n < a + 1 → a + 1 < phase1Target n →
        triStep (a + 1) (b + 1) (by omega) a
            + triStep (a + 1) (b + 1) (by omega) (a + 1) * w n γ
            + triStep (a + 1) (b + 1) (by omega) (a + 2) * (w n γ) ^ 2
          ≤ φ n γ * w n γ) :
    ∀ n γ x : ℕ, n₀ ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n → AssemblyInitial n γ x →
      Phase1BandBridge n x (phase1Horizon C₁ n γ)
        (phase1BridgeError C₁ n γ (w n γ) (φ n γ)) := by
  intro n γ x hn hγ hsize hx
  exact phase1_bridge C₁ n γ x (w n γ) (φ n γ) (hn₀.trans hn) hγ
    hsize hx (hw1 n γ hn hγ hsize) (hw0 n γ hn hγ hsize)
    (hdir n γ x hn hγ hsize hx)

#print axioms phase1_size_ge_twelve
#print axioms phase1Target_le_iff
#print axioms phase1Target_pos
#print axioms phase1ReturnLo_succ
#print axioms phase1BandLo_arithmetic
#print axioms phase1Return_arithmetic
#print axioms phase1_initial_above_lower
#print axioms bandCount_upper_failure_eq_directionStop
#print axioms phase1_direction_error_le
#print axioms phase1_bridge
#print axioms hphase1_bridges_proved

end Tri

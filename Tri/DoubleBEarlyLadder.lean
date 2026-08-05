/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBDirectionConstants
import Tri.Ladder
import Tri.Phase1Refactored

/-!
# The early Double-B geometric ladder

One dyadic stage of scale `q` is split into four narrow subrungs.  Their public
effective gaps are

```
4q, 5q, 6q, 7q, 8q.
```

Every subrung uses the symmetric lower gap `2q`, stops `q` levels above its
next public checkpoint, and therefore has total upward width exactly `2q`.
This is the geometry required by the joint occupation clock.  The fourth
checkpoint at scale `q` is definitionally the first checkpoint at scale `2q`.
-/

namespace Tri

open scoped BigOperators ENNReal

/-- Effective level of subcheckpoint `t` in an early stage of scale `q`. -/
def doubleEarlyLevel (n q t : ℕ) : ℕ :=
  n + (4 + t) * q

/-- State predicate at an early-stage subcheckpoint. -/
def DoubleEarlyCheckpoint (n q t : ℕ) (s : DoubleState n) : Prop :=
  doubleEarlyLevel n q t ≤ s.1.doubleLevel

instance (n q t : ℕ) :
    DecidablePred (DoubleEarlyCheckpoint n q t) := by
  intro s
  unfold DoubleEarlyCheckpoint
  infer_instance

/-- Exact error assigned to subrung `t` at scale `q`. -/
noncomputable def doubleEarlySubrungError
    (n q t : ℕ) : ℝ≥0∞ :=
  doubleBandSymmetricRungError
    n (2 * q) (n - 2 * q - 2) ((2 + t) * q)
    (n + (5 + t) * q - 1) (n - (5 + t) * q - 1) (q + 1)

/-- Sum of the four subrung errors in one dyadic stage. -/
noncomputable def doubleEarlyStageError
    (n q : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range 4, doubleEarlySubrungError n q t

/-- Raw interaction horizon of one four-subrung stage. -/
def doubleEarlyStageHorizon (n : ℕ) : ℕ :=
  4 * doubleClockHorizon n (4 * n)

/-- A single narrow early subrung.  The guard `72q ≤ n` is uniform over all
four positions and implies the blank-heavy restriction `8hi ≤ 9n`. -/
theorem doubleEarly_subrung
    (n : ℕ) (hn : 2 ≤ n) (q t : ℕ)
    (hq : 0 < q) (ht : t < 4) (hqSmall : 72 * q ≤ n) :
    Reaches (doubleStateStep n hn) (doubleClockHorizon n (4 * n))
      (DoubleEarlyCheckpoint n q t)
      (DoubleEarlyCheckpoint n q (t + 1))
      (doubleEarlySubrungError n q t) := by
  have htCases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases htCases with rfl | rfl | rfl | rfl
  · convert doubleBand_symmetric_rung
      n hn (2 * q) (n - 2 * q - 2) (n + 6 * q) (2 * q)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (n + 5 * q - 1) (n - 5 * q - 1) (q + 1)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) using 1
    all_goals
      funext s
      unfold DoubleEarlyCheckpoint doubleEarlyLevel
      apply propext
      omega
  · convert doubleBand_symmetric_rung
      n hn (2 * q) (n - 2 * q - 2) (n + 7 * q) (3 * q)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (n + 6 * q - 1) (n - 6 * q - 1) (q + 1)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) using 1
    all_goals
      funext s
      unfold DoubleEarlyCheckpoint doubleEarlyLevel
      apply propext
      omega
  · convert doubleBand_symmetric_rung
      n hn (2 * q) (n - 2 * q - 2) (n + 8 * q) (4 * q)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (n + 7 * q - 1) (n - 7 * q - 1) (q + 1)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) using 1
    all_goals
      funext s
      unfold DoubleEarlyCheckpoint doubleEarlyLevel
      apply propext
      omega
  · convert doubleBand_symmetric_rung
      n hn (2 * q) (n - 2 * q - 2) (n + 9 * q) (5 * q)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (n + 8 * q - 1) (n - 8 * q - 1) (q + 1)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) using 1
    all_goals
      funext s
      unfold DoubleEarlyCheckpoint doubleEarlyLevel
      apply propext
      omega

/-- The last checkpoint of a scale-`q` stage is the first checkpoint of the
next scale-`2q` stage. -/
theorem doubleEarlyLevel_four_eq_next
    (n q : ℕ) :
    doubleEarlyLevel n q 4 = doubleEarlyLevel n (2 * q) 0 := by
  simp [doubleEarlyLevel]
  ring

/-- Four narrow subrungs compose to one dyadic gap doubling. -/
theorem doubleEarly_stage
    (n : ℕ) (hn : 2 ≤ n) (q : ℕ)
    (hq : 0 < q) (hqSmall : 72 * q ≤ n) :
    Reaches (doubleStateStep n hn) (doubleEarlyStageHorizon n)
      (DoubleEarlyCheckpoint n q 0)
      (DoubleEarlyCheckpoint n (2 * q) 0)
      (doubleEarlyStageError n q) := by
  let P : ℕ → DoubleState n → Prop :=
    fun t => DoubleEarlyCheckpoint n q t
  let T : ℕ → ℕ := fun _ => doubleClockHorizon n (4 * n)
  let ε : ℕ → ℝ≥0∞ := fun t => doubleEarlySubrungError n q t
  have hrungs : ∀ t < 4,
      Reaches (doubleStateStep n hn) (T t) (P t) (P (t + 1)) (ε t) := by
    intro t ht
    exact doubleEarly_subrung n hn q t hq ht hqSmall
  have hchain :=
    Reaches.chain
      (K := doubleStateStep n hn) (P := P) (T := T) (ε := ε) hrungs
  have hchain' := hchain.mono_post (by
    intro s hs
    change doubleEarlyLevel n q 4 ≤ s.1.doubleLevel at hs
    change doubleEarlyLevel n (2 * q) 0 ≤ s.1.doubleLevel
    rwa [doubleEarlyLevel_four_eq_next] at hs)
  simpa [P, T, ε, doubleEarlyStageHorizon,
    doubleEarlyStageError] using hchain'

/-- The lower Feller term of every scale-`q` subrung costs at most the common
Gaussian envelope. -/
theorem doubleEarly_safety_le
    (n q k : ℕ) (hq : 0 < q) (hqSmall : 72 * q ≤ n)
    (hk : 2 * q ≤ k) :
    (((n - 2 * q - 2 : ℕ) : ℝ≥0∞) /
        ((n + 2 * q : ℕ) : ℝ≥0∞)) ^ k ≤
      ENNReal.ofReal
        (Real.exp (-((4 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ)))) := by
  have hn : 0 < n := by omega
  have hsub : 2 * q + 2 ≤ n := by omega
  have h2qN : 2 * q ≤ n := by omega
  have htwo : 2 ≤ n - 2 * q := by omega
  have hb : 0 < n - 2 * q - 2 := by omega
  apply ratio_pow_le_ofReal_exp
    (n + 2 * q) (n - 2 * q - 2) k
    ((4 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ)) hb (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqSmallR : (72 : ℝ) * q ≤ n := by exact_mod_cast hqSmall
  have hkR : (2 : ℝ) * q ≤ k := by exact_mod_cast hk
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub h2qN, Nat.cast_sub htwo]
  have haPos : (0 : ℝ) < n + 2 * q := by positivity
  rw [div_le_div_iff₀ hnR haPos]
  have haUpper : (n : ℝ) + 2 * q ≤ 2 * n := by
    linarith
  have hleft :=
    mul_le_mul_of_nonneg_left haUpper
      (show (0 : ℝ) ≤ 4 * q ^ 2 by positivity)
  have hfactor :=
    mul_le_mul_of_nonneg_right hkR
      (show (0 : ℝ) ≤ 4 * q + 2 by positivity)
  have hright :=
    mul_le_mul_of_nonneg_right hfactor hnR.le
  calc
    (4 : ℝ) * (q : ℝ) ^ 2 * ((n : ℝ) + 2 * q)
        ≤ 4 * q ^ 2 * (2 * n) := hleft
    _ ≤ (k : ℝ) *
          ((n : ℝ) + 2 * q - ((n : ℝ) - 2 * q - 2)) * n := by
      nlinarith

/-- The upper-return Feller term of a subrung whose next public gap lies
between `5q` and `8q` has the same Gaussian envelope. -/
theorem doubleEarly_return_le
    (n q d : ℕ) (hq : 0 < q) (hqSmall : 72 * q ≤ n)
    (hdLo : 5 * q ≤ d) (hdHi : d ≤ 8 * q) :
    (((n - d - 1 : ℕ) : ℝ≥0∞) /
        ((n + d - 1 : ℕ) : ℝ≥0∞)) ^ (q + 1) ≤
      ENNReal.ofReal
        (Real.exp (-((4 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ)))) := by
  have hn : 0 < n := by omega
  have hdN : d + 1 ≤ n := by omega
  have hdLe : d ≤ n := by omega
  have hone : 1 ≤ n - d := by omega
  have hb : 0 < n - d - 1 := by omega
  have haOne : 1 ≤ n + d := by omega
  apply ratio_pow_le_ofReal_exp
    (n + d - 1) (n - d - 1) (q + 1)
    ((4 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ)) hb (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqSmallR : (72 : ℝ) * q ≤ n := by exact_mod_cast hqSmall
  have hdLoR : (5 : ℝ) * q ≤ d := by exact_mod_cast hdLo
  have hdHiR : (d : ℝ) ≤ 8 * q := by exact_mod_cast hdHi
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub haOne, Nat.cast_sub hdLe, Nat.cast_sub hone]
  have haPos : (0 : ℝ) < n + d - 1 := by
    exact_mod_cast (show 0 < n + d - 1 by omega)
  rw [div_le_div_iff₀ hnR haPos]
  have haUpper : (n : ℝ) + d - 1 ≤ 2 * n := by
    linarith
  have hleft :=
    mul_le_mul_of_nonneg_left haUpper
      (show (0 : ℝ) ≤ 4 * q ^ 2 by positivity)
  have hqPlus : (q : ℝ) ≤ q + 1 := by linarith
  have hprod :=
    mul_le_mul hqPlus hdLoR
      (show (0 : ℝ) ≤ 5 * q by positivity)
      (show (0 : ℝ) ≤ q + 1 by positivity)
  have hfactor :
      8 * (q : ℝ) ^ 2 ≤ (q + 1) * (2 * d) := by
    nlinarith
  have hright :=
    mul_le_mul_of_nonneg_right hfactor hnR.le
  calc
    (4 : ℝ) * (q : ℝ) ^ 2 * ((n : ℝ) + d - 1)
        ≤ 4 * q ^ 2 * (2 * n) := hleft
    _ ≤ ((q : ℝ) + 1) *
          ((n : ℝ) + d - 1 - ((n : ℝ) - d - 1)) * n := by
      nlinarith

/-- One narrow subrung costs at most five copies of its common Gaussian
envelope: lower safety, three joint direction/clock terms, and upper return.
-/
theorem doubleEarlySubrungError_le
    (n q t : ℕ) (hq : 0 < q) (ht : t < 4)
    (hqSmall : 72 * q ≤ n) :
    doubleEarlySubrungError n q t ≤
      5 * ENNReal.ofReal
        (Real.exp (-((4 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ)))) := by
  let E : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-((4 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ))))
  have hsafety :=
    doubleEarly_safety_le n q ((2 + t) * q) hq hqSmall (by
      exact Nat.mul_le_mul_right q (by omega))
  let d := (5 + t) * q
  have hdLo : 5 * q ≤ d := by
    dsimp [d]
    exact Nat.mul_le_mul_right q (by omega)
  have hdHi : d ≤ 8 * q := by
    dsimp [d]
    exact Nat.mul_le_mul_right q (by omega)
  have hreturn :=
    doubleEarly_return_le n q d hq hqSmall hdLo hdHi
  unfold doubleEarlySubrungError doubleBandSymmetricRungError
  change
    ((((n - 2 * q - 2 : ℕ) : ℝ≥0∞) /
          ((n + 2 * q : ℕ) : ℝ≥0∞)) ^ ((2 + t) * q) +
        3 * ENNReal.ofReal
          (Real.exp (-(((2 * q : ℕ) : ℝ) ^ 2 / (n : ℝ))))) +
      (((n - (5 + t) * q - 1 : ℕ) : ℝ≥0∞) /
          ((n + (5 + t) * q - 1 : ℕ) : ℝ≥0∞)) ^ (q + 1) ≤
        5 * E
  have hE :
      ENNReal.ofReal
          (Real.exp (-(((2 * q : ℕ) : ℝ) ^ 2 / (n : ℝ)))) = E := by
    congr 3
    push_cast
    ring
  rw [hE]
  have hreturn' :
      (((n - (5 + t) * q - 1 : ℕ) : ℝ≥0∞) /
          ((n + (5 + t) * q - 1 : ℕ) : ℝ≥0∞)) ^ (q + 1) ≤ E := by
    simpa only [d, E] using hreturn
  calc
    ((((n - 2 * q - 2 : ℕ) : ℝ≥0∞) /
          ((n + 2 * q : ℕ) : ℝ≥0∞)) ^ ((2 + t) * q) +
        3 * E) +
        (((n - (5 + t) * q - 1 : ℕ) : ℝ≥0∞) /
          ((n + (5 + t) * q - 1 : ℕ) : ℝ≥0∞)) ^ (q + 1)
        ≤ (E + 3 * E) + E :=
      add_le_add (add_le_add hsafety le_rfl) hreturn'
    _ = 5 * E := by ring

/-- A four-subrung dyadic stage costs at most twenty copies of its Gaussian
envelope. -/
theorem doubleEarlyStageError_le
    (n q : ℕ) (hq : 0 < q) (hqSmall : 72 * q ≤ n) :
    doubleEarlyStageError n q ≤
      20 * ENNReal.ofReal
        (Real.exp (-((4 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ)))) := by
  unfold doubleEarlyStageError
  calc
    (∑ t ∈ Finset.range 4, doubleEarlySubrungError n q t)
        ≤ ∑ _t ∈ Finset.range 4,
            5 * ENNReal.ofReal
              (Real.exp (-((4 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ)))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact doubleEarlySubrungError_le n q t hq
        (Finset.mem_range.mp ht) hqSmall
    _ = 20 * ENNReal.ofReal
          (Real.exp (-((4 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ)))) := by
      simp
      ring

/-- Initial dyadic scale.  The `max 1` makes the outer search total even
outside the headline's large-`n` regime. -/
def doubleEarlySeedUnit (n γ : ℕ) : ℕ :=
  max 1 (phase1SeedR n γ / 4)

/-- Scale of outer dyadic stage `j`. -/
def doubleEarlyScale (n γ j : ℕ) : ℕ :=
  2 ^ j * doubleEarlySeedUnit n γ

/-- Real exponent scale of the first outer dyadic stage. -/
noncomputable def doubleEarlyEnvelopeScale (n γ : ℕ) : ℝ :=
  4 * (doubleEarlySeedUnit n γ : ℝ) ^ 2 / (n : ℝ)

/-- The fixed early-ladder target, a constant-fraction effective gap. -/
def doubleEarlyTarget (n : ℕ) : ℕ :=
  n + 4 * (n / 144)

/-- The dyadic scale doubles exactly between outer stages. -/
theorem doubleEarlyScale_succ (n γ j : ℕ) :
    doubleEarlyScale n γ (j + 1) = 2 * doubleEarlyScale n γ j := by
  unfold doubleEarlyScale
  rw [pow_succ]
  ring

/-- The initial scale is always positive. -/
theorem doubleEarlyScale_pos (n γ j : ℕ) :
    0 < doubleEarlyScale n γ j := by
  unfold doubleEarlyScale doubleEarlySeedUnit
  positivity

/-- The Gaussian exponent at outer stage `j` is `4^j` times the first-stage
exponent. -/
theorem doubleEarlyEnvelope_eq
    (n γ j : ℕ) :
    (4 : ℝ) * (doubleEarlyScale n γ j : ℝ) ^ 2 / (n : ℝ) =
      (4 : ℝ) ^ j * doubleEarlyEnvelopeScale n γ := by
  unfold doubleEarlyScale doubleEarlyEnvelopeScale
  push_cast
  have hpow : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul]
    calc
      (2 : ℝ) ^ (j * 2) = ((2 : ℝ) ^ 2) ^ j := by
        rw [← pow_mul, Nat.mul_comm]
      _ = (4 : ℝ) ^ j := by norm_num
  rw [mul_pow, hpow]
  ring

/-- At stage `lg n`, the dyadic scale has crossed `n/144`. -/
theorem doubleEarlyScale_at_log (n γ : ℕ) :
    n / 144 ≤ doubleEarlyScale n γ (Nat.log 2 n) := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hpow :
        n < 2 ^ (Nat.log 2 n + 1) := by
      simpa using Nat.lt_pow_succ_log_self
        (by norm_num : 1 < (2 : ℕ)) n
    have hhalf : n / 144 ≤ 2 ^ Nat.log 2 n := by
      rw [pow_succ] at hpow
      omega
    exact hhalf.trans (by
      unfold doubleEarlyScale doubleEarlySeedUnit
      calc
        2 ^ Nat.log 2 n = 2 ^ Nat.log 2 n * 1 := by simp
        _ ≤ 2 ^ Nat.log 2 n * max 1 (phase1SeedR n γ / 4) :=
          Nat.mul_le_mul_left (2 ^ Nat.log 2 n)
            (le_max_left 1 (phase1SeedR n γ / 4)))

/-- By stage `lg n`, the dyadic scale has crossed `n/144`. -/
theorem doubleEarlyScale_hits (n γ : ℕ) :
    ∃ j, n / 144 ≤ doubleEarlyScale n γ j := by
  exact ⟨Nat.log 2 n, doubleEarlyScale_at_log n γ⟩

/-- Number of genuinely small outer stages, chosen by first crossing of the
constant-fraction target scale. -/
def doubleEarlyStages (n γ : ℕ) : ℕ :=
  Nat.find (doubleEarlyScale_hits n γ)

/-- The selected final scale has crossed the target threshold. -/
theorem doubleEarlyScale_final (n γ : ℕ) :
    n / 144 ≤ doubleEarlyScale n γ (doubleEarlyStages n γ) := by
  exact Nat.find_spec (doubleEarlyScale_hits n γ)

/-- Every earlier scale is strictly below the target threshold. -/
theorem doubleEarlyScale_lt_final
    (n γ i : ℕ) (hi : i < doubleEarlyStages n γ) :
    doubleEarlyScale n γ i < n / 144 := by
  exact Nat.lt_of_not_ge
    (Nat.find_min (doubleEarlyScale_hits n γ) hi)

/-- The number of early stages is at most `lg n`. -/
theorem doubleEarlyStages_le_log (n γ : ℕ) :
    doubleEarlyStages n γ ≤ Nat.log 2 n := by
  exact Nat.find_min' (doubleEarlyScale_hits n γ)
    (doubleEarlyScale_at_log n γ)

/-- Every selected moving stage obeys the uniform blank-heavy width guard. -/
theorem doubleEarlyScale_small
    (n γ i : ℕ) (hi : i < doubleEarlyStages n γ) :
    72 * doubleEarlyScale n γ i ≤ n := by
  have hlt := doubleEarlyScale_lt_final n γ i hi
  calc
    72 * doubleEarlyScale n γ i ≤
        144 * doubleEarlyScale n γ i :=
      Nat.mul_le_mul_right _ (by norm_num)
    _ ≤ 144 * (n / 144) :=
      Nat.mul_le_mul_left 144 hlt.le
    _ ≤ n := Nat.mul_div_le _ _

/-- Total raw horizon of the selected early ladder. -/
def doubleEarlyLadderHorizon (n γ : ℕ) : ℕ :=
  doubleEarlyStages n γ * doubleEarlyStageHorizon n

/-- Sum of all selected stage errors. -/
noncomputable def doubleEarlyLadderError
    (n γ : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (doubleEarlyStages n γ),
    doubleEarlyStageError n (doubleEarlyScale n γ j)

/-- The selected dyadic stages compose to the constant-fraction early target.
-/
theorem doubleEarly_ladder
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ) :
    Reaches (doubleStateStep n hn) (doubleEarlyLadderHorizon n γ)
      (DoubleEarlyCheckpoint n (doubleEarlySeedUnit n γ) 0)
      (fun s => doubleEarlyTarget n ≤ s.1.doubleLevel)
      (doubleEarlyLadderError n γ) := by
  let P : ℕ → DoubleState n → Prop :=
    fun j => DoubleEarlyCheckpoint n (doubleEarlyScale n γ j) 0
  let T : ℕ → ℕ := fun _ => doubleEarlyStageHorizon n
  let ε : ℕ → ℝ≥0∞ :=
    fun j => doubleEarlyStageError n (doubleEarlyScale n γ j)
  have hrungs : ∀ j < doubleEarlyStages n γ,
      Reaches (doubleStateStep n hn) (T j) (P j) (P (j + 1)) (ε j) := by
    intro j hj
    have hr := doubleEarly_stage n hn (doubleEarlyScale n γ j)
      (doubleEarlyScale_pos n γ j) (doubleEarlyScale_small n γ j hj)
    have hscale := doubleEarlyScale_succ n γ j
    simpa only [P, T, ε, hscale] using hr
  have hchain :=
    Reaches.chain
      (K := doubleStateStep n hn) (P := P) (T := T) (ε := ε) hrungs
  have hpost := hchain.mono_post (by
    intro s hs
    change doubleEarlyLevel n
      (doubleEarlyScale n γ (doubleEarlyStages n γ)) 0 ≤
        s.1.doubleLevel at hs
    change doubleEarlyTarget n ≤ s.1.doubleLevel
    unfold doubleEarlyLevel at hs
    unfold doubleEarlyTarget
    have hfinal := doubleEarlyScale_final n γ
    omega)
  have hscaleZero :
      doubleEarlyScale n γ 0 = doubleEarlySeedUnit n γ := by
    simp [doubleEarlyScale]
  simpa [P, T, ε, hscaleZero, doubleEarlyLadderHorizon,
    doubleEarlyLadderError] using hpost

/-- Under the headline's large-size assumptions, the corrected square-root
seed is at least four. -/
theorem phase1SeedR_ge_four
    {n γ : ℕ} (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    4 ≤ phase1SeedR n γ := by
  have hn : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hrad : 4 ^ 2 ≤ phase1SeedRadicand n γ := by
    unfold phase1SeedRadicand
    calc
      4 ^ 2 ≤ 1 * 4096 * 12 := by norm_num
      _ ≤ γ * n * Nat.log 2 n :=
        Nat.mul_le_mul (Nat.mul_le_mul hγ hn) hlog
  have hsqrt : 4 ≤ Nat.sqrt (phase1SeedRadicand n γ) :=
    (Nat.le_sqrt').mpr hrad
  unfold phase1SeedR
  dsimp only
  split_ifs <;> omega

/-- The first early-stage Gaussian exponent retains one sixteenth of the
square-gap logarithmic scale. -/
theorem doubleEarlyEnvelopeScale_ge_natLog
    (n γ : ℕ) (hn : 0 < n) :
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 16 ≤
      doubleEarlyEnvelopeScale n γ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let q := doubleEarlySeedUnit n γ
  let seed := phase1SeedR n γ
  have hq1 : 1 ≤ q := by
    dsimp [q, doubleEarlySeedUnit]
    exact le_max_left _ _
  have hqDiv : phase1SeedR n γ / 4 ≤ q := by
    dsimp [q, doubleEarlySeedUnit]
    exact le_max_right _ _
  have hmod := Nat.mod_lt seed (by norm_num : 0 < 4)
  have hdecomp := Nat.mod_add_div seed 4
  have hseedQ : seed ≤ 8 * q := by omega
  have hseedSq : seed ^ 2 ≤ 64 * q ^ 2 := by
    have hp := Nat.pow_le_pow_left hseedQ 2
    nlinarith
  have hrad :
      γ * n * Nat.log 2 n ≤ 64 * q ^ 2 := by
    exact (phase1SeedRadicand_le_sq n γ).trans hseedSq
  have hradR :
      (γ : ℝ) * n * Nat.log 2 n ≤ 64 * (q : ℝ) ^ 2 := by
    exact_mod_cast hrad
  have hscale :
      (γ : ℝ) * Nat.log 2 n / 16 ≤
        4 * (q : ℝ) ^ 2 / (n : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 16) hnR]
    nlinarith
  simpa only [q, doubleEarlyEnvelopeScale] using hscale

/-- The first early-stage exponent is large enough for geometric summation.
-/
theorem doubleEarlyEnvelopeScale_ge_log_two_div_three
    {n γ : ℕ} (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    Real.log 2 / 3 ≤ doubleEarlyEnvelopeScale n γ := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size hlog
    omega
  have hmulNat : 12 ≤ γ * Nat.log 2 n :=
    calc
      12 = 1 * 12 := by norm_num
      _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
  have hmulR : (12 : ℝ) ≤ γ * Nat.log 2 n := by
    exact_mod_cast hmulNat
  have hlogQuarter : Real.log 2 / 3 ≤ (1 : ℝ) / 4 := by
    have hlogTwo : Real.log 2 ≤ (3 : ℝ) / 4 :=
      Real.log_two_lt_d9.le.trans (by norm_num)
    nlinarith
  have hquarter :
      (1 : ℝ) / 4 ≤ (γ : ℝ) * Nat.log 2 n / 16 := by
    nlinarith
  exact hlogQuarter.trans
    (hquarter.trans (doubleEarlyEnvelopeScale_ge_natLog n γ hnNat))

/-- The sum of selected early-stage errors is controlled by the first
Gaussian scale. -/
theorem doubleEarlyLadderError_le_first
    (n γ : ℕ) (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    doubleEarlyLadderError n γ ≤
      ENNReal.ofReal
        (40 * Real.exp (-doubleEarlyEnvelopeScale n γ)) := by
  unfold doubleEarlyLadderError
  calc
    (∑ j ∈ Finset.range (doubleEarlyStages n γ),
        doubleEarlyStageError n (doubleEarlyScale n γ j))
        ≤ ∑ j ∈ Finset.range (doubleEarlyStages n γ),
            ENNReal.ofReal
              (20 * Real.exp
                (-((4 : ℝ) ^ j * doubleEarlyEnvelopeScale n γ))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hstage :=
        doubleEarlyStageError_le n (doubleEarlyScale n γ j)
          (doubleEarlyScale_pos n γ j)
          (doubleEarlyScale_small n γ j (Finset.mem_range.mp hj))
      rw [doubleEarlyEnvelope_eq n γ j] at hstage
      simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20)] using hstage
    _ = ENNReal.ofReal
          (∑ j ∈ Finset.range (doubleEarlyStages n γ),
            20 * Real.exp
              (-((4 : ℝ) ^ j * doubleEarlyEnvelopeScale n γ))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j hj
      positivity
    _ ≤ ENNReal.ofReal
          (40 * Real.exp (-doubleEarlyEnvelopeScale n γ)) := by
      apply ENNReal.ofReal_le_ofReal
      have hsum :=
        phase1Envelope_sum_le
          (doubleEarlyEnvelopeScale_ge_log_two_div_three hlog hγ)
          (doubleEarlyStages n γ)
      have heq :
          (∑ j ∈ Finset.range (doubleEarlyStages n γ),
            20 * Real.exp
              (-((4 : ℝ) ^ j * doubleEarlyEnvelopeScale n γ))) =
            10 * (∑ j ∈ Finset.range (doubleEarlyStages n γ),
              2 * Real.exp
                (-((4 : ℝ) ^ j * doubleEarlyEnvelopeScale n γ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      rw [heq]
      nlinarith [Real.exp_pos (-doubleEarlyEnvelopeScale n γ)]

/-- Flooring the base-two logarithm still leaves the margin needed for the
early-ladder exponent `1/24`. -/
theorem doubleEarly_natLog_div_sixteen_ge_log_div_twentyfour
    {n : ℕ} (hlog : 12 ≤ Nat.log 2 n) :
    Real.log (n : ℝ) / 24 ≤ (Nat.log 2 n : ℝ) / 16 := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size hlog
    omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hpowUpper :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  have hpowUpperCast :
      (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast hpowUpper
  have hlogUpper :
      Real.log (n : ℝ) <
        ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 := by
    have h := Real.log_lt_log hnReal hpowUpperCast
    simpa only [Real.log_pow] using h
  have hlogTwo : Real.log 2 ≤ (0.6931471808 : ℝ) :=
    Real.log_two_lt_d9.le
  have hmulLog :
      ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        ((Nat.log 2 n + 1 : ℕ) : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hlogTwo (by positivity)
  have hlogCast : (12 : ℝ) ≤ Nat.log 2 n := by
    exact_mod_cast hlog
  have hcoefficient :
      16 * (((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2) ≤
        24 * (Nat.log 2 n : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hmulLog ⊢
    nlinarith
  nlinarith

/-- The first real Gaussian envelope is bounded by the coefficient-`40`,
exponent-`1/24` power law. -/
theorem doubleEarlyFirstEnvelope_le_power
    (n γ : ℕ) (hlog : 12 ≤ Nat.log 2 n) :
    ENNReal.ofReal
        (40 * Real.exp (-doubleEarlyEnvelopeScale n γ)) ≤
      40 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 24 : ℝ) * (γ : ℝ)) := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size hlog
    omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hmargin :=
    doubleEarly_natLog_div_sixteen_ge_log_div_twentyfour hlog
  have hmarginMul :
      (γ : ℝ) * (Real.log (n : ℝ) / 24) ≤
        (γ : ℝ) * ((Nat.log 2 n : ℝ) / 16) :=
    mul_le_mul_of_nonneg_left hmargin (by positivity)
  have htarget :
      Real.log (n : ℝ) * ((1 / 24 : ℝ) * (γ : ℝ)) ≤
        doubleEarlyEnvelopeScale n γ := by
    calc
      Real.log (n : ℝ) * ((1 / 24 : ℝ) * (γ : ℝ)) =
          (γ : ℝ) * (Real.log (n : ℝ) / 24) := by ring
      _ ≤ (γ : ℝ) * ((Nat.log 2 n : ℝ) / 16) := hmarginMul
      _ = (γ : ℝ) * (Nat.log 2 n : ℝ) / 16 := by ring
      _ ≤ doubleEarlyEnvelopeScale n γ :=
        doubleEarlyEnvelopeScale_ge_natLog n γ hnNat
  have hexp :
      Real.exp (-doubleEarlyEnvelopeScale n γ) ≤
        ((n : ℝ)⁻¹) ^ ((1 / 24 : ℝ) * (γ : ℝ)) := by
    calc
      Real.exp (-doubleEarlyEnvelopeScale n γ) ≤
          Real.exp
            (-Real.log (n : ℝ) * ((1 / 24 : ℝ) * (γ : ℝ))) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = ((n : ℝ)⁻¹) ^ ((1 / 24 : ℝ) * (γ : ℝ)) := by
        rw [Real.rpow_def_of_pos (inv_pos.mpr hnReal), Real.log_inv]
  calc
    ENNReal.ofReal
        (40 * Real.exp (-doubleEarlyEnvelopeScale n γ)) ≤
        ENNReal.ofReal
          (40 * ((n : ℝ)⁻¹) ^ ((1 / 24 : ℝ) * (γ : ℝ))) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hexp (by norm_num))
    _ = 40 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 24 : ℝ) * (γ : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 40)]
      norm_num only [ENNReal.ofReal_ofNat]
      rw [← ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hnReal),
        ENNReal.ofReal_inv_of_pos hnReal, ENNReal.ofReal_natCast]

/-- The complete early Double-B ladder has an explicit power-law failure
budget. -/
theorem doubleEarlyLadderError_le_power
    (n γ : ℕ) (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    doubleEarlyLadderError n γ ≤
      40 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 24 : ℝ) * (γ : ℝ)) := by
  exact (doubleEarlyLadderError_le_first n γ hlog hγ).trans
    (doubleEarlyFirstEnvelope_le_power n γ hlog)

/-- A paper-style initial gap lies above the first early checkpoint. -/
theorem doubleEarlyCheckpoint_zero_of_gap
    (n γ : ℕ) (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (s : DoubleState n) (gap : ℕ)
    (hlevel : n + gap ≤ s.1.doubleLevel)
    (hgapSq : γ * n * Nat.log 2 n ≤ gap ^ 2) :
    DoubleEarlyCheckpoint n (doubleEarlySeedUnit n γ) 0 s := by
  have hseedGap : phase1SeedR n γ ≤ gap :=
    phase1SeedR_le_of_sq
      (by simpa [phase1SeedRadicand] using hgapSq)
  have hseedFour := phase1SeedR_ge_four hlog hγ
  have hunit :
      doubleEarlySeedUnit n γ = phase1SeedR n γ / 4 := by
    unfold doubleEarlySeedUnit
    rw [max_eq_right]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
    simpa using hseedFour
  have hfour :
      4 * doubleEarlySeedUnit n γ ≤ phase1SeedR n γ := by
    rw [hunit]
    exact Nat.mul_div_le _ _
  unfold DoubleEarlyCheckpoint doubleEarlyLevel
  omega

/-- Initial-state predicate used by the unconditional early-ladder theorem. -/
def DoubleBEarlyInitial (n γ : ℕ) (s : DoubleState n) : Prop :=
  ∃ gap : ℕ,
    n + gap ≤ s.1.doubleLevel ∧
      γ * n * Nat.log 2 n ≤ gap ^ 2

/-- The complete early ladder starts directly from the paper's initial gap
condition. -/
theorem doubleEarly_reaches
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    Reaches (doubleStateStep n hn) (doubleEarlyLadderHorizon n γ)
      (DoubleBEarlyInitial n γ)
      (fun s => doubleEarlyTarget n ≤ s.1.doubleLevel)
      (doubleEarlyLadderError n γ) := by
  have hl := doubleEarly_ladder n hn γ
  intro s hs
  obtain ⟨gap, hlevel, hgapSq⟩ := hs
  exact hl s
    (doubleEarlyCheckpoint_zero_of_gap
      n γ hlog hγ s gap hlevel hgapSq)

end Tri

#print axioms Tri.doubleEarly_subrung
#print axioms Tri.doubleEarly_stage
#print axioms Tri.doubleEarlySubrungError_le
#print axioms Tri.doubleEarlyLadderError_le_first
#print axioms Tri.doubleEarlyEnvelopeScale_ge_natLog
#print axioms Tri.doubleEarly_natLog_div_sixteen_ge_log_div_twentyfour
#print axioms Tri.doubleEarlyFirstEnvelope_le_power
#print axioms Tri.doubleEarlyLadderError_le_power
#print axioms Tri.doubleEarly_ladder
#print axioms Tri.doubleEarly_reaches

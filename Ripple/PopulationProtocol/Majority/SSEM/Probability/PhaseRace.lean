/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generic Phase Race Lemma

Protocol-independent "good before bad" probability bounds for finite windows.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Probability.ExpectedTime

namespace SSEM
namespace Probability

open scoped ENNReal
open PMF

variable {Q X Y : Type*} {n : ℕ}

/-- Probability that `G` has been hit by time `K` while `D` has not been hit
by time `K`.  This is represented by the two-hit-flag chain. -/
noncomputable def ProbGoodBeforeBad
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (G D : Config Q X n → Prop)
    (K : ℕ) : ENNReal :=
  (hitTwoFlagDist P hn C₀ G D K).toOuterMeasure
    {S : Config Q X n × (Bool × Bool) |
      S.2.1 = true ∧ S.2.2 = false}

/-- Markov tail bound at a positive finite window:
`P[T > K] ≤ E[T] / K`.  The tail-sum definition actually gives the slightly
stronger `E[T] ≥ (K + 1) P[T > K]`; this positive-window form matches the
phase-race statements. -/
theorem probNotHitBy_le_expectedHittingTime_div_window
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K : ℕ) [NeZero K] :
    probNotHitBy P hn C₀ Goal K ≤
      expectedHittingTime P hn C₀ Goal / (K : ENNReal) := by
  have htail :
      probNotHitBy P hn C₀ Goal K ≤
        probNotHitBy P hn C₀ Goal (K - 1) :=
    probNotHitBy_le_of_le P hn C₀ Goal (by omega)
  have hmul_prev :=
    probNotHitBy_le_expectedHittingTime_div P hn C₀ Goal (K - 1)
  have hKcast :
      (((K - 1 + 1 : ℕ) : ENNReal)) = (K : ENNReal) := by
    congr
    exact Nat.sub_one_add_one (NeZero.ne K)
  have hmul :
      probNotHitBy P hn C₀ Goal K * (K : ENNReal) ≤
        expectedHittingTime P hn C₀ Goal := by
    calc
      probNotHitBy P hn C₀ Goal K * (K : ENNReal)
          ≤ probNotHitBy P hn C₀ Goal (K - 1) * (K : ENNReal) :=
            by simpa [mul_comm] using
              mul_le_mul_right htail (K : ENNReal)
      _ = probNotHitBy P hn C₀ Goal (K - 1) *
            (((K - 1 + 1 : ℕ) : ENNReal)) := by
            rw [hKcast]
      _ ≤ expectedHittingTime P hn C₀ Goal := hmul_prev
  have hK0 : (K : ENNReal) ≠ 0 := by
    exact_mod_cast (NeZero.ne K)
  have hKtop : (K : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top K
  exact (ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl hKtop)).2 hmul

/-- General Markov lower bound:
`P[T ≤ K] ≥ 1 - E[T]/K`.  The `K = 0` case is handled separately using
the zero tail term of the tail-sum expectation. -/
theorem ProbHitWithin_ge_one_sub_expectedHittingTime_div
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K : ℕ) :
    1 - expectedHittingTime P hn C₀ Goal / (K : ENNReal) ≤
      ProbHitWithin P hn C₀ Goal K := by
  by_cases hK : K = 0
  · subst K
    by_cases hE : expectedHittingTime P hn C₀ Goal = 0
    · have htail0_le :
          probNotHitBy P hn C₀ Goal 0 ≤
            expectedHittingTime P hn C₀ Goal := by
        rw [expectedHittingTime]
        exact ENNReal.le_tsum 0
      have htail0_zero : probNotHitBy P hn C₀ Goal 0 = 0 :=
        le_antisymm (by simpa [hE] using htail0_le) zero_le
      rw [ProbHitWithin_eq_one_sub_probNotHitBy, htail0_zero, hE]
      simp
    · rw [show ((0 : ℕ) : ENNReal) = 0 by norm_num, ENNReal.div_zero hE]
      simp
  · haveI : NeZero K := ⟨hK⟩
    exact ProbHitWithin_ge_one_sub_of_probNotHitBy_le P hn C₀ Goal K
      (probNotHitBy_le_expectedHittingTime_div_window P hn C₀ Goal K)

/-- The hit event for `G ∨ D` is covered by "good hit and no bad hit" plus
the bad-hit event. -/
theorem ProbHitWithin_or_le_ProbGoodBeforeBad_add_bad
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (G D : Config Q X n → Prop)
    (K : ℕ) :
    ProbHitWithin P hn C₀ (fun C => G C ∨ D C) K ≤
      ProbGoodBeforeBad P hn C₀ G D K +
        ProbHitWithin P hn C₀ D K := by
  classical
  let μ := hitTwoFlagDist P hn C₀ G D K
  have hGood :
      ProbGoodBeforeBad P hn C₀ G D K =
        μ.toOuterMeasure
          {S : Config Q X n × (Bool × Bool) |
            S.2.1 = true ∧ S.2.2 = false} := rfl
  have hOr :
      ProbHitWithin P hn C₀ (fun C => G C ∨ D C) K =
        μ.toOuterMeasure
          {S : Config Q X n × (Bool × Bool) |
            S.2.1 || S.2.2 = true} := by
    rw [ProbHitWithin, probHitBy_eq_hitFlagDist_toOuterMeasure,
      ← hitTwoFlagDist_map_or P hn C₀ G D K, PMF.toOuterMeasure_map_apply]
    congr 1
    ext ⟨_C, g, d⟩
    simp [Bool.or_eq_true]
  have hBad :
      ProbHitWithin P hn C₀ D K =
        μ.toOuterMeasure
          {S : Config Q X n × (Bool × Bool) | S.2.2 = true} := by
    rw [ProbHitWithin, probHitBy_eq_hitFlagDist_toOuterMeasure,
      ← hitTwoFlagDist_map_right P hn C₀ G D K, PMF.toOuterMeasure_map_apply]
    simp [μ]
  rw [hOr, hBad, hGood]
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro S
  rcases S with ⟨C, g, d⟩
  cases g <;> cases d <;> simp

/-- Generic phase-race lemma: if the union target `G ∪ D` has expected hitting
time at most `B`, and the bad target has finite-window probability at most
`δ`, then the probability of hitting `G` by time `K` while avoiding `D` through
time `K` is at least `1 - B/K - δ`. -/
theorem probHit_good_before_bad_ge
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (G D : Config Q X n → Prop)
    (K : ℕ) (B δ : ENNReal)
    (hExp :
      expectedHittingTime P hn C₀ (fun C => G C ∨ D C) ≤ B)
    (hBad : ProbHitWithin P hn C₀ D K ≤ δ) :
    1 - B / (K : ENNReal) - δ ≤
      ProbGoodBeforeBad P hn C₀ G D K := by
  have hdiv :
      expectedHittingTime P hn C₀ (fun C => G C ∨ D C) / (K : ENNReal) ≤
        B / (K : ENNReal) :=
    ENNReal.div_le_div_right hExp (K : ENNReal)
  have hMarkov :
      1 - B / (K : ENNReal) ≤
        ProbHitWithin P hn C₀ (fun C => G C ∨ D C) K :=
    (tsub_le_tsub_left hdiv 1).trans
      (ProbHitWithin_ge_one_sub_expectedHittingTime_div
        P hn C₀ (fun C => G C ∨ D C) K)
  have hCover :
      ProbHitWithin P hn C₀ (fun C => G C ∨ D C) K ≤
        ProbGoodBeforeBad P hn C₀ G D K +
          ProbHitWithin P hn C₀ D K :=
    ProbHitWithin_or_le_ProbGoodBeforeBad_add_bad P hn C₀ G D K
  have hMain :
      1 - B / (K : ENNReal) ≤
        ProbGoodBeforeBad P hn C₀ G D K + δ := by
    calc
      1 - B / (K : ENNReal)
          ≤ ProbHitWithin P hn C₀ (fun C => G C ∨ D C) K := hMarkov
      _ ≤ ProbGoodBeforeBad P hn C₀ G D K +
            ProbHitWithin P hn C₀ D K := hCover
      _ ≤ ProbGoodBeforeBad P hn C₀ G D K + δ :=
            add_le_add_right hBad _
  exact (tsub_le_iff_right).2 hMain

end Probability
end SSEM

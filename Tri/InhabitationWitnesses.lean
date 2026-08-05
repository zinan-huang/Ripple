/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem4Statement
import Tri.Theorem2
import Tri.MultiTheorem5

/-!
# Concrete inhabitation witnesses

The examples below show that the numerical and state predicates appearing in
the paper-facing theorem statements are jointly satisfiable.  They are sanity
checks against vacuous interfaces, not substitutes for the general theorems.
-/

namespace Tri

/-- Theorem 4: the exact requested witness, including both entry-side
conditions and a positive Byzantine population. -/
example :
    3 ≤ (2 ^ 20 : ℕ) ∧
      1 ≤ (1 : ℕ) ∧
      6 * 1 * Nat.log 2 (2 ^ 20) ≤ 2 ^ 20 ∧
      68 * 1 * Nat.log 2 (2 ^ 20) + 1 ≤ 3 * (2 ^ 20) ∧
      1 ≤ (286 : ℕ) ∧
      Theorem4PaperInitial
        (2 ^ 20) 1 526578 521712 286 4580 := by
  have hlog : Nat.log 2 (2 ^ 20) = 20 := by
    simpa using (Nat.log_pow (b := 2) (by norm_num) 20)
  simp only [Theorem4PaperInitial]
  rw [hlog]
  norm_num

/-- Single-B: a physical state with one genuine blank and the full local
side-condition bundle used by `Theorem2_singleB_statement`. -/
example :
    let s : BiCfg := ⟨43, 20, 1⟩
    3 ≤ (64 : ℕ) ∧
      1 ≤ (1 : ℕ) ∧
      6 * 1 * Nat.log 2 64 ≤ 64 ∧
      s.DoubleInv 64 ∧
      1 ≤ s.b ∧
      SingleBPaperInitial 64 1 s := by
  dsimp only
  simp only [SingleBPaperInitial, DoubleBPaperInitial]
  have hlog : Nat.log 2 64 = 6 := by decide
  rw [hlog]
  refine ⟨by norm_num, by norm_num, by norm_num,
    by norm_num [BiCfg.DoubleInv], by norm_num, ?_⟩
  refine ⟨by norm_num, 20, by norm_num, by norm_num⟩

/-- Heavy-B: a physical state with one genuine heavy blank.  In particular,
the actual paper premise here is `4 * b ≤ n`. -/
example :
    let s : BiCfg := ⟨42, 20, 1⟩
    3 ≤ (64 : ℕ) ∧
      1 ≤ (1 : ℕ) ∧
      6 * 1 * Nat.log 2 64 ≤ 64 ∧
      s.HeavyInv 64 ∧
      1 ≤ s.b ∧
      HeavyBPaperInitial 64 1 s := by
  dsimp only
  simp only [HeavyBPaperInitial]
  have hlog : Nat.log 2 64 = 6 := by decide
  rw [hlog]
  refine ⟨by norm_num, by norm_num, by norm_num,
    by norm_num [BiCfg.HeavyInv], by norm_num, ?_⟩
  refine ⟨by norm_num, 20, by norm_num, by norm_num⟩

end Tri

namespace Tri.Multi

/-- Theorem 5: a genuinely three-species configuration satisfying every
concrete numerical premise and the pairwise-gap premise.  Both competitors
have positive population, so neither `m ≥ 3` nor `HasPairwiseGap` is vacuous. -/
example :
    ∃ q : Config 3 256,
      3 ≤ (3 : ℕ) ∧
        3 ≤ (256 : ℕ) ∧
        1 ≤ (1 : ℕ) ∧
        4 ≤ (48 : ℕ) ∧
        48 ≤ 256 ∧
        3 * 48 ≤ 256 ∧
        6 ≤ 1 * Nat.log 2 256 ∧
        6 * 1 * Nat.log 2 256 ≤ 256 ∧
        3 * (1 * Nat.log 2 256) ≤ 256 ∧
        1 * 256 * Nat.log 2 256 ≤ 48 ^ 2 ∧
        HasPairwiseGap q (0 : Species 3) 48 ∧
        0 < count q (1 : Species 3) ∧
        0 < count q (2 : Species 3) := by
  let q : Config 3 256 :=
    ⟨fun i => if i = (0 : Species 3) then 120 else 68, by decide⟩
  have hlog : Nat.log 2 256 = 8 := by decide
  have hgap : HasPairwiseGap q (0 : Species 3) 48 := by
    unfold HasPairwiseGap
    intro Y hY
    norm_num [q, count, hY]
  refine ⟨q, ?_⟩
  rw [hlog]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, hgap, ?_, ?_⟩
  · -- the `if` is on `Fin 3` indices; `decide` evaluates it, `norm_num` alone does not.
    simp only [q, count]
    decide
  · simp only [q, count]
    decide

end Tri.Multi

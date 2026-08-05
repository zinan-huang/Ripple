/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BiChain
import Tri.HeavyBChain
import Tri.SingleBKernel
import Tri.Decay
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# A formal statement of Theorem 2 (bi-molecular, Double-B)

This records the faithful, explicit-constant formulation of Theorem 2 of
Condon--Hajiaghayi--Kirkpatrick--Mañuch for the Double-B bi-molecular CRN,
mirroring `Theorem1a_statement` / `Theorem1b_statement`.  The proposition is
recorded as a **definition** and is not proved here; its proof is the
resolution-event-time three-phase argument at effective population `2n`, whose
safety analysis (`doubleB_ruin` etc.) is already in place.
-/

namespace Tri

open scoped ENNReal

/-- All-`X` consensus for a Double-B configuration: every molecule is `X`. -/
def BiXConsensus (n : ℕ) (z : BiCfg) : Prop := z.x = n ∧ z.y = 0 ∧ z.b = 0

instance (n : ℕ) (z : BiCfg) : Decidable (BiXConsensus n z) := by
  unfold BiXConsensus; infer_instance

/-- The exact finite initial-state assumptions of the paper's Double-B clause.
At least half of the population is active (`2b ≤ n`), and the ordinary
opinion gap `x-y` has the required square-root size. -/
def DoubleBPaperInitial (n γ : ℕ) (s : BiCfg) : Prop :=
  2 * s.b ≤ n ∧
    ∃ g : ℕ,
      s.y + g ≤ s.x ∧
        γ * n * Nat.log 2 n ≤ g ^ 2

/-- Regression witness: the paper premise allows initial blanks that the old
stronger condition `n+g ≤ 2x` incorrectly excluded. -/
theorem doubleBPaperInitial_not_oldExample :
    let s : BiCfg := ⟨34, 14, 16⟩
    s.DoubleInv 64 ∧
      DoubleBPaperInitial 64 1 s ∧
      ¬ ∃ g : ℕ,
        64 + g ≤ 2 * s.x ∧
          1 * 64 * Nat.log 2 64 ≤ g ^ 2 := by
  dsimp only
  refine ⟨by norm_num [BiCfg.DoubleInv],
    ⟨by norm_num, 20, by norm_num, ?_⟩, ?_⟩
  · have hlog : Nat.log 2 64 = 6 := by decide
    rw [hlog]
    norm_num
  · rintro ⟨g, hlin, hsq⟩
    have hg : g ≤ 4 := by omega
    have hlog : Nat.log 2 64 = 6 := by decide
    rw [hlog] at hsq
    norm_num at hsq
    nlinarith

/-- **The formal statement of Theorem 2 (Double-B); this proposition is NOT
proved here.**

From a physical Double-B configuration `s₀` (`x + y + b = n`) with `X`-majority
initial gap at least `√(γ n lg n)` and with at least half the molecules active,
the Double-B chain reaches all-`X` consensus within `C · γ · n · lg n`
interaction events, except for a failure mass `(n⁻¹)^(c·γ) = exp(-Ω(γ lg n))`.
The constants `C, c` replace the paper's `O(γ n lg n)` and `exp(-Ω(γ lg n))`, and
`n₀` makes "sufficiently large `n`" explicit. -/
def Theorem2_doubleB_statement : Prop :=
  ∃ C n₀ : ℕ, ∃ c : ℝ,
    0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ : ℕ,
        n₀ ≤ n → 1 ≤ γ → 6 * γ * Nat.log 2 n ≤ n →
        ∀ s₀ : BiCfg, s₀.DoubleInv n →
          DoubleBPaperInitial n γ s₀ →
          ∑' z, (if BiXConsensus n z then 0
            else iter doubleBChain (C * γ * n * Nat.log 2 n) s₀ z)
              ≤ (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))

/-! ## Heavy-B clause -/

/-- The exact finite initial-state assumptions of the paper's Heavy-B clause.
The Heavy-B invariant is `x + y + 2b = n` (heavy blanks).  At least half the
population is active (`2b ≤ n`), and the ordinary opinion gap `x-y` has the
required square-root size.  This matches the Double-B clause structurally. -/
def HeavyBPaperInitial (n γ : ℕ) (s : BiCfg) : Prop :=
  4 * s.b ≤ n ∧
    ∃ g : ℕ,
      s.y + g ≤ s.x ∧
        γ * n * Nat.log 2 n ≤ g ^ 2

/-- **The formal statement of Theorem 2 (Heavy-B); this proposition is NOT
proved here.**

From a physical Heavy-B configuration `s₀` (`x + y + 2b = n`) with `X`-majority
initial gap at least `√(γ n lg n)` and with at most half the population as blanks,
the Heavy-B chain reaches all-`X` consensus within `C · γ · n · lg n`
interaction events, except for a failure mass `(n⁻¹)^(c·γ) = exp(-Ω(γ lg n))`.
The constants `C, c` replace the paper's asymptotic notation, and `n₀ ≥ 3` makes
"sufficiently large `n`" explicit. -/
def Theorem2_heavyB_statement : Prop :=
  ∃ C n₀ : ℕ, ∃ c : ℝ,
    0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ : ℕ,
        n₀ ≤ n → 1 ≤ γ → 6 * γ * Nat.log 2 n ≤ n →
        ∀ s₀ : BiCfg, s₀.HeavyInv n →
          HeavyBPaperInitial n γ s₀ →
          ∑' z, (if BiXConsensus n z then 0
            else iter heavyBChain (C * γ * n * Nat.log 2 n) s₀ z)
              ≤ (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))

/-! ## Single-B clause -/

/-- Paper premise for the Single-B clause: identical in content to Double-B's
(`x+y ≥ n/2`, equivalently `2b ≤ n` under `x+y+b = n`, and
gap at least `√(γ n lg n)`). -/
abbrev SingleBPaperInitial (n γ : ℕ) (s : BiCfg) : Prop :=
  DoubleBPaperInitial n γ s

/-- **The formal statement of Theorem 2 (Single-B); this proposition is NOT
proved here.**

From a physical Single-B configuration `s₀` (`x + y + b = n`) with `X`-majority
initial gap at least `√(γ n lg n)` and with at least half the molecules active,
the Single-B chain reaches all-`X` consensus within `C · γ · n · lg n`
interaction events, except for a failure mass `(n⁻¹)^(c·γ) = exp(-Ω(γ lg n))`.
The constants `C, c` replace the paper's asymptotic notation, and `n₀ ≥ 3` makes
"sufficiently large `n`" explicit. -/
def Theorem2_singleB_statement : Prop :=
  ∃ C n₀ : ℕ, ∃ c : ℝ,
    0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ : ℕ,
        n₀ ≤ n → 1 ≤ γ → 6 * γ * Nat.log 2 n ≤ n →
        ∀ s₀ : BiCfg, s₀.DoubleInv n →
          SingleBPaperInitial n γ s₀ →
          ∑' z, (if BiXConsensus n z then 0
            else iter singleBChain (C * γ * n * Nat.log 2 n) s₀ z)
              ≤ (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))

end Tri

#print axioms Tri.doubleBPaperInitial_not_oldExample
#print axioms Tri.Theorem2_singleB_statement

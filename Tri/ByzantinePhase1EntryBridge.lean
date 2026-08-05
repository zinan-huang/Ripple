/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase1RawRung
import Tri.Theorem4Statement

/-!
# Deterministic Phase-I entry bridge

The paper's initial signed gap is itself the first dyadic seed.  This file
packages the initial physical state in the fixed `z = b` fibre and proves its
checkpoint-zero membership before any transition is taken.
-/

namespace Tri.Byzantine

noncomputable section

/-- With the dyadic seed chosen as `d₀ = d`, the paper's square premise is
already in the exact form consumed by the dyadic error bound. -/
theorem theorem4PaperInitial_phase1_seed_square
    (n γ x₀ y₀ b d : ℕ)
    (hinit : Theorem4PaperInitial n γ x₀ y₀ b d) :
    γ * n * Nat.log 2 n ≤ d ^ 2 := by
  exact hinit.2.2.1

/-- The strict printed Byzantine premise is only needed later, at the rung
rate-floor specialization. -/
theorem theorem4PaperInitial_phase1_seed_budget
    (n γ x₀ y₀ b d : ℕ)
    (hinit : Theorem4PaperInitial n γ x₀ y₀ b d) :
    16 * b ≤ d := by
  -- omega cannot see through the conjunction; destructure first.
  obtain ⟨-, -, -, hb⟩ := hinit
  omega

/-- The paper initial state is in dyadic checkpoint zero deterministically.
Here the seed parameter of the ladder is exactly `d₀ = d`. -/
theorem theorem4PaperInitial_phase1DyadicCheckpoint
    (n γ x₀ y₀ b d : ℕ)
    (hinit : Theorem4PaperInitial n γ x₀ y₀ b d) :
    Phase1DyadicCheckpoint (B := b) (z := b) n d 0
      (⟨theorem4InitialState n x₀ y₀ b hinit.1, by rfl⟩ :
        Phase1Level n b b) := by
  apply phase1DyadicCheckpoint_zero_of_gap
  change n + d ≤ 2 * x₀
  exact hinit.2.1.le

end

end Tri.Byzantine

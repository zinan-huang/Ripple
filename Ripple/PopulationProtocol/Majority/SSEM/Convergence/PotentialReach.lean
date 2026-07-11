/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reachability via a Decreasing Potential

A generic reachability tool: if from any non-zero-potential
configuration we can find a single step that strictly decreases the
potential while preserving an invariant `Pinv`, then a deterministic
scheduler reaches a zero-potential configuration in finitely many
steps.

This separates the local "single step" reasoning from the global
existence of a scheduler.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Schedule

namespace SSEM

variable {Q X Y : Type*} {n : ℕ}

/-- **Reach-zero-by-decreasing-potential.**

Given an invariant `Pinv : Config Q X n → Prop` and a potential
`φ : Config Q X n → ℕ`, if from every `Pinv`-configuration with positive
potential we can choose an interaction that preserves `Pinv` and strictly
decreases `φ`, then from every `Pinv`-configuration there is a finite
deterministic schedule whose terminal configuration still satisfies
`Pinv` and has potential `0`.

The lemma assumes `Inhabited (Fin n × Fin n)` (i.e., `n > 0`) so that a
"default" scheduler exists for the zero-potential base case.  When
`n = 0` there are no agents and the existence claim is vacuous from the
protocol perspective. -/
theorem reach_zero_potential
    [Inhabited (Fin n × Fin n)]
    (P : Protocol Q X Y) (Pinv : Config Q X n → Prop) (φ : Config Q X n → ℕ)
    (hStep : ∀ C, Pinv C → 0 < φ C →
              ∃ u v : Fin n,
                Pinv (C.step P u v) ∧ φ (C.step P u v) < φ C) :
    ∀ C, Pinv C → ∃ (γ : DetScheduler n) (t : ℕ),
      Pinv (execution P C γ t) ∧ φ (execution P C γ t) = 0 := by
  intro C₀ hC₀
  -- Strong induction on `φ C₀`.
  suffices h : ∀ k, ∀ C, Pinv C → φ C ≤ k →
      ∃ (γ : DetScheduler n) (t : ℕ),
        Pinv (execution P C γ t) ∧ φ (execution P C γ t) = 0 from
    h (φ C₀) C₀ hC₀ le_rfl
  intro k
  induction k with
  | zero =>
    intro C hC h_le
    have h0 : φ C = 0 := Nat.le_zero.mp h_le
    refine ⟨fun _ => default, 0, hC, h0⟩
  | succ k ih =>
    intro C hC h_le
    by_cases h_zero : φ C = 0
    · refine ⟨fun _ => default, 0, hC, h_zero⟩
    · have h_pos : 0 < φ C := Nat.pos_of_ne_zero h_zero
      obtain ⟨u, v, hC', h_dec⟩ := hStep C hC h_pos
      have h_le' : φ (C.step P u v) ≤ k := by omega
      obtain ⟨γ', t', hC_t', h_zero_t'⟩ := ih (C.step P u v) hC' h_le'
      -- Build the composed scheduler via concatScheduler.
      let γ₁ : DetScheduler n := fun _ => (u, v)
      refine ⟨concatScheduler γ₁ 1 γ', 1 + t', ?_, ?_⟩
      · rw [execution_concat]
        -- execution P C γ₁ 1 = C.step P u v.
        have hone : execution P C γ₁ 1 = C.step P u v := by
          show (execution P C γ₁ 0).step P (γ₁ 0).1 (γ₁ 0).2 = C.step P u v
          rfl
        rw [hone]; exact hC_t'
      · rw [execution_concat]
        have hone : execution P C γ₁ 1 = C.step P u v := by
          show (execution P C γ₁ 0).step P (γ₁ 0).1 (γ₁ 0).2 = C.step P u v
          rfl
        rw [hone]; exact h_zero_t'

/-- **Macro-step variant of `reach_zero_potential`.**

If from every `Pinv`-configuration with positive potential there exists a
finite (possibly multi-step) execution leading to another `Pinv`-config
with strictly smaller potential, then a finite scheduler reaches a
zero-potential `Pinv` configuration.

This generalizes `reach_zero_potential` (which is the `k = 1` special
case): the macro-step can include any finite number of base steps,
admitting protocols that temporarily leave the invariant during reset
cycles (or analogous transient phases) before recovering. -/
theorem reach_zero_potential_macro
    [Inhabited (Fin n × Fin n)]
    (P : Protocol Q X Y) (Pinv : Config Q X n → Prop) (φ : Config Q X n → ℕ)
    (hMacro : ∀ C, Pinv C → 0 < φ C →
              ∃ (γ : DetScheduler n) (k : ℕ),
                Pinv (execution P C γ k) ∧ φ (execution P C γ k) < φ C) :
    ∀ C, Pinv C → ∃ (γ : DetScheduler n) (t : ℕ),
      Pinv (execution P C γ t) ∧ φ (execution P C γ t) = 0 := by
  intro C₀ hC₀
  suffices h : ∀ k, ∀ C, Pinv C → φ C ≤ k →
      ∃ (γ : DetScheduler n) (t : ℕ),
        Pinv (execution P C γ t) ∧ φ (execution P C γ t) = 0 from
    h (φ C₀) C₀ hC₀ le_rfl
  intro k
  induction k with
  | zero =>
    intro C hC h_le
    have h0 : φ C = 0 := Nat.le_zero.mp h_le
    refine ⟨fun _ => default, 0, hC, h0⟩
  | succ k ih =>
    intro C hC h_le
    by_cases h_zero : φ C = 0
    · refine ⟨fun _ => default, 0, hC, h_zero⟩
    · have h_pos : 0 < φ C := Nat.pos_of_ne_zero h_zero
      obtain ⟨γ₁, t₁, hC₁, h_dec⟩ := hMacro C hC h_pos
      have h_le' : φ (execution P C γ₁ t₁) ≤ k := by omega
      obtain ⟨γ', t', hC_t', h_zero_t'⟩ := ih (execution P C γ₁ t₁) hC₁ h_le'
      refine ⟨concatScheduler γ₁ t₁ γ', t₁ + t', ?_, ?_⟩
      · rw [execution_concat]; exact hC_t'
      · rw [execution_concat]; exact h_zero_t'

end SSEM

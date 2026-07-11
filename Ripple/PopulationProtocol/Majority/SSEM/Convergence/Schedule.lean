/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Scheduler Composition

Glueing two schedulers γ₁, γ₂ at a step boundary `k`: the resulting
scheduler runs γ₁ for the first `k` steps, then γ₂ thereafter.  The
corresponding execution lemma `execution_concat` lets us chain
phase-existence results in sequence.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Defs.Execution

namespace SSEM

variable {Q X Y : Type*} {n : ℕ}

/-- If two schedulers agree on the first `k` steps, their `k`-step
executions from the same configuration are identical. -/
theorem execution_eq_of_scheduler_eq (P : Protocol Q X Y) (C : Config Q X n)
    (γ₁ γ₂ : DetScheduler n) (k : ℕ)
    (h : ∀ i, i < k → γ₁ i = γ₂ i) :
    execution P C γ₁ k = execution P C γ₂ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (execution P C γ₁ k).step P (γ₁ k).1 (γ₁ k).2
       = (execution P C γ₂ k).step P (γ₂ k).1 (γ₂ k).2
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
    rw [h k (Nat.lt_succ_self k)]

/-- Concatenate two schedulers at step boundary `k`. -/
def concatScheduler (γ₁ : DetScheduler n) (k : ℕ) (γ₂ : DetScheduler n) :
    DetScheduler n :=
  fun t => if t < k then γ₁ t else γ₂ (t - k)

/-- Running the concatenated scheduler for `k + t` steps from `C` is the same
as running `γ₁` for `k` steps from `C`, then `γ₂` for `t` steps from the
result. -/
theorem execution_concat (P : Protocol Q X Y) (C : Config Q X n)
    (γ₁ γ₂ : DetScheduler n) (k t : ℕ) :
    execution P C (concatScheduler γ₁ k γ₂) (k + t)
      = execution P (execution P C γ₁ k) γ₂ t := by
  -- First: the concat scheduler matches γ₁ on the first k steps.
  have hagree : ∀ i, i < k → concatScheduler γ₁ k γ₂ i = γ₁ i := by
    intro i hi; unfold concatScheduler; simp [hi]
  have hk : execution P C (concatScheduler γ₁ k γ₂) k = execution P C γ₁ k :=
    execution_eq_of_scheduler_eq P C (concatScheduler γ₁ k γ₂) γ₁ k hagree
  -- Now induct on t.
  induction t with
  | zero =>
    show execution P C (concatScheduler γ₁ k γ₂) k = execution P (execution P C γ₁ k) γ₂ 0
    rw [hk]; rfl
  | succ t ih =>
    show execution P C (concatScheduler γ₁ k γ₂) (k + (t + 1))
       = execution P (execution P C γ₁ k) γ₂ (t + 1)
    -- Both unfold one step.
    have hkt : k + (t + 1) = (k + t) + 1 := by omega
    rw [hkt]
    show (execution P C (concatScheduler γ₁ k γ₂) (k + t)).step P
            ((concatScheduler γ₁ k γ₂) (k + t)).1
            ((concatScheduler γ₁ k γ₂) (k + t)).2
       = (execution P (execution P C γ₁ k) γ₂ t).step P (γ₂ t).1 (γ₂ t).2
    rw [ih]
    -- The scheduler at index `k + t` is γ₂ t.
    have hsched : (concatScheduler γ₁ k γ₂) (k + t) = γ₂ t := by
      unfold concatScheduler
      have : ¬ (k + t < k) := by omega
      simp [this]
    rw [hsched]

/-- **Phase composition**: chain two reachability claims.  If from any
configuration we can reach a configuration satisfying `P₁`, and from any
`P₁`-configuration we can reach a `P₂`-configuration, then from any
configuration we can reach a `P₂`-configuration. -/
theorem reachable_compose
    {P : Protocol Q X Y}
    {P₁ P₂ : Config Q X n → Prop}
    (h1 : ∀ C₀, ∃ (γ : DetScheduler n) (t : ℕ),
            P₁ (execution P C₀ γ t))
    (h2 : ∀ C, P₁ C → ∃ (γ : DetScheduler n) (t : ℕ),
            P₂ (execution P C γ t)) :
    ∀ C₀, ∃ (γ : DetScheduler n) (t : ℕ), P₂ (execution P C₀ γ t) := by
  intro C₀
  obtain ⟨γ₁, t₁, hP₁⟩ := h1 C₀
  obtain ⟨γ₂, t₂, hP₂⟩ := h2 _ hP₁
  refine ⟨concatScheduler γ₁ t₁ γ₂, t₁ + t₂, ?_⟩
  rw [execution_concat]
  exact hP₂

end SSEM

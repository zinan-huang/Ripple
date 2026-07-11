/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theorem 1: Impossibility Without Knowledge of n

No protocol can solve the self-stabilizing exact majority problem
without knowledge of n.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Defs.ExactMajority
import Ripple.PopulationProtocol.Majority.SSEM.Embed
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Card

namespace SSEM

variable {Q : Type*} [DecidableEq Q] [Inhabited Q]

private def embed25 : Fin 2 → Fin 5
  | ⟨0, _⟩ => ⟨3, by omega⟩
  | ⟨1, _⟩ => ⟨4, by omega⟩

private theorem embed25_injective : Function.Injective embed25 := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [embed25]

private def liftSched (γ' : DetScheduler 2) : DetScheduler 5 :=
  fun t => (embed25 (γ' t).1, embed25 (γ' t).2)

private def C₀_5 : Config Q Opinion 5 := fun v =>
  if v.val < 3 then (default, .A) else (default, .B)

private theorem safe5_gives_allA
    (P : Protocol Q Opinion Output) (C : Config Q Opinion 5)
    (hInput : ∀ v : Fin 5, C.inputOf v = if v.val < 3 then Opinion.A else Opinion.B)
    (hSafe : ExactMajoritySafe' P C Opinion.A Opinion.B Output.A Output.B Output.T) :
    C.allOutput P .A := by
  unfold ExactMajoritySafe' at hSafe
  have hA : C.agentsWithInput .A = {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} := by
    ext v; simp only [Config.agentsWithInput, Finset.mem_filter, Finset.mem_univ, true_and,
      Config.inputOf, Finset.mem_insert, Finset.mem_singleton]
    have hv := hInput v; simp only [Config.inputOf] at hv
    constructor
    · intro h; rw [hv] at h; split at h
      · fin_cases v <;> simp_all
      · exact absurd h (by decide)
    · intro h; rw [hv]; rcases h with h | h | h <;> subst h <;> simp
  have hB : C.agentsWithInput .B = {⟨3, by omega⟩, ⟨4, by omega⟩} := by
    ext v; simp only [Config.agentsWithInput, Finset.mem_filter, Finset.mem_univ, true_and,
      Config.inputOf, Finset.mem_insert, Finset.mem_singleton]
    have hv := hInput v; simp only [Config.inputOf] at hv
    constructor
    · intro h; rw [hv] at h; split at h
      · exact absurd h (by decide)
      · fin_cases v <;> simp_all
    · intro h; rw [hv]; rcases h with h | h <;> subst h <;> simp
  simp only [hA, hB] at hSafe; norm_num at hSafe; exact hSafe

private theorem safe2_gives_allB
    (P : Protocol Q Opinion Output) (C : Config Q Opinion 2)
    (hInput : ∀ v : Fin 2, C.inputOf v = .B)
    (hSafe : ExactMajoritySafe' P C Opinion.A Opinion.B Output.A Output.B Output.T) :
    C.allOutput P .B := by
  unfold ExactMajoritySafe' at hSafe
  have hA : C.agentsWithInput Opinion.A = ∅ := by
    ext v; constructor
    · intro h
      simp only [Config.agentsWithInput, Finset.mem_filter, Finset.mem_univ, true_and,
        Config.inputOf] at h
      have hv := hInput v; simp only [Config.inputOf] at hv
      rw [hv] at h; exact absurd h (by decide)
    · intro h; exact absurd h (by simp)
  have hB : C.agentsWithInput Opinion.B = Finset.univ := by
    ext v; simp only [Config.agentsWithInput, Finset.mem_filter, Finset.mem_univ, true_and,
      Config.inputOf, iff_true]
    have hv := hInput v; simp only [Config.inputOf] at hv
    exact hv
  simp only [hA, hB, Finset.card_empty, Finset.card_univ, Fintype.card_fin] at hSafe
  norm_num at hSafe; exact hSafe

theorem impossibility_without_n (P : Protocol Q Opinion Output) :
    ¬ (∀ n, n ≥ 2 → SolvesSSEM P n) := by
  intro hAll
  -- Step 1: On 5 agents (3A, 2B), reach output-stable config, all output A
  obtain ⟨γ₅, t₅, hOS₅, hSafe₅⟩ := hAll 5 (by omega) (C₀_5 (Q := Q))
  set Ct := execution P C₀_5 γ₅ t₅
  have hCtInput : ∀ v : Fin 5,
      Ct.inputOf v = if v.val < 3 then Opinion.A else Opinion.B := by
    intro v; simp only [Config.inputOf]; rw [execution_input_preserved]
    simp only [C₀_5]; split <;> rfl
  have hAllA := safe5_gives_allA P Ct hCtInput hSafe₅
  -- Step 2: Restrict to {3,4} → 2-agent config, both input B
  set C₀' : Config Q Opinion 2 := fun v => Ct (embed25 v)
  have hC₀'B : ∀ v : Fin 2, C₀'.inputOf v = .B := by
    intro v; simp only [Config.inputOf, C₀']
    have := hCtInput (embed25 v)
    simp only [Config.inputOf] at this
    fin_cases v <;> simp_all [embed25]
  -- Apply SolvesSSEM P 2
  obtain ⟨γ₂, t₂, _, hSafe₂⟩ := hAll 2 (by omega) C₀'
  set Ct' := execution P C₀' γ₂ t₂
  have hCt'B : ∀ v : Fin 2, Ct'.inputOf v = .B := by
    intro v; simp only [Config.inputOf, Ct']; rw [execution_input_preserved]; exact hC₀'B v
  have hAllB := safe2_gives_allB P Ct' hCt'B hSafe₂
  -- Step 3: Contradiction
  have hMatch := execution_embed P embed25 embed25_injective C₀' Ct
    (fun i => rfl) γ₂ (liftSched γ₂) (fun t => rfl)
  have hOutEq : Ct'.outputOf P ⟨0, by omega⟩ =
      (execution P Ct (liftSched γ₂) t₂).outputOf P (embed25 ⟨0, by omega⟩) := by
    simp only [Config.outputOf, Ct']; rw [hMatch]
  have hStable := hOS₅ (liftSched γ₂) t₂ (embed25 ⟨0, by omega⟩)
  have : Output.B = Output.A :=
    calc Output.B
        = Ct'.outputOf P ⟨0, by omega⟩ := (hAllB ⟨0, by omega⟩).symm
      _ = (execution P Ct (liftSched γ₂) t₂).outputOf P (embed25 ⟨0, by omega⟩) := hOutEq
      _ = Ct.outputOf P (embed25 ⟨0, by omega⟩) := hStable.symm
      _ = Output.A := hAllA _
  exact absurd this (by decide)

end SSEM

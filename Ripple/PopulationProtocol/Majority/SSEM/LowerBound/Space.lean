/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Space Lower Bound

Lemma 4: In a silent, safe configuration with |V_a| ≤ |V_b|,
A-agents must have pairwise distinct states.

Key idea: if two A-agents share state s_A, then δ((s_A,A),(s_A,A)) = (s_A,s_A)
by silence. A population of n agents all in (s_A, A) is stuck outputting
π_out(s_A, A). SolvesSSEM forces this output to be A (majority = A),
but in the original config the safe output is B or T. Contradiction.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Defs.ExactMajority
import Ripple.PopulationProtocol.Majority.SSEM.Embed
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace SSEM

variable {Q : Type*} [DecidableEq Q] [DecidableEq Opinion] [Fintype Q]

/-! ## Silent config ⟹ execution stays put -/

private theorem execution_of_silent {n : ℕ}
    (P : Protocol Q Opinion Output) (C : Config Q Opinion n)
    (hSilent : C.isSilent P) (γ : DetScheduler n) (t : ℕ) :
    execution P C γ t = C := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [execution, ih]; exact hSilent _ _

/-! ## Lemma 4 -/

theorem silent_config_A_agents_distinct
    {n : ℕ} (P : Protocol Q Opinion Output)
    (C : Config Q Opinion n)
    (hSilent : C.isSilent P)
    (hSafe : ExactMajoritySafe' P C Opinion.A Opinion.B Output.A Output.B Output.T)
    (hSolves : SolvesSSEM P n)
    (hVa : (C.agentsWithInput .A).card ≤ (C.agentsWithInput .B).card)
    (hn : n ≥ 2)
    (u v : Fin n)
    (huA : C.inputOf u = .A)
    (hvA : C.inputOf v = .A)
    (hne : u ≠ v) :
    C.stateOf u ≠ C.stateOf v := by
  intro hEq
  -- Extract: C u = C v = (s_A, .A) where s_A = C.stateOf u
  set s_A := C.stateOf u with s_A_def
  have hCu : C u = (s_A, Opinion.A) := Prod.ext rfl huA
  have hCv : C v = (s_A, Opinion.A) := Prod.ext hEq.symm hvA
  -- From silence: δ((s_A, A), (s_A, A)) = (s_A, s_A)
  have hS := hSilent u v
  have hSu := congr_fun hS u
  have hSv := congr_fun hS v
  unfold Config.step at hSu hSv
  simp only [if_neg hne] at hSu hSv
  simp only [ite_true] at hSu
  simp only [show (v = u) = False from propext ⟨fun h => hne (h.symm), False.elim⟩,
    ite_false, ite_true] at hSv
  have hDelta1 : (P.δ (C u, C v)).1 = s_A := congr_arg Prod.fst hSu
  have hDelta2 : (P.δ (C u, C v)).2 = s_A := by
    have := congr_arg Prod.fst hSv; simp only [Prod.fst] at this
    rw [this]; exact hEq.symm
  rw [hCu, hCv] at hDelta1 hDelta2
  have hDelta : P.δ ((s_A, Opinion.A), (s_A, Opinion.A)) = (s_A, s_A) :=
    Prod.ext hDelta1 hDelta2
  -- Construct all-(s_A, A) config
  set C' : Config Q Opinion n := fun _ => (s_A, Opinion.A) with C'_def
  -- C' is silent
  have hSilent' : C'.isSilent P := by
    intro u' v'; funext w; unfold Config.step
    by_cases huv' : u' = v'
    · simp [huv']
    · simp only [if_neg huv', C'_def, hDelta]
      split_ifs <;> rfl
  -- Apply SolvesSSEM to C'
  obtain ⟨γ', t', _, hSafe'⟩ := hSolves C'
  -- execution stays at C'
  have hExec : execution P C' γ' t' = C' := execution_of_silent P C' hSilent' γ' t'
  -- All agents in C' have input A, so majority is A
  have hC'A : (execution P C' γ' t').agentsWithInput Opinion.A = Finset.univ := by
    rw [hExec]; ext w
    simp [Config.agentsWithInput, Config.inputOf, C'_def]
  have hC'B : (execution P C' γ' t').agentsWithInput Opinion.B = ∅ := by
    rw [hExec]; ext w; constructor
    · intro h; simp [Config.agentsWithInput, Config.inputOf, C'_def] at h
    · intro h; exact absurd h (by simp)
  -- Safe means allOutput A
  unfold ExactMajoritySafe' at hSafe'
  simp only [hC'A, hC'B, Finset.card_univ, Finset.card_empty] at hSafe'
  have hCardPos : Fintype.card (Fin n) > 0 := by
    rw [Fintype.card_fin]; omega
  simp only [hCardPos, ↓reduceIte] at hSafe'
  -- hSafe' : allOutput P ... .A
  -- In particular, at any agent w: P.π_out (s_A, .A) = .A
  rw [hExec] at hSafe'
  have hPiA : P.π_out (s_A, Opinion.A) = Output.A := by
    have := hSafe' ⟨0, by omega⟩
    simp [Config.outputOf, Config.allOutput, C'_def] at this
    exact this
  -- But in original config C, agent u outputs P.π_out(s_A, A) = A
  have hOutU : C.outputOf P u = Output.A := by
    simp [Config.outputOf, hCu, hPiA]
  -- From hSafe on C with hVa: safe output is B or T, not A
  unfold ExactMajoritySafe' at hSafe
  have hNotA : C.outputOf P u ≠ Output.A := by
    by_cases hLt : (C.agentsWithInput Opinion.A).card < (C.agentsWithInput Opinion.B).card
    · simp only [show ¬((C.agentsWithInput .A).card > (C.agentsWithInput .B).card) from by omega,
        ↓reduceIte, hLt] at hSafe
      have := hSafe u; rw [this]; decide
    · have hEqCard : (C.agentsWithInput .A).card = (C.agentsWithInput .B).card := by omega
      simp only [show ¬((C.agentsWithInput .A).card > (C.agentsWithInput .B).card) from by omega,
        ↓reduceIte, show ¬((C.agentsWithInput .A).card < (C.agentsWithInput .B).card) from hLt]
        at hSafe
      have := hSafe u; rw [this]; decide
  exact hNotA hOutU

/-! ## Lemma 4 (B-agents symmetric version) -/

theorem silent_config_B_agents_distinct
    {n : ℕ} (P : Protocol Q Opinion Output)
    (C : Config Q Opinion n)
    (hSilent : C.isSilent P)
    (hSafe : ExactMajoritySafe' P C Opinion.A Opinion.B Output.A Output.B Output.T)
    (hSolves : SolvesSSEM P n)
    (hVb : (C.agentsWithInput .B).card ≤ (C.agentsWithInput .A).card)
    (hn : n ≥ 2)
    (u v : Fin n)
    (huB : C.inputOf u = .B)
    (hvB : C.inputOf v = .B)
    (hne : u ≠ v) :
    C.stateOf u ≠ C.stateOf v := by
  intro hEq
  set s_B := C.stateOf u with s_B_def
  have hCu : C u = (s_B, Opinion.B) := Prod.ext rfl huB
  have hCv : C v = (s_B, Opinion.B) := Prod.ext hEq.symm hvB
  have hS := hSilent u v
  have hSu := congr_fun hS u
  have hSv := congr_fun hS v
  unfold Config.step at hSu hSv
  simp only [if_neg hne] at hSu hSv
  simp only [ite_true] at hSu
  simp only [show (v = u) = False from propext ⟨fun h => hne (h.symm), False.elim⟩,
    ite_false, ite_true] at hSv
  have hDelta1 : (P.δ (C u, C v)).1 = s_B := congr_arg Prod.fst hSu
  have hDelta2 : (P.δ (C u, C v)).2 = s_B := by
    have := congr_arg Prod.fst hSv; simp only [Prod.fst] at this
    rw [this]; exact hEq.symm
  rw [hCu, hCv] at hDelta1 hDelta2
  have hDelta : P.δ ((s_B, Opinion.B), (s_B, Opinion.B)) = (s_B, s_B) :=
    Prod.ext hDelta1 hDelta2
  set C' : Config Q Opinion n := fun _ => (s_B, Opinion.B) with C'_def
  have hSilent' : C'.isSilent P := by
    intro u' v'; funext w; unfold Config.step
    by_cases huv' : u' = v'
    · simp [huv']
    · simp only [if_neg huv', C'_def, hDelta]
      split_ifs <;> rfl
  obtain ⟨γ', t', _, hSafe'⟩ := hSolves C'
  have hExec : execution P C' γ' t' = C' := execution_of_silent P C' hSilent' γ' t'
  have hC'B : (execution P C' γ' t').agentsWithInput Opinion.B = Finset.univ := by
    rw [hExec]; ext w
    simp [Config.agentsWithInput, Config.inputOf, C'_def]
  have hC'A : (execution P C' γ' t').agentsWithInput Opinion.A = ∅ := by
    rw [hExec]; ext w; constructor
    · intro h; simp [Config.agentsWithInput, Config.inputOf, C'_def] at h
    · intro h; exact absurd h (by simp)
  unfold ExactMajoritySafe' at hSafe'
  simp only [hC'A, hC'B, Finset.card_univ, Finset.card_empty] at hSafe'
  have hNotGt : ¬ ((0 : ℕ) > Fintype.card (Fin n)) := by
    rw [Fintype.card_fin]; omega
  have hLt : (0 : ℕ) < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]; omega
  simp only [hNotGt, hLt, ↓reduceIte] at hSafe'
  rw [hExec] at hSafe'
  have hPiB : P.π_out (s_B, Opinion.B) = Output.B := by
    have := hSafe' ⟨0, by omega⟩
    simp [Config.outputOf, C'_def] at this
    exact this
  have hOutB : C.outputOf P u = Output.B := by
    simp [Config.outputOf, hCu, hPiB]
  unfold ExactMajoritySafe' at hSafe
  have hNotB : C.outputOf P u ≠ Output.B := by
    by_cases hGt : (C.agentsWithInput Opinion.A).card > (C.agentsWithInput Opinion.B).card
    · simp only [hGt, ↓reduceIte] at hSafe
      have := hSafe u; rw [this]; decide
    · simp only [show ¬((C.agentsWithInput .A).card > (C.agentsWithInput .B).card) from hGt,
        ↓reduceIte,
        show ¬((C.agentsWithInput .A).card < (C.agentsWithInput .B).card) from by omega]
        at hSafe
      have := hSafe u; rw [this]; decide
  exact hNotB hOutB

/-! ## Lemma 5: A-agent and B-agent cannot share a state (input-oblivious) -/

theorem silent_config_AB_distinct
    {n : ℕ} (P : Protocol Q Opinion Output)
    (C : Config Q Opinion n)
    (hSilent : C.isSilent P)
    (hSafe : ExactMajoritySafe' P C Opinion.A Opinion.B Output.A Output.B Output.T)
    (hSolves : SolvesSSEM P n)
    (hIO : ∀ (q₁ q₂ : Q) (x₁ x₂ y₁ y₂ : Opinion),
      P.δ ((q₁, x₁), (q₂, y₁)) = P.δ ((q₁, x₂), (q₂, y₂)))
    (hBal : (C.agentsWithInput .A).card = (C.agentsWithInput .B).card)
    (hn : n ≥ 2)
    (u v : Fin n)
    (huA : C.inputOf u = .A)
    (hvB : C.inputOf v = .B)
    (hne : u ≠ v) :
    C.stateOf u ≠ C.stateOf v := by
  intro hEq
  set s := C.stateOf u with s_def
  have hCu : C u = (s, Opinion.A) := Prod.ext rfl huA
  have hCv : C v = (s, Opinion.B) := Prod.ext hEq.symm hvB
  have hS := hSilent u v
  have hSu := congr_fun hS u
  have hSv := congr_fun hS v
  unfold Config.step at hSu hSv
  simp only [if_neg hne] at hSu hSv
  simp only [ite_true] at hSu
  simp only [show (v = u) = False from propext ⟨fun h => hne (h.symm), False.elim⟩,
    ite_false, ite_true] at hSv
  have hD1 : (P.δ (C u, C v)).1 = s := congr_arg Prod.fst hSu
  have hD2 : (P.δ (C u, C v)).2 = s := by
    have := congr_arg Prod.fst hSv; simp only [Prod.fst] at this
    rw [this]; exact hEq.symm
  rw [hCu, hCv] at hD1 hD2
  have hDelta_AB : P.δ ((s, Opinion.A), (s, Opinion.B)) = (s, s) :=
    Prod.ext hD1 hD2
  have hDelta_AA : P.δ ((s, Opinion.A), (s, Opinion.A)) = (s, s) := by
    rw [hIO s s Opinion.A Opinion.A Opinion.A Opinion.B]; exact hDelta_AB
  set C' : Config Q Opinion n := fun _ => (s, Opinion.A) with C'_def
  have hSilent' : C'.isSilent P := by
    intro u' v'; funext w; unfold Config.step
    by_cases huv' : u' = v'
    · simp [huv']
    · simp only [if_neg huv', C'_def, hDelta_AA]
      split_ifs <;> rfl
  obtain ⟨γ', t', _, hSafe'⟩ := hSolves C'
  have hExec : execution P C' γ' t' = C' := execution_of_silent P C' hSilent' γ' t'
  have hC'A : (execution P C' γ' t').agentsWithInput Opinion.A = Finset.univ := by
    rw [hExec]; ext w
    simp [Config.agentsWithInput, Config.inputOf, C'_def]
  have hC'B : (execution P C' γ' t').agentsWithInput Opinion.B = ∅ := by
    rw [hExec]; ext w; constructor
    · intro h; simp [Config.agentsWithInput, Config.inputOf, C'_def] at h
    · intro h; exact absurd h (by simp)
  unfold ExactMajoritySafe' at hSafe'
  simp only [hC'A, hC'B, Finset.card_univ, Finset.card_empty] at hSafe'
  have hCardPos : Fintype.card (Fin n) > 0 := by
    rw [Fintype.card_fin]; omega
  simp only [hCardPos, ↓reduceIte] at hSafe'
  rw [hExec] at hSafe'
  have hPiA : P.π_out (s, Opinion.A) = Output.A := by
    have := hSafe' ⟨0, by omega⟩
    simp [Config.outputOf, C'_def] at this
    exact this
  have hOutA : C.outputOf P u = Output.A := by
    simp [Config.outputOf, hCu, hPiA]
  unfold ExactMajoritySafe' at hSafe
  simp only [show ¬((C.agentsWithInput .A).card > (C.agentsWithInput .B).card) from by omega,
    ↓reduceIte,
    show ¬((C.agentsWithInput .A).card < (C.agentsWithInput .B).card) from by omega] at hSafe
  exact absurd (hSafe u ▸ hOutA) (by decide)

/-! ## Theorem 2: Space lower bound -/

/-- A silent, input-oblivious SSEM protocol on a balanced config
    requires at least n states. -/
theorem space_lower_bound
    {n : ℕ} (P : Protocol Q Opinion Output)
    (C : Config Q Opinion n)
    (hn : n ≥ 2)
    (hSilent : C.isSilent P)
    (hSafe : ExactMajoritySafe' P C Opinion.A Opinion.B Output.A Output.B Output.T)
    (hSolves : SolvesSSEM P n)
    (hIO : ∀ (q₁ q₂ : Q) (x₁ x₂ y₁ y₂ : Opinion),
      P.δ ((q₁, x₁), (q₂, y₁)) = P.δ ((q₁, x₂), (q₂, y₂)))
    (hBal : (C.agentsWithInput .A).card = (C.agentsWithInput .B).card) :
    Fintype.card Q ≥ n := by
  suffices hInj : Function.Injective C.stateOf by
    calc (n : ℕ) = Fintype.card (Fin n) := (Fintype.card_fin n).symm
      _ ≤ Fintype.card Q := Fintype.card_le_of_injective C.stateOf hInj
  intro u v hEq
  by_contra hne
  have opinionExh : ∀ (x : Opinion), x = .A ∨ x = .B := by
    intro x; cases x <;> simp
  obtain huA | huB := opinionExh (C.inputOf u)
  · obtain hvA | hvB := opinionExh (C.inputOf v)
    · exact (silent_config_A_agents_distinct P C hSilent hSafe hSolves
        (by omega) (by omega) u v huA hvA hne) hEq
    · exact (silent_config_AB_distinct P C hSilent hSafe hSolves hIO hBal
        (by omega) u v huA hvB hne) hEq
  · obtain hvA | hvB := opinionExh (C.inputOf v)
    · exact (silent_config_AB_distinct P C hSilent hSafe hSolves hIO hBal
        (by omega) v u hvA huB (Ne.symm hne)) hEq.symm
    · exact (silent_config_B_agents_distinct P C hSilent hSafe hSolves
        (by omega) (by omega) u v huB hvB hne) hEq

end SSEM

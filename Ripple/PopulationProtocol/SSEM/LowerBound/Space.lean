/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Space lower bound (Kanaya et al. 2025, Lemma 5 and Theorem 2)

Source: arXiv:2503.17652v1, §5.1 (`ref/Kanaya-2025-SSEM-2503.17652v1.pdf`).

Lemma 5: in a silent configuration of a silent SSEM protocol with `|V_a| ≤ |V_b|`, the
`A`-input agents have pairwise distinct states (`silent_config_A_agents_distinct`; the
symmetric `B` version is `silent_config_B_agents_distinct`).

Key idea: if two A-agents share state s_A, then δ((s_A,A),(s_A,A)) = (s_A,s_A)
by silence. A population of n agents all in (s_A, A) is stuck outputting
π_out(s_A, A). SolvesSSEM forces this output to be A (majority = A),
but in the original config the safe output is B or T. Contradiction.

Theorem 2 (`space_lower_bound`): a silent SSEM protocol on an even number `n ≥ 2` of agents
has at least `n` states. No assumption on the transition function.
-/

import Ripple.PopulationProtocol.SSEM.Defs.ExactMajority
import Ripple.PopulationProtocol.SSEM.Defs.Silent
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Ripple.PopulationProtocol.SSEM

variable {Q : Type*} [DecidableEq Q] [Fintype Q]

/-! ## Silent config ⟹ execution stays put -/

private theorem execution_of_silent {n : ℕ}
    (P : Protocol Q Opinion Output) (C : Config Q Opinion n)
    (hSilent : C.isSilent P) (γ : DetScheduler n) (t : ℕ) :
    execution P C γ t = C := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [execution, ih]; exact hSilent _ _

/-! ## Lemma 5 -/

theorem silent_config_A_agents_distinct
    {n : ℕ} (P : Protocol Q Opinion Output)
    (C : Config Q Opinion n)
    (hSilent : C.isSilent P)
    (hSafe : ExactMajoritySafe P C Opinion.A Opinion.B Output.A Output.B Output.T)
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
  unfold ExactMajoritySafe at hSafe'
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
  unfold ExactMajoritySafe at hSafe
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

/-! ## Lemma 5 (B-agents symmetric version) -/

theorem silent_config_B_agents_distinct
    {n : ℕ} (P : Protocol Q Opinion Output)
    (C : Config Q Opinion n)
    (hSilent : C.isSilent P)
    (hSafe : ExactMajoritySafe P C Opinion.A Opinion.B Output.A Output.B Output.T)
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
  unfold ExactMajoritySafe at hSafe'
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
  unfold ExactMajoritySafe at hSafe
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

/-! ## Theorem 2: space lower bound -/

/-- In a silent configuration of a silent SSEM protocol with `|V_a| ≤ |V_b|`, the states of the
`A`-input agents form a set of `|V_a|` states, each of which outputs the configuration's majority
answer when paired with input `A`. -/
private theorem inputA_states_card_and_output
    {n : ℕ} {P : Protocol Q Opinion Output}
    (hSolves : SolvesSSEM P n) (hn : n ≥ 2) (C : Config Q Opinion n)
    (hSilent : C.isSilent P)
    (hSafe : ExactMajoritySafe P C Opinion.A Opinion.B Output.A Output.B Output.T)
    (hVa : (C.agentsWithInput .A).card ≤ (C.agentsWithInput .B).card) :
    ((C.agentsWithInput .A).image C.stateOf).card = (C.agentsWithInput .A).card ∧
    ∀ q ∈ (C.agentsWithInput .A).image C.stateOf,
      P.π_out (q, Opinion.A) =
        majorityOpinion (C.agentsWithInput .A).card (C.agentsWithInput .B).card := by
  constructor
  · apply Finset.card_image_of_injOn
    intro u hu v hv hEq
    by_contra hne
    simp only [Finset.mem_coe, Config.agentsWithInput, Finset.mem_filter, Finset.mem_univ,
      true_and] at hu hv
    exact silent_config_A_agents_distinct P C hSilent hSafe hSolves hVa hn u v hu hv hne hEq
  · intro q hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    have huA : C.inputOf u = .A := by
      simpa [Config.agentsWithInput] using hu
    have hCu : C u = (C.stateOf u, Opinion.A) := Prod.ext rfl huA
    have hout : C.outputOf P u =
        majorityOpinion (C.agentsWithInput .A).card (C.agentsWithInput .B).card := by
      simp only [ExactMajoritySafe] at hSafe
      unfold majorityOpinion
      split_ifs at hSafe ⊢ <;> exact hSafe u
    rw [← hout, Config.outputOf, hCu]

/-- **Theorem 2 of Kanaya et al. (2025).** A silent self-stabilizing exact-majority protocol on
an even number `n ≥ 2` of agents has at least `n` states.

Proof (the paper's): with `|V_a| = n/2 - 1`, Lemma 5 (`silent_config_A_agents_distinct`) gives
`n/2 - 1` distinct states that output `B` on input `A`; with `|V_a| = n/2` it gives `n/2` distinct
states that output `T` on input `A`; with `|V_a| = n` some state outputs `A` on input `A`. The
three sets are disjoint since their outputs on input `A` differ.

The paper states the theorem for even `n ≥ 4`; the proof works for every even `n ≥ 2`. Silence
and self-stabilization are the reachability forms `SilentProtocol` and `SolvesSSEM`, which the
paper's probability-one definitions imply (`silentProtocol_of_almostSure`,
`solvesSSEM_of_kanayaDefinition1`). -/
theorem space_lower_bound [Nonempty Q]
    {n : ℕ} (P : Protocol Q Opinion Output)
    (hn : 2 ≤ n) (heven : Even n)
    (hSolves : SolvesSSEM P n) (hSilent : SilentProtocol P n) :
    n ≤ Fintype.card Q := by
  classical
  obtain ⟨m, rfl⟩ := heven
  have hm : 1 ≤ m := by omega
  -- populations with `m - 1`, `m`, and `2m` agents of input `A`
  obtain ⟨C₁, hS₁, hSafe₁, hA₁, hB₁⟩ :=
    exists_silent_config_with_inputA_card hSolves hSilent (m - 1) (by omega)
  obtain ⟨C₂, hS₂, hSafe₂, hA₂, hB₂⟩ :=
    exists_silent_config_with_inputA_card hSolves hSilent m (by omega)
  obtain ⟨C₃, _hS₃, hSafe₃, hA₃, hB₃⟩ :=
    exists_silent_config_with_inputA_card hSolves hSilent (m + m) le_rfl
  obtain ⟨hcard₁, hout₁⟩ := inputA_states_card_and_output hSolves hn C₁ hS₁ hSafe₁
    (by rw [hA₁, hB₁]; omega)
  obtain ⟨hcard₂, hout₂⟩ := inputA_states_card_and_output hSolves hn C₂ hS₂ hSafe₂
    (by rw [hA₂, hB₂]; omega)
  set S₁ := (C₁.agentsWithInput .A).image C₁.stateOf
  set S₂ := (C₂.agentsWithInput .A).image C₂.stateOf
  have hmaj₁ : majorityOpinion (m - 1) (m + m - (m - 1)) = Output.B := by
    unfold majorityOpinion
    split_ifs <;> first | rfl | (exfalso; omega)
  have hmaj₂ : majorityOpinion m (m + m - m) = Output.T := by
    unfold majorityOpinion
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [hA₁, hB₁, hmaj₁] at hout₁
  rw [hA₂, hB₂, hmaj₂] at hout₂
  -- one state that outputs `A` on input `A`
  let v₀ : Fin (m + m) := ⟨0, by omega⟩
  have hv₀ : C₃.inputOf v₀ = .A := by
    have hmem : v₀ ∈ C₃.agentsWithInput .A := by
      have huniv : C₃.agentsWithInput .A = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [hA₃, Fintype.card_fin])
      rw [huniv]
      exact Finset.mem_univ _
    simpa [Config.agentsWithInput] using hmem
  have hq₃ : P.π_out (C₃.stateOf v₀, Opinion.A) = Output.A := by
    simp only [ExactMajoritySafe, hA₃, hB₃] at hSafe₃
    have hgt : m + m > m + m - (m + m) := by omega
    rw [if_pos hgt] at hSafe₃
    have h := hSafe₃ v₀
    rwa [Config.outputOf, show C₃ v₀ = (C₃.stateOf v₀, Opinion.A) from Prod.ext rfl hv₀] at h
  have hdisj₁₂ : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro q h₁ h₂
    have := (hout₁ q h₁).symm.trans (hout₂ q h₂)
    exact absurd this (by decide)
  have hnot₃ : C₃.stateOf v₀ ∉ S₁ ∪ S₂ := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact absurd ((hout₁ _ h).symm.trans hq₃) (by decide)
    · exact absurd ((hout₂ _ h).symm.trans hq₃) (by decide)
  have hcard : (insert (C₃.stateOf v₀) (S₁ ∪ S₂)).card = m + m := by
    rw [Finset.card_insert_of_notMem hnot₃, Finset.card_union_of_disjoint hdisj₁₂,
      hcard₁, hcard₂, hA₁, hA₂]
    omega
  rw [← hcard]
  exact Finset.card_le_univ _

end Ripple.PopulationProtocol.SSEM

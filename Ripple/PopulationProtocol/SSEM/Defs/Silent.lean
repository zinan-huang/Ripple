/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Silent protocols and silent self-stabilizing exact majority

Kanaya, Eguchi, Sasada, Ooshita, Inoue, *Time- and Space-Optimal Silent Self-Stabilizing
Exact Majority in Population Protocols*, arXiv:2503.17652v1 (`ref/Kanaya-2025-SSEM-2503.17652v1.pdf`),
§2.1–2.2:

* a configuration is *safe* if no execution from it changes any output
  (`Config.isOutputStable`), and *silent* if no execution from it changes any state
  (`Config.isSilent`: every interaction is the identity);
* a protocol is *silent* if an execution reaches a silent configuration with probability 1
  under the uniform random scheduler;
* Definition 1: a self-stabilizing exact majority protocol is one where, from every initial
  configuration, every safe configuration reachable from it outputs the exact majority, and an
  execution reaches a safe configuration with probability 1.

**Scheduler model.** The paper's interactions are ordered pairs of distinct agents. A
`DetScheduler` may also pick a self-pair `(u, u)`, but `Config.step P u u = C`, so such a step is a
skipped step: it changes neither the set of reachable configurations nor silence. The random
scheduler `Probability.uniformPair` is supported on distinct pairs only.

**Reachability form.** The predicates below are the reachability forms of the paper's
probability-one conditions: `SilentProtocol P n` says that from every configuration some schedule
reaches a silent configuration, and `SolvesSSEM P n` (in `Defs/Execution.lean`) says that from
every configuration some schedule reaches a safe configuration with the majority output. Both are
*implied* by the paper's definitions (`silentProtocol_of_almostSure`,
`solvesSSEM_of_kanayaDefinition1` below), so a lower bound proved from them applies to every
protocol that is silent and self-stabilizing in the paper's sense. For a finite state set the
converse also holds (finite Markov chain with every configuration admissible as initial), but that
direction is not formalized here.
-/

import Ripple.PopulationProtocol.SSEM.Probability.ExpectedTime
import Ripple.PopulationProtocol.SSEM.Convergence.Schedule
import Ripple.PopulationProtocol.SSEM.Embed

namespace Ripple.PopulationProtocol.SSEM

variable {Q X Y : Type*} {n : ℕ}

/-- A silent configuration stays fixed along every execution. -/
theorem execution_of_isSilent [DecidableEq Q] [DecidableEq X]
    {P : Protocol Q X Y} {C : Config Q X n} (hSilent : C.isSilent P)
    (γ : DetScheduler n) (t : ℕ) :
    execution P C γ t = C := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [execution, ih]
      exact hSilent _ _

/-- A silent configuration is output-stable (safe).

Kanaya §2 distinguishes the two predicates: safe/output-stable means outputs never change,
while silent means states never change. -/
theorem Config.isSilent.isOutputStable [DecidableEq Q] [DecidableEq X]
    {P : Protocol Q X Y} {C : Config Q X n} (hSilent : C.isSilent P) :
    C.isOutputStable P := by
  intro γ t w
  rw [execution_of_isSilent hSilent γ t]

/-- **Silent protocol** (Kanaya §2.1, reachability form): from every configuration on `n`
agents, some schedule reaches a silent configuration. The paper's probability-one definition
implies it (`silentProtocol_of_almostSure`). -/
def SilentProtocol [DecidableEq Q] (P : Protocol Q Opinion Output) (n : ℕ) : Prop :=
  ∀ C₀ : Config Q Opinion n,
    ∃ (γ : DetScheduler n) (t : ℕ), (execution P C₀ γ t).isSilent P

/-- **Silent self-stabilizing exact majority** on `n` agents, the problem of Kanaya et al.:
self-stabilizing exact majority (`SolvesSSEM`, Definition 1) by a silent protocol. -/
def SolvesSilentSSEM [DecidableEq Q] (P : Protocol Q Opinion Output) (n : ℕ) : Prop :=
  SolvesSSEM P n ∧ SilentProtocol P n

/-- **Kanaya Definition 1, literally** (with `X = {A, B}`, `Y = {A, B, T}`): from every initial
configuration, (1) every safe configuration reachable from it outputs the exact majority, and
(2) an execution under the uniform random scheduler reaches a safe configuration with
probability 1. -/
def KanayaDefinition1 [DecidableEq Q] (P : Protocol Q Opinion Output) (n : ℕ)
    (hn : 2 ≤ n) : Prop :=
  ∀ C₀ : Config Q Opinion n,
    (∀ (γ : DetScheduler n) (t : ℕ),
      (execution P C₀ γ t).isOutputStable P →
        ExactMajoritySafe P (execution P C₀ γ t)
          Opinion.A Opinion.B Output.A Output.B Output.T) ∧
    Probability.reachesGoalAlmostSurely P hn C₀ (fun C => C.isOutputStable P)

/-- If the uniform random scheduler reaches `Goal` with probability 1 from `C₀`, then some
deterministic schedule reaches `Goal` from `C₀`. -/
theorem exists_execution_of_reachesGoalAlmostSurely
    (P : Protocol Q X Y) (hn : 2 ≤ n) (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (h : Probability.reachesGoalAlmostSurely P hn C₀ Goal) :
    ∃ (γ : DetScheduler n) (t : ℕ), Goal (execution P C₀ γ t) := by
  classical
  by_contra hno
  have hno' : ∀ (γ : DetScheduler n) (t : ℕ), ¬ Goal (execution P C₀ γ t) := by
    intro γ t hG
    exact hno ⟨γ, t, hG⟩
  let Reach : Config Q X n → Prop :=
    fun C => ∃ (γ : DetScheduler n) (s : ℕ), execution P C₀ γ s = C
  have hReach₀ : Reach C₀ :=
    ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩), 0, rfl⟩
  have hReachStep : ∀ C : Config Q X n, Reach C → ∀ i j : Fin n, Reach (C.step P i j) := by
    rintro C ⟨γ, s, rfl⟩ i j
    refine ⟨concatScheduler γ s (fun _ => (i, j)), s + 1, ?_⟩
    rw [execution_concat]
    rfl
  have hzero : ∀ t : ℕ, Probability.probHitBy P hn C₀ Goal t = 0 := by
    intro t
    have heq := Probability.probHitBy_eq_and_inv_of_invariant P hn C₀ Goal Reach
      hReach₀ hReachStep t
    change Probability.probHitBy P hn C₀ (fun C => Goal C ∧ Reach C) t =
      Probability.probHitBy P hn C₀ Goal t at heq
    rw [← heq]
    exact Probability.probHitBy_eq_zero_of_forall_not P hn C₀ _
      (by
        rintro C ⟨hG, γ, s, rfl⟩
        exact hno' γ s hG) t
  unfold Probability.reachesGoalAlmostSurely at h
  simp [hzero] at h

/-- The paper's probability-one silence implies the reachability form `SilentProtocol`. -/
theorem silentProtocol_of_almostSure [DecidableEq Q]
    {P : Protocol Q Opinion Output} {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ C₀ : Config Q Opinion n,
      Probability.reachesGoalAlmostSurely P hn C₀ (fun C => C.isSilent P)) :
    SilentProtocol P n :=
  fun C₀ => exists_execution_of_reachesGoalAlmostSurely P hn C₀ _ (h C₀)

/-- Kanaya Definition 1 implies the reachability form `SolvesSSEM`. -/
theorem solvesSSEM_of_kanayaDefinition1 [DecidableEq Q]
    {P : Protocol Q Opinion Output} {n : ℕ} {hn : 2 ≤ n}
    (h : KanayaDefinition1 P n hn) :
    SolvesSSEM P n := by
  intro C₀
  obtain ⟨γ, t, hSafe⟩ := exists_execution_of_reachesGoalAlmostSurely P hn C₀ _ (h C₀).2
  exact ⟨γ, t, hSafe, (h C₀).1 γ t hSafe⟩

/-- If a configuration is already output-stable, then `SolvesSSEM` forces it to have the
correct exact-majority outputs: from it, a safe correct configuration is reachable, and outputs
cannot change on the way. -/
theorem exactMajoritySafe_of_outputStable_of_solves [DecidableEq Q]
    {P : Protocol Q Opinion Output} {n : ℕ}
    {C : Config Q Opinion n}
    (hSolves : SolvesSSEM P n)
    (hStable : C.isOutputStable P) :
    ExactMajoritySafe P C Opinion.A Opinion.B Output.A Output.B Output.T := by
  obtain ⟨γ, t, _hStable', hSafe'⟩ := hSolves C
  unfold ExactMajoritySafe at hSafe' ⊢
  rw [Config.agentsWithInput_execution P C γ t Opinion.A] at hSafe'
  rw [Config.agentsWithInput_execution P C γ t Opinion.B] at hSafe'
  by_cases hgt : (C.agentsWithInput Opinion.A).card >
      (C.agentsWithInput Opinion.B).card
  · simp [hgt] at hSafe' ⊢
    intro w
    rw [hStable γ t w]
    exact hSafe' w
  · by_cases hlt : (C.agentsWithInput Opinion.A).card <
        (C.agentsWithInput Opinion.B).card
    · simp [hgt, hlt] at hSafe' ⊢
      intro w
      rw [hStable γ t w]
      exact hSafe' w
    · simp [hgt, hlt] at hSafe' ⊢
      intro w
      rw [hStable γ t w]
      exact hSafe' w

/-- The two input classes partition the agents. -/
theorem Config.card_inputA_add_card_inputB (C : Config Q Opinion n) :
    (C.agentsWithInput Opinion.A).card + (C.agentsWithInput Opinion.B).card = n := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun v => C.inputOf v = Opinion.A)
  have hB : (Finset.univ.filter fun v => ¬ C.inputOf v = Opinion.A) =
      C.agentsWithInput Opinion.B := by
    ext v
    simp only [Config.agentsWithInput, Finset.mem_filter, Finset.mem_univ, true_and]
    cases C.inputOf v <;> simp
  rw [hB, Finset.card_univ, Fintype.card_fin] at hsplit
  exact hsplit

/-- For a silent protocol solving SSEM on `n ≥ 1` agents and any `k ≤ n`, there is a silent
configuration with exactly `k` agents of input `A` (and `n - k` of input `B`); being silent, it is
safe, hence it outputs the exact majority. -/
theorem exists_silent_config_with_inputA_card [DecidableEq Q] [Nonempty Q]
    {P : Protocol Q Opinion Output} {n : ℕ}
    (hSolves : SolvesSSEM P n) (hSilent : SilentProtocol P n) (k : ℕ) (hk : k ≤ n) :
    ∃ C : Config Q Opinion n, C.isSilent P ∧
      ExactMajoritySafe P C Opinion.A Opinion.B Output.A Output.B Output.T ∧
      (C.agentsWithInput Opinion.A).card = k ∧
      (C.agentsWithInput Opinion.B).card = n - k := by
  classical
  let q : Q := Classical.choice inferInstance
  let C₀ : Config Q Opinion n :=
    fun i => (q, if (i : ℕ) < k then Opinion.A else Opinion.B)
  have hA₀ : (C₀.agentsWithInput Opinion.A).card = k := by
    have hset : C₀.agentsWithInput Opinion.A =
        (Finset.univ.filter fun i : Fin n => (i : ℕ) < k) := by
      ext i
      by_cases hi : (i : ℕ) < k <;>
        simp [Config.agentsWithInput, Config.inputOf, C₀, hi]
    rw [hset, Fin.card_filter_val_lt]
    omega
  obtain ⟨γ, t, hS⟩ := hSilent C₀
  refine ⟨execution P C₀ γ t, hS,
    exactMajoritySafe_of_outputStable_of_solves hSolves hS.isOutputStable, ?_, ?_⟩
  · rw [Config.agentsWithInput_execution]
    exact hA₀
  · have hsum := Config.card_inputA_add_card_inputB (execution P C₀ γ t)
    rw [Config.agentsWithInput_execution P C₀ γ t Opinion.A, hA₀] at hsum
    omega

end Ripple.PopulationProtocol.SSEM

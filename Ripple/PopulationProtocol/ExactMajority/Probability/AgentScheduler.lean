/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The labelled-agent scheduler and the configuration chain

The uniform random scheduler can be run on `n` labelled agents `Fin n`: an assignment
`a : Fin n → Λ` gives every agent a state, a letter is an ordered pair of distinct agents,
and the letter `(i, j)` updates agents `i` and `j` by the transition `δ (a i) (a j)`. This
file proves that this labelled process, observed through its configuration (the multiset
of agent states), is the configuration Markov chain `Protocol.transitionKernel`.

The statements and their paper proofs are in `docs/audit/AGENT-SCHEDULER-LUMPING.md`:

* Lemma 1, `Protocol.ofAgents_agentStep`: one labelled step is one configuration step;
* Lemma 2, `card_filter_agentPair_states` and `card_agentPair_eq_totalPairs`: the number of
  ordered agent pairs in a given pair of states is `Config.interactionCount`, and the number
  of all ordered agent pairs is `Config.totalPairs`;
* Proposition 3, `Protocol.map_agentStep_letterPMF`: the configuration after one uniform
  letter has law `Protocol.stepDist`;
* Theorem 4, `Protocol.map_agentRun_eq_transitionKernel_pow`: under the product measure of
  uniform letters, the configuration after `T` letters has law
  `(P.transitionKernel ^ T) (Config.ofAgents a)`.

Theorem 4 is proved by induction on `T` splitting off the *first* letter: the product
measure on `ℕ → AgentPair n` is the image of `letter law × product measure` under prepending
a letter (`infinitePi_eq_map_seqCons`), and the Chapman–Kolmogorov identity
`κ ^ (1 + T) = κ ^ T ∘ₖ κ` then closes the induction with Proposition 3.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.MarkovChain
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Ordered pairs of distinct agents -/

/-- The letters of the labelled scheduler: ordered pairs `(i, j)` of distinct agents among
`n` labelled agents. -/
def AgentPair (n : ℕ) : Type := {p : Fin n × Fin n // p.1 ≠ p.2}

namespace AgentPair

variable {n : ℕ}

instance : Fintype (AgentPair n) :=
  inferInstanceAs (Fintype {p : Fin n × Fin n // p.1 ≠ p.2})

instance : DecidableEq (AgentPair n) :=
  inferInstanceAs (DecidableEq {p : Fin n × Fin n // p.1 ≠ p.2})

/-- The letters carry the discrete σ-algebra. -/
instance instMeasurableSpace : MeasurableSpace (AgentPair n) := ⊤

instance instDiscreteMeasurableSpace : DiscreteMeasurableSpace (AgentPair n) where
  forall_measurableSet _ := trivial

/-- The ordered pair of distinct agents `(i, j)`. -/
def mk (i j : Fin n) (h : i ≠ j) : AgentPair n := Subtype.mk (i, j) h

/-- The first agent (initiator) of a letter. -/
def initiator (p : AgentPair n) : Fin n := (Subtype.val p).1

/-- The second agent (responder) of a letter. -/
def responder (p : AgentPair n) : Fin n := (Subtype.val p).2

theorem initiator_ne_responder (p : AgentPair n) : p.initiator ≠ p.responder :=
  Subtype.property p

@[simp] theorem initiator_mk (i j : Fin n) (h : i ≠ j) : (mk i j h).initiator = i := rfl

@[simp] theorem responder_mk (i j : Fin n) (h : i ≠ j) : (mk i j h).responder = j := rfl

theorem ext {p q : AgentPair n} (h₁ : p.initiator = q.initiator)
    (h₂ : p.responder = q.responder) : p = q :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- With at least two agents there is a letter. -/
theorem nonempty (hn : 2 ≤ n) : Nonempty (AgentPair n) :=
  ⟨mk ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)⟩

/-- Ordered pairs of distinct agents with initiator in `A` and responder in `B` correspond
to the off-diagonal part of `A ×ˢ B`. -/
theorem card_filter_mem (A B : Finset (Fin n)) :
    (Finset.univ.filter fun p : AgentPair n => p.initiator ∈ A ∧ p.responder ∈ B).card =
      ((A ×ˢ B).filter fun q : Fin n × Fin n => q.1 ≠ q.2).card := by
  refine Finset.card_bij (fun p _ => (p.initiator, p.responder)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_product.2 hp.2, p.initiator_ne_responder⟩
  · intro p _ q _ h
    exact ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq
    exact ⟨mk q.1 q.2 hq.2, Finset.mem_filter.2 ⟨Finset.mem_univ _, hq.1⟩, rfl⟩

/-- The off-diagonal part of `A ×ˢ A` is `A.offDiag`. -/
theorem filter_product_self_ne (A : Finset (Fin n)) :
    ((A ×ˢ A).filter fun q : Fin n × Fin n => q.1 ≠ q.2) = A.offDiag := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag, and_assoc]

/-- There are `n (n - 1)` ordered pairs of distinct agents. -/
theorem card_eq (n : ℕ) : Fintype.card (AgentPair n) = n * (n - 1) := by
  have h := card_filter_mem (n := n) Finset.univ Finset.univ
  rw [filter_product_self_ne, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
    ← Nat.mul_sub_one] at h
  rw [← h, ← Finset.card_univ]
  congr 1
  exact (Finset.filter_true_of_mem fun p _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩).symm

end AgentPair

/-! ### Uniform letters and the scheduler measure -/

/-- The uniform law of one letter of the labelled scheduler. -/
noncomputable def letterPMF (n : ℕ) (hn : 2 ≤ n) : PMF (AgentPair n) :=
  haveI := AgentPair.nonempty hn
  PMF.uniformOfFintype (AgentPair n)

theorem letterPMF_apply {n : ℕ} (hn : 2 ≤ n) (p : AgentPair n) :
    letterPMF n hn p = (Fintype.card (AgentPair n) : ℝ≥0∞)⁻¹ := by
  have := AgentPair.nonempty hn
  exact PMF.uniformOfFintype_apply p

/-- The scheduler measure: independent uniform letters at times `0, 1, 2, …`. -/
noncomputable def schedulerMeasure (n : ℕ) (hn : 2 ≤ n) : Measure (ℕ → AgentPair n) :=
  Measure.infinitePi fun _ : ℕ => (letterPMF n hn).toMeasure

instance schedulerMeasure_isProbabilityMeasure {n : ℕ} (hn : 2 ≤ n) :
    IsProbabilityMeasure (schedulerMeasure n hn) := by
  unfold schedulerMeasure
  infer_instance

/-! ### Prepending a letter -/

/-- The sequence `x, ω 0, ω 1, …` obtained by prepending `x` to `ω`. -/
def seqCons {X : Type*} (x : X) (ω : ℕ → X) : ℕ → X
  | 0 => x
  | k + 1 => ω k

theorem measurable_seqCons {X : Type*} [MeasurableSpace X] :
    Measurable fun q : X × (ℕ → X) => seqCons q.1 q.2 := by
  refine measurable_pi_lambda _ fun k => ?_
  cases k with
  | zero => exact measurable_fst
  | succ k => exact (measurable_pi_apply k).comp measurable_snd

/-- Under the product of a probability measure `ν` over `ℕ`, the first coordinate and the
shifted sequence are independent: the product measure is the image of
`ν × (product measure)` under prepending a coordinate. -/
theorem infinitePi_eq_map_seqCons {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] :
    (ν.prod (Measure.infinitePi fun _ : ℕ => ν)).map (fun q => seqCons q.1 q.2) =
      Measure.infinitePi fun _ : ℕ => ν := by
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hmeas : MeasurableSet (Set.pi (↑s : Set ℕ) t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  have hpre : (fun q : X × (ℕ → X) => seqCons q.1 q.2) ⁻¹' Set.pi (↑s) t =
      (if 0 ∈ s then t 0 else Set.univ) ×ˢ
        Set.pi (↑(s.preimage Nat.succ Nat.succ_injective.injOn)) fun i => t (i + 1) := by
    ext ⟨x, ω⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
      Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨?_, fun i hi => h (i + 1) hi⟩
      split_ifs with h0
      · exact h 0 h0
      · exact Set.mem_univ x
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero =>
          rw [if_pos hi] at h0
          exact h0
      | succ i => exact h i hi
  have hzero : ∀ x ∈ s, x ∉ Set.range Nat.succ →
      (if x = 0 then (1 : ℝ≥0∞) else ν (t x)) = 1 := by
    intro x _ hx
    rcases x with _ | x
    · exact if_pos rfl
    · exact (hx ⟨x, rfl⟩).elim
  have hg := Finset.prod_preimage Nat.succ s Nat.succ_injective.injOn
    (fun x => if x = 0 then (1 : ℝ≥0∞) else ν (t x)) hzero
  simp only [Nat.succ_eq_add_one, Nat.add_one_ne_zero, ↓reduceIte] at hg
  have hsplit : ∏ i ∈ s, ν (t i) =
      (∏ i ∈ s, if i = 0 then ν (t 0) else 1) *
        ∏ i ∈ s, (if i = 0 then 1 else ν (t i)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = 0
    · subst hi
      simp
    · simp [hi]
  rw [Measure.map_apply measurable_seqCons hmeas, hpre, Measure.prod_prod,
    Measure.infinitePi_pi _ fun i _ => ht (i + 1), hg, hsplit, Finset.prod_ite_eq']
  congr 1
  split_ifs <;> simp

/-! ### Assignments and their configurations -/

namespace Config

variable {Λ : Type*} {n : ℕ}

/-- The configuration of an assignment of states to `n` labelled agents: the multiset of
their states. -/
def ofAgents (a : Fin n → Λ) : Config Λ := Multiset.map a Finset.univ.val

theorem card_ofAgents (a : Fin n → Λ) : (ofAgents a).card = n := by
  rw [ofAgents, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]

/-- The number of agents in state `s` is the count of `s` in the configuration. -/
theorem count_ofAgents [DecidableEq Λ] (a : Fin n → Λ) (s : Λ) :
    (ofAgents a).count s = (Finset.univ.filter fun i => a i = s).card := by
  rw [Config.count, ofAgents, Multiset.count_map, Finset.card_def, Finset.filter_val]
  exact congrArg Multiset.card (Multiset.filter_congr fun i _ => eq_comm)

/-- Splitting two distinct agents off the configuration. -/
theorem ofAgents_eq_cons (a : Fin n → Λ) {i j : Fin n} (hij : i ≠ j) :
    ofAgents a =
      a i ::ₘ a j ::ₘ (((Finset.univ : Finset (Fin n)).val.erase i).erase j).map a := by
  have hj : j ∈ (Finset.univ : Finset (Fin n)).val.erase i :=
    (Multiset.mem_erase_of_ne (Ne.symm hij)).2 (Finset.mem_univ j)
  have huniv : (Finset.univ : Finset (Fin n)).val =
      i ::ₘ j ::ₘ (((Finset.univ : Finset (Fin n)).val.erase i).erase j) := by
    rw [Multiset.cons_erase hj, Multiset.cons_erase (Finset.mem_univ i)]
  unfold ofAgents
  conv_lhs => rw [huniv]
  rw [Multiset.map_cons, Multiset.map_cons]

/-- An agent left after removing `i` and `j` is neither `i` nor `j`. -/
theorem ne_of_mem_erase_erase {i j k : Fin n}
    (hk : k ∈ (((Finset.univ : Finset (Fin n)).val.erase i).erase j)) : k ≠ i ∧ k ≠ j := by
  have h₁ := ((Multiset.Nodup.erase i Finset.univ.nodup).mem_erase_iff).1 hk
  have h₂ := (Finset.univ.nodup.mem_erase_iff).1 h₁.2
  exact ⟨h₂.1, h₁.1⟩

end Config

/-! ### Lemma 2: pair counts -/

section PairCounts

variable {Λ : Type*} {n : ℕ}

/-- **Lemma 2 (pair counts).** The number of ordered pairs of distinct agents `(i, j)` with
`a i = s₁` and `a j = s₂` is `Config.interactionCount (Config.ofAgents a) s₁ s₂`. -/
theorem card_filter_agentPair_states [DecidableEq Λ] (a : Fin n → Λ) (s₁ s₂ : Λ) :
    (Finset.univ.filter fun p : AgentPair n => a p.initiator = s₁ ∧ a p.responder = s₂).card =
      (Config.ofAgents a).interactionCount s₁ s₂ := by
  have hfilter :
      (Finset.univ.filter fun p : AgentPair n => a p.initiator = s₁ ∧ a p.responder = s₂) =
        Finset.univ.filter fun p : AgentPair n =>
          p.initiator ∈ Finset.univ.filter (fun i => a i = s₁) ∧
            p.responder ∈ Finset.univ.filter (fun i => a i = s₂) := by
    refine Finset.filter_congr fun p _ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfilter, AgentPair.card_filter_mem, Config.interactionCount, Config.count_ofAgents,
    Config.count_ofAgents]
  split_ifs with h
  · subst h
    rw [AgentPair.filter_product_self_ne, Finset.offDiag_card, Nat.mul_sub_one]
  · rw [← Finset.card_product]
    congr 1
    refine Finset.filter_true_of_mem fun q hq => ?_
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hq
    intro hq12
    exact h (hq.1.2.symm.trans ((congrArg a hq12).trans hq.2.2))

/-- **Lemma 2 (total).** The number of ordered pairs of distinct agents is
`Config.totalPairs (Config.ofAgents a)`. -/
theorem card_agentPair_eq_totalPairs (a : Fin n → Λ) :
    Fintype.card (AgentPair n) = (Config.ofAgents a).totalPairs := by
  rw [AgentPair.card_eq, Config.totalPairs, Config.card_ofAgents]

/-- Pushing the uniform letter forward to the pair of states of its two agents gives the
scheduler's law on ordered state pairs. -/
theorem map_statePair_letterPMF [Fintype Λ] [DecidableEq Λ] (a : Fin n → Λ) (hn : 2 ≤ n)
    (hc : 2 ≤ (Config.ofAgents a).card) :
    PMF.map (fun p : AgentPair n => (a p.initiator, a p.responder)) (letterPMF n hn) =
      (Config.ofAgents a).interactionPMF hc := by
  ext x
  rw [PMF.map_apply, tsum_fintype]
  simp_rw [letterPMF_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  change _ = ((Config.ofAgents a).interactionCount x.1 x.2 : ℝ≥0∞) /
    ((Config.ofAgents a).totalPairs : ℝ≥0∞)
  rw [← card_filter_agentPair_states a x.1 x.2, ← card_agentPair_eq_totalPairs a,
    div_eq_mul_inv]
  congr 3
  refine Finset.filter_congr fun p _ => ?_
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩
    exact Prod.ext h₁.symm h₂.symm

end PairCounts

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {n : ℕ}

namespace Protocol

/-! ### Labelled steps and runs -/

/-- The labelled step: letter `p = (i, j)` sets agent `i` to `(δ (a i) (a j)).1` and agent
`j` to `(δ (a i) (a j)).2`; the other agents keep their states. -/
def agentStep (P : Protocol Λ) (a : Fin n → Λ) (p : AgentPair n) : Fin n → Λ :=
  Function.update
    (Function.update a p.initiator (P.δ (a p.initiator) (a p.responder)).1)
    p.responder (P.δ (a p.initiator) (a p.responder)).2

/-- The labelled run: the assignment after the letters `ω 0, …, ω (T - 1)`. -/
def agentRun (P : Protocol Λ) : (Fin n → Λ) → (ℕ → AgentPair n) → ℕ → Fin n → Λ
  | a, _, 0 => a
  | a, ω, T + 1 => agentRun P (P.agentStep a (ω 0)) (fun k => ω (k + 1)) T

@[simp] theorem agentRun_zero (P : Protocol Λ) (a : Fin n → Λ) (ω : ℕ → AgentPair n) :
    P.agentRun a ω 0 = a := rfl

theorem agentRun_succ (P : Protocol Λ) (a : Fin n → Λ) (ω : ℕ → AgentPair n) (T : ℕ) :
    P.agentRun a ω (T + 1) = P.agentRun (P.agentStep a (ω 0)) (fun k => ω (k + 1)) T := rfl

/-- The run folds the labelled step over the letters in order: the last letter is applied
last. -/
theorem agentRun_succ' (P : Protocol Λ) (a : Fin n → Λ) (ω : ℕ → AgentPair n) (T : ℕ) :
    P.agentRun a ω (T + 1) = P.agentStep (P.agentRun a ω T) (ω T) := by
  induction T generalizing a ω with
  | zero => rfl
  | succ T ih =>
      rw [agentRun_succ P a ω (T + 1), ih (P.agentStep a (ω 0)) (fun k => ω (k + 1)),
        agentRun_succ P a ω T]

/-- The run after a prepended letter `p` is the run from `agentStep a p`. -/
theorem agentRun_seqCons (P : Protocol Λ) (a : Fin n → Λ) (p : AgentPair n)
    (ω : ℕ → AgentPair n) (T : ℕ) :
    P.agentRun a (seqCons p ω) (T + 1) = P.agentRun (P.agentStep a p) ω T := rfl

/-! ### Lemma 1: one labelled step is one configuration step -/

/-- `stepOrSelf` applied to a configuration that visibly contains the chosen pair. -/
theorem stepOrSelf_cons_cons (P : Protocol Λ) (x y : Λ) (M : Multiset Λ) :
    P.stepOrSelf (x ::ₘ y ::ₘ M) x y = (P.δ x y).1 ::ₘ (P.δ x y).2 ::ₘ M := by
  have hpair : ∀ u v : Λ, (u ::ₘ v ::ₘ M : Multiset Λ) = {u, v} + M := fun u v => by
    rw [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.cons_add, Multiset.cons_add,
      zero_add]
  have happ : Applicable (x ::ₘ y ::ₘ M) x y := by
    rw [Applicable, hpair]
    exact Multiset.le_add_right _ _
  unfold stepOrSelf
  rw [if_pos happ]
  change (x ::ₘ y ::ₘ M) - {x, y} + {(P.δ x y).1, (P.δ x y).2} = _
  rw [hpair x y, add_tsub_cancel_left, hpair]
  exact add_comm _ _

/-- **Lemma 1.** One labelled step is one configuration step: the configuration after the
letter `(i, j)` is `stepOrSelf` of the configuration at the states of agents `i` and `j`. -/
theorem ofAgents_agentStep (P : Protocol Λ) (a : Fin n → Λ) (p : AgentPair n) :
    Config.ofAgents (P.agentStep a p) =
      P.stepOrSelf (Config.ofAgents a) (a p.initiator) (a p.responder) := by
  have hij := p.initiator_ne_responder
  rw [Config.ofAgents_eq_cons _ hij, Config.ofAgents_eq_cons _ hij]
  have hi : P.agentStep a p p.initiator = (P.δ (a p.initiator) (a p.responder)).1 := by
    rw [agentStep, Function.update_of_ne hij, Function.update_self]
  have hj : P.agentStep a p p.responder = (P.δ (a p.initiator) (a p.responder)).2 := by
    rw [agentStep, Function.update_self]
  have hrest :
      (((Finset.univ : Finset (Fin n)).val.erase p.initiator).erase p.responder).map
          (P.agentStep a p) =
        (((Finset.univ : Finset (Fin n)).val.erase p.initiator).erase p.responder).map a :=
    Multiset.map_congr rfl fun k hk => by
      obtain ⟨hki, hkj⟩ := Config.ne_of_mem_erase_erase hk
      rw [agentStep, Function.update_of_ne hkj, Function.update_of_ne hki]
  rw [hi, hj, hrest, stepOrSelf_cons_cons]

/-! ### Proposition 3: one-step lumping -/

/-- **Proposition 3 (one-step lumping).** The configuration after one uniform letter has the
law `stepDist` of the configuration chain. -/
theorem map_agentStep_letterPMF (P : Protocol Λ) (a : Fin n → Λ) (hn : 2 ≤ n)
    (hc : 2 ≤ (Config.ofAgents a).card) :
    PMF.map (fun p => Config.ofAgents (P.agentStep a p)) (letterPMF n hn) =
      P.stepDist (Config.ofAgents a) hc := by
  rw [stepDist, ← map_statePair_letterPMF a hn hc, PMF.map_comp]
  congr 1
  funext p
  exact ofAgents_agentStep P a p

/-! ### Theorem 4: multi-step lumping -/

/-- Every event about the labelled run at a fixed time is measurable for the product
σ-algebra on letter sequences. -/
theorem measurableSet_agentRun_mem (P : Protocol Λ) (T : ℕ) :
    ∀ (a : Fin n → Λ) (S : Set (Fin n → Λ)),
      MeasurableSet {ω : ℕ → AgentPair n | P.agentRun a ω T ∈ S} := by
  induction T with
  | zero =>
      intro a S
      exact MeasurableSet.const (a ∈ S)
  | succ T ih =>
      intro a S
      have hset : {ω : ℕ → AgentPair n | P.agentRun a ω (T + 1) ∈ S} =
          ⋃ p : AgentPair n, (fun ω : ℕ → AgentPair n => ω 0) ⁻¹' {p} ∩
            (fun ω : ℕ → AgentPair n => fun k => ω (k + 1)) ⁻¹'
              {ω' | P.agentRun (P.agentStep a p) ω' T ∈ S} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff]
        constructor
        · intro h
          exact ⟨ω 0, rfl, h⟩
        · rintro ⟨p, rfl, h⟩
          exact h
      rw [hset]
      refine MeasurableSet.iUnion fun p => ?_
      exact ((measurable_pi_apply 0) (measurableSet_singleton p)).inter
        ((measurable_pi_lambda (fun ω : ℕ → AgentPair n => fun k => ω (k + 1))
          fun k => measurable_pi_apply (k + 1)) (ih _ _))

theorem measurable_ofAgents_agentRun (P : Protocol Λ) (a : Fin n → Λ) (T : ℕ) :
    Measurable fun ω : ℕ → AgentPair n => Config.ofAgents (P.agentRun a ω T) :=
  fun S _ => measurableSet_agentRun_mem P T a (Config.ofAgents ⁻¹' S)

/-- The scheduler measure is the image of `letter law × scheduler measure` under prepending
the letter. -/
theorem schedulerMeasure_eq_map_seqCons (hn : 2 ≤ n) :
    schedulerMeasure n hn =
      ((letterPMF n hn).toMeasure.prod (schedulerMeasure n hn)).map
        (fun q => seqCons q.1 q.2) :=
  (infinitePi_eq_map_seqCons _).symm

/-- One step of the configuration kernel from an assignment's configuration is the image of
the uniform letter. -/
theorem transitionKernel_ofAgents (P : Protocol Λ) (hn : 2 ≤ n) (a : Fin n → Λ) :
    P.transitionKernel (Config.ofAgents a) =
      (letterPMF n hn).toMeasure.map fun p => Config.ofAgents (P.agentStep a p) := by
  have hc : 2 ≤ (Config.ofAgents a).card := by rw [Config.card_ofAgents]; exact hn
  change (P.stepDistOrSelf _).toMeasure = _
  rw [stepDistOrSelf, dif_pos hc, ← map_agentStep_letterPMF P a hn hc]
  exact (PMF.toMeasure_map _ _ Measurable.of_discrete).symm

/-- **Theorem 4 (multi-step lumping).** Under the scheduler measure, the configuration of the
labelled run after `T` letters has the law of `T` steps of the configuration chain started at
the configuration of `a`. -/
theorem map_agentRun_eq_transitionKernel_pow (P : Protocol Λ) (hn : 2 ≤ n) (a : Fin n → Λ)
    (T : ℕ) :
    (schedulerMeasure n hn).map (fun ω => Config.ofAgents (P.agentRun a ω T)) =
      (P.transitionKernel ^ T) (Config.ofAgents a) := by
  induction T generalizing a with
  | zero =>
      rw [pow_zero]
      change (schedulerMeasure n hn).map (fun _ => Config.ofAgents a) =
        Kernel.id (Config.ofAgents a)
      rw [Measure.map_const, measure_univ, one_smul, Kernel.id_apply]
  | succ T ih =>
      ext S hS
      have hR : (P.transitionKernel ^ (T + 1)) (Config.ofAgents a) S =
          ∫⁻ p, (P.transitionKernel ^ T) (Config.ofAgents (P.agentStep a p)) S
            ∂(letterPMF n hn).toMeasure := by
        rw [add_comm T 1, Kernel.pow_add_apply_eq_lintegral _ 1 T _ hS, pow_one,
          transitionKernel_ofAgents P hn a,
          lintegral_map (Kernel.measurable_coe _ hS) Measurable.of_discrete]
      have hF := measurable_ofAgents_agentRun P a (T + 1) hS
      rw [hR, Measure.map_apply (measurable_ofAgents_agentRun P a (T + 1)) hS]
      conv_lhs => rw [schedulerMeasure_eq_map_seqCons hn]
      rw [Measure.map_apply measurable_seqCons hF, Measure.prod_apply (measurable_seqCons hF)]
      refine lintegral_congr fun p => ?_
      rw [← ih (P.agentStep a p), Measure.map_apply (measurable_ofAgents_agentRun P _ T) hS]
      rfl

end Protocol

end Ripple.PopulationProtocol.ExactMajority

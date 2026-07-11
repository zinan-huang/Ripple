/-
Generic population protocol model.

A population protocol is a pair P = (Λ, δ) where Λ is a finite state set and
δ : Λ × Λ → Λ × Λ is a (possibly randomized) transition function. A configuration
is a multiset of size n over Λ. Reachability c ⇒ c' holds when some sequence of
applicable transitions takes c to c'.

This file provides the generic infrastructure shared by any population protocol,
independent of the specific Doty et al. exact majority protocol. Future research
work building on top of exact majority can reuse these definitions.

Reference: Doty, Eftekhari, Gąsieniec, Severson, Stachowiak, Uznański,
"A time and space optimal stable population protocol solving exact majority"
(arXiv:2106.10201v2), §2.1.
-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace ExactMajority

/-- A (deterministic) population protocol on state set `Λ`. -/
structure Protocol (Λ : Type*) [Fintype Λ] [DecidableEq Λ] where
  /-- Transition function on ordered pairs of states. -/
  δ : Λ → Λ → Λ × Λ

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- A configuration is a multiset of agent states. The population size is
its cardinality. -/
abbrev Config (Λ : Type*) := Multiset Λ

/-- Population size of a configuration. -/
def Config.size (c : Config Λ) : ℕ := c.card

/-- Count of agents in state `s`. -/
def Config.count [DecidableEq Λ] (c : Config Λ) (s : Λ) : ℕ := Multiset.count s c

/-- Additive sum of a state observable over a configuration. -/
def Config.sumOf {M : Type*} [AddCommMonoid M] (f : Λ → M) (c : Config Λ) : M :=
  (c.map f).sum

namespace Protocol

variable (P : Protocol Λ)

/-- A transition `α : r₁, r₂ → p₁, p₂` is applicable to `c` if `c` contains both
`r₁` and `r₂` as a (multiset) submultiset. -/
def Applicable (c : Config Λ) (r₁ r₂ : Λ) : Prop :=
  {r₁, r₂} ≤ c

/-- One-step reachability: `c ⇒_α c'` for transition α applied to states r₁, r₂. -/
def StepRel (c c' : Config Λ) : Prop :=
  ∃ r₁ r₂, Applicable c r₁ r₂ ∧
    let (p₁, p₂) := P.δ r₁ r₂
    c' = c - {r₁, r₂} + {p₁, p₂}

/-- Deterministic one-step update for a chosen ordered pair of states. If the
pair is not present in the configuration, the update leaves the configuration
unchanged. -/
noncomputable def stepOrSelf (P : Protocol Λ) (c : Config Λ) (r₁ r₂ : Λ) : Config Λ := by
  classical
  exact
    if Applicable c r₁ r₂ then
      let p := P.δ r₁ r₂
      c - {r₁, r₂} + {p.1, p.2}
    else c

/-- Applying an applicable chosen pair with `stepOrSelf` gives a `StepRel`. -/
theorem stepRel_stepOrSelf_of_applicable {P : Protocol Λ} {c : Config Λ}
    {r₁ r₂ : Λ} (happ : Applicable c r₁ r₂) :
    P.StepRel c (stepOrSelf P c r₁ r₂) := by
  refine ⟨r₁, r₂, happ, ?_⟩
  unfold stepOrSelf
  rw [if_pos happ]

/-- If the chosen pair is not applicable, `stepOrSelf` is the identity. -/
theorem stepOrSelf_eq_self_of_not_applicable {P : Protocol Λ} {c : Config Λ}
    {r₁ r₂ : Λ} (happ : ¬Applicable c r₁ r₂) :
    stepOrSelf P c r₁ r₂ = c := by
  unfold stepOrSelf
  rw [if_neg happ]

/-- Reachability: reflexive-transitive closure of `StepRel`. -/
def Reachable (c c' : Config Λ) : Prop :=
  Relation.ReflTransGen P.StepRel c c'

/-- Every chosen-pair update is reachable: if the pair is applicable this is a
single protocol step, and otherwise it is the reflexive case. -/
theorem reachable_stepOrSelf {P : Protocol Λ} (c : Config Λ) (r₁ r₂ : Λ) :
    P.Reachable c (stepOrSelf P c r₁ r₂) := by
  by_cases happ : Applicable c r₁ r₂
  · exact Relation.ReflTransGen.single
      (stepRel_stepOrSelf_of_applicable (P := P) happ)
  · rw [stepOrSelf_eq_self_of_not_applicable (P := P) happ]
    exact Relation.ReflTransGen.refl

/-- A single population-protocol step preserves the population size. -/
theorem stepRel_card_eq {P : Protocol Λ} {c c' : Config Λ}
    (h_step : P.StepRel c c') :
    c'.card = c.card := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp at hc'
  subst c'
  have hpair_card : ({r₁, r₂} : Multiset Λ).card = 2 := by simp
  have hpair_le_card : 2 ≤ c.card := by
    simpa [hpair_card] using Multiset.card_le_card happ
  change Multiset.card
      (c - ({r₁, r₂} : Multiset Λ) +
        ({(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} : Multiset Λ)) = c.card
  rw [Multiset.card_add, Multiset.card_sub happ, hpair_card]
  simpa using Nat.sub_add_cancel hpair_le_card

/-- Reachability preserves the population size. -/
theorem reachable_card_eq {P : Protocol Λ} {c c' : Config Λ}
    (h_reach : P.Reachable c c') :
    c'.card = c.card := by
  induction h_reach with
  | refl => rfl
  | tail _ hstep ih =>
      exact (stepRel_card_eq hstep).trans ih

/-- A single population-protocol step preserves `Config.size`. -/
theorem stepRel_size_eq {P : Protocol Λ} {c c' : Config Λ}
    (h_step : P.StepRel c c') :
    c'.size = c.size :=
  stepRel_card_eq h_step

/-- The chosen-pair update preserves population size whether or not the pair is
applicable. -/
theorem stepOrSelf_card_eq {P : Protocol Λ} (c : Config Λ) (r₁ r₂ : Λ) :
    (stepOrSelf P c r₁ r₂).card = c.card := by
  by_cases happ : Applicable c r₁ r₂
  · exact stepRel_card_eq (stepRel_stepOrSelf_of_applicable (P := P) happ)
  · rw [stepOrSelf_eq_self_of_not_applicable (P := P) happ]

/-- `stepOrSelf` preserves `Config.size`. -/
theorem stepOrSelf_size_eq {P : Protocol Λ} (c : Config Λ) (r₁ r₂ : Λ) :
    (stepOrSelf P c r₁ r₂).size = c.size :=
  stepOrSelf_card_eq c r₁ r₂

/-- Reachability preserves `Config.size`. -/
theorem reachable_size_eq {P : Protocol Λ} {c c' : Config Λ}
    (h_reach : P.Reachable c c') :
    c'.size = c.size :=
  reachable_card_eq h_reach

/-- A single step preserves any additive state observable whose value is
preserved by the pair transition. -/
theorem stepRel_sumOf_eq {P : Protocol Λ} {M : Type*} [AddCommMonoid M]
    {f : Λ → M} {c c' : Config Λ}
    (hδ : ∀ r₁ r₂, let p := P.δ r₁ r₂; f p.1 + f p.2 = f r₁ + f r₂)
    (h_step : P.StepRel c c') :
    c'.sumOf f = c.sumOf f := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp at hc'
  rcases hpair : P.δ r₁ r₂ with ⟨p₁, p₂⟩
  subst c'
  have hδ' : f p₁ + f p₂ = f r₁ + f r₂ := by
    simpa [hpair] using hδ r₁ r₂
  dsimp [Config.sumOf]
  change ((c - ({r₁, r₂} : Multiset Λ) +
        ({(P.δ r₁ r₂).1, (P.δ r₁ r₂).2} : Multiset Λ)).map f).sum =
    (c.map f).sum
  rw [hpair]
  calc
    ((c - ({r₁, r₂} : Multiset Λ) + ({p₁, p₂} : Multiset Λ)).map f).sum
        = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum +
            (({p₁, p₂} : Multiset Λ).map f).sum := by
          rw [Multiset.map_add, Multiset.sum_add]
    _ = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum + (f p₁ + f p₂) := by
          simp
    _ = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum + (f r₁ + f r₂) := by
          rw [hδ']
    _ = ((c - ({r₁, r₂} : Multiset Λ)).map f).sum +
          (({r₁, r₂} : Multiset Λ).map f).sum := by
          simp
    _ = (((c - ({r₁, r₂} : Multiset Λ)) + ({r₁, r₂} : Multiset Λ)).map f).sum := by
          rw [Multiset.map_add, Multiset.sum_add]
    _ = (c.map f).sum := by
          rw [Multiset.sub_add_cancel happ]

/-- Reachability preserves any additive state observable whose value is
preserved by every pair transition. -/
theorem reachable_sumOf_eq {P : Protocol Λ} {M : Type*} [AddCommMonoid M]
    {f : Λ → M} {c c' : Config Λ}
    (hδ : ∀ r₁ r₂, let p := P.δ r₁ r₂; f p.1 + f p.2 = f r₁ + f r₂)
    (h_reach : P.Reachable c c') :
    c'.sumOf f = c.sumOf f := by
  induction h_reach with
  | refl => rfl
  | tail _ hstep ih =>
      exact (stepRel_sumOf_eq hδ hstep).trans ih

/-- `stepOrSelf` preserves any pairwise additive invariant whether or not the
chosen pair is applicable. -/
theorem stepOrSelf_sumOf_eq {P : Protocol Λ} {M : Type*} [AddCommMonoid M]
    {f : Λ → M}
    (hδ : ∀ r₁ r₂, let p := P.δ r₁ r₂; f p.1 + f p.2 = f r₁ + f r₂)
    (c : Config Λ) (r₁ r₂ : Λ) :
    (stepOrSelf P c r₁ r₂).sumOf f = c.sumOf f := by
  by_cases happ : Applicable c r₁ r₂
  · exact stepRel_sumOf_eq hδ (stepRel_stepOrSelf_of_applicable (P := P) happ)
  · rw [stepOrSelf_eq_self_of_not_applicable (P := P) happ]

end Protocol

/-- Output partition for a Boolean-valued (with tie) population protocol.
Λ is partitioned into states outputting A, B, or T. -/
structure OutputPartition (Λ : Type*) [Fintype Λ] where
  isA : Λ → Bool
  isB : Λ → Bool
  isT : Λ → Bool
  partition : ∀ s, (isA s).toNat + (isB s).toNat + (isT s).toNat = 1

/-- A configuration has a defined output `u` if all agents agree on output `u`. -/
def OutputPartition.output (part : OutputPartition Λ)
    (u : Bool × Bool × Bool) (c : Config Λ) : Prop :=
  ∀ s ∈ c, (part.isA s, part.isB s, part.isT s) = u

/-- A configuration `c` is **stable** with respect to an output partition iff
there exists a single output triple `u` such that every agent in `c` outputs
`u` AND every reachable configuration `c'` continues to have all agents
output the same `u`.

Paper §2.2: "we say `o` is stable if `φ(o)` is defined and, for all `o₂` such
that `o ⇒ o₂`, `φ(o) = φ(o₂)`." -/
def Protocol.IsStable (P : Protocol Λ) (part : OutputPartition Λ)
    (c : Config Λ) : Prop :=
  ∃ u, part.output u c ∧ ∀ c', P.Reachable c c' → part.output u c'

/-- A protocol **stably computes** a target predicate `target : Config → Bool ×
Bool × Bool` (mapping initial configs to their intended majority verdict)
if every initial configuration `init` satisfying the validity predicate has
some reachable configuration `o` that is `IsStable` with output equal to
`target init`.

Paper §2.2: "The protocol stably computes majority if, for any valid initial
configuration `i`, for all `c` such that `i ⇒ c`, there is a stable `o` such
that `c ⇒ o` and `φ(o) = M(i)`." -/
def Protocol.StablyComputes (P : Protocol Λ) (part : OutputPartition Λ)
    (valid : Config Λ → Prop)
    (target : Config Λ → Bool × Bool × Bool) : Prop :=
  ∀ init, valid init → ∀ c, P.Reachable init c →
    ∃ o, P.Reachable c o ∧
      part.output (target init) o ∧
      P.IsStable part o

end ExactMajority

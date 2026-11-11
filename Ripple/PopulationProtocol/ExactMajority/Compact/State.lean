/-
# The compact state type of Nonuniform Majority and its `O(L)` count

`CompactState L K` is the set of normal forms of `normalize` (`Compact/Live.lean`): the agents of
the flat type `AgentState L K` whose dead fields hold their defaults. The flat transition
induces a protocol `NonuniformMajorityCompact` on it (decode, run `Transition`, normalize), and
`Transition_normalize` (`Compact/Transition.lean`) makes `normalize` a state simulation of the
flat protocol by the compact one. Hence:

* `compact_stable_majority_correct`: `NonuniformMajorityCompact L K` stably computes majority
  on the compact valid initial configurations (`11 ≤ n ≤ 2^L`), transported from
  `stable_majority_correct` through `StateSimulation.stablyComputes`;
* `card_compactState_le`: `Fintype.card (CompactState L K) ≤ 73920 ((K + 53)(L + 1) + 4)`;
  at the paper's parameters `L = ⌈log₂ n⌉`, `K = 45` this is `73920 (98 ⌈log₂ n⌉ + 102)`,
  i.e. `O(log n)` states (`compact_state_count_clog`).

The constant `73920 = 2 · 3 · 11 · 5 · 2 · 7 · 2 · 8` is the product of the ranges of the eight
`O(1)` fields that every state keeps (`input`, `output`, `phase`, `role`, `assigned`,
`smallBias`, `full`, `opinions`); the factor `(K + 53)(L + 1) + 4` counts the at most one live
`Θ(L)` field (`bias`, `hour`, `minute` or `counter`, or none).
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Transition
import Ripple.PopulationProtocol.ExactMajority.Compact.Count
import Ripple.PopulationProtocol.ExactMajority.Basic.Simulation
import Ripple.PopulationProtocol.ExactMajority.Analysis.DeterministicChain

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

open CompactState

/-- The Doty et al. protocol on the compact state type: decode, run the flat transition,
normalize both results. -/
def NonuniformMajorityCompact (L K : ℕ) : Protocol (CompactState L K) where
  δ x y := (enc (Transition L K x.1 y.1).1, enc (Transition L K x.1 y.1).2)

/-- The compact protocol simulates the flat one on good states. -/
def simulation (L K : ℕ) :
    StateSimulation (NonuniformMajority L K) (NonuniformMajorityCompact L K) where
  Good := Good
  enc := enc
  emb := emb
  good_emb := good_emb
  enc_emb := enc_emb
  good_δ a b ha hb := (Transition_normalize a b ha hb).2.2
  enc_δ a b ha hb := by
    have h := Transition_normalize a b ha hb
    simp only [NonuniformMajorityCompact, NonuniformMajority, emb_enc]
    refine Prod.ext ?_ ?_
    · exact (Subtype.ext h.1).symm
    · exact (Subtype.ext h.2.1).symm

/-- Output partition of the compact protocol: the `output` field. -/
def compactPartition (L K : ℕ) : OutputPartition (CompactState L K) where
  isA x := (doutPartition L K).isA x.1
  isB x := (doutPartition L K).isB x.1
  isT x := (doutPartition L K).isT x.1
  partition x := (doutPartition L K).partition x.1

lemma outputCompat (L K : ℕ) :
    (simulation L K).OutputCompat (doutPartition L K) (compactPartition L K) := by
  intro a _
  simp [compactPartition, simulation, doutPartition, enc]

/-- Valid initial configurations of the compact protocol: every agent in phase 0, role MCR,
unassigned, with empty opinion set and the small bias of its input. -/
def compactValidInitial (D : Config (CompactState L K)) : Prop :=
  ∀ x ∈ D, (x.1.phase = ⟨0, by decide⟩) ∧ (x.1.role = .mcr) ∧
    (x.1.assigned = false) ∧
    (x.1.opinions = (⟨0, by decide⟩ : Fin 8)) ∧
    (x.1.input = .A → x.1.smallBias = ⟨4, by decide⟩) ∧
    (x.1.input = .B → x.1.smallBias = ⟨2, by decide⟩)

/-- The nonuniform regime of the correctness theorem, on compact configurations. -/
def compactValidInitialInRegime (L K : ℕ) (D : Config (CompactState L K)) : Prop :=
  compactValidInitial D ∧ 11 ≤ D.card ∧ D.card ≤ 2 ^ L

/-- Majority verdict of a compact configuration, from the inputs. -/
def compactMajorityVerdict (D : Config (CompactState L K)) : Bool × Bool × Bool :=
  let nA := (D.filter (fun x => x.1.input = .A)).card
  let nB := (D.filter (fun x => x.1.input = .B)).card
  if nA > nB then (true, false, false)
  else if nA < nB then (false, true, false)
  else (false, false, true)

lemma embC_eq (D : Config (CompactState L K)) :
    (simulation L K).embC D = D.map Subtype.val := rfl

lemma validInitial_embC (D : Config (CompactState L K)) (hD : compactValidInitial D) :
    validInitial ((simulation L K).embC D) := by
  intro a ha
  rw [embC_eq] at ha
  rcases Multiset.mem_map.mp ha with ⟨x, hx, rfl⟩
  exact hD x hx

lemma majorityVerdict_embC (D : Config (CompactState L K)) :
    compactMajorityVerdict D = majorityVerdict ((simulation L K).embC D) := by
  have hA : ((D.map Subtype.val).filter (fun a : AgentState L K => a.input = .A)).card =
      (D.filter (fun x : CompactState L K => x.1.input = .A)).card := by
    rw [Multiset.filter_map, Multiset.card_map]
    rfl
  have hB : ((D.map Subtype.val).filter (fun a : AgentState L K => a.input = .B)).card =
      (D.filter (fun x : CompactState L K => x.1.input = .B)).card := by
    rw [Multiset.filter_map, Multiset.card_map]
    rfl
  simp only [compactMajorityVerdict, majorityVerdict, embC_eq, hA, hB]

/-- **Stable correctness on the compact state type** (Doty et al. Theorem 3.1, correctness
part, with the `O(L)` state set): `NonuniformMajorityCompact L K` stably computes majority on
every valid initial configuration with `11 ≤ n ≤ 2^L`. -/
theorem compact_stable_majority_correct (L K : ℕ) :
    Protocol.StablyComputes (NonuniformMajorityCompact L K) (compactPartition L K)
      (compactValidInitialInRegime L K) compactMajorityVerdict := by
  refine (simulation L K).stablyComputes (outputCompat L K) ?_ ?_ (stable_majority_correct L K)
  · intro D hD
    refine ⟨validInitial_embC D hD.1, ?_, ?_⟩
    · simpa using hD.2.1
    · simpa using hD.2.2
  · intro D _
    exact majorityVerdict_embC D

/-- Fixed population size `n`, at the paper's exponent parameter `L = ⌈log₂ n⌉`. -/
theorem compact_stable_majority_correct_clog (K n : ℕ) (hlow : 11 ≤ n) :
    Protocol.StablyComputes (NonuniformMajorityCompact (Nat.clog 2 n) K)
      (compactPartition (Nat.clog 2 n) K)
      (fun D => compactValidInitial D ∧ D.card = n) compactMajorityVerdict := by
  intro D hD
  apply compact_stable_majority_correct (Nat.clog 2 n) K D
  exact ⟨hD.1, by rw [hD.2]; exact hlow, by rw [hD.2]; exact Nat.le_pow_clog (by omega) n⟩

/-- Non-vacuity: for every `n` there is a compact valid initial configuration of size `n`. -/
theorem compactValidInitial_nonempty (L K n : ℕ) :
    ∃ D : Config (CompactState L K), compactValidInitial D ∧ D.card = n := by
  refine ⟨Multiset.replicate n (enc (canonicalInitialAgent L K)), ?_, by simp⟩
  intro x hx
  rw [Multiset.eq_of_mem_replicate hx]
  simp [enc, canonicalInitialAgent]

#print axioms compact_stable_majority_correct
#print axioms compact_stable_majority_correct_clog
#print axioms compactValidInitial_nonempty

end Compact

end Ripple.PopulationProtocol.ExactMajority

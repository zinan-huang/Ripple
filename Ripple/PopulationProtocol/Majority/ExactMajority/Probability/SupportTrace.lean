/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite Support Traces

A finite Markov execution can be represented by a list of configurations where
each next configuration lies in the support of the one-step kernel.  This file
connects such stochastic support traces back to deterministic protocol
reachability and the exact-majority invariants.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SupportInvariants

namespace ExactMajority

namespace Protocol

variable {Λ : Type*}

/-- Endpoint of a finite trace whose elements are successive configurations. -/
def supportTraceEndpoint : Config Λ → List (Config Λ) → Config Λ
  | c, [] => c
  | _, c' :: rest => supportTraceEndpoint c' rest

/-- A finite trace through the support of a one-step stochastic kernel. -/
def supportTrace (step : Config Λ → PMF (Config Λ)) :
    Config Λ → List (Config Λ) → Prop
  | _, [] => True
  | c, c' :: rest => c' ∈ (step c).support ∧ supportTrace step c' rest

end Protocol

variable {L K : ℕ}

/-- Concrete support-trace predicate for the nonuniform exact-majority chain. -/
def nonuniformSupportTrace (L K : ℕ) :
    Config (AgentState L K) → List (Config (AgentState L K)) → Prop :=
  Protocol.supportTrace (nonuniformStepDistOrSelf L K)

/-- Endpoint of a concrete nonuniform support trace. -/
def nonuniformSupportTraceEndpoint (L K : ℕ) :
    Config (AgentState L K) → List (Config (AgentState L K)) →
      Config (AgentState L K) :=
  Protocol.supportTraceEndpoint

/-- Every finite stochastic support trace is a deterministic reachable path. -/
theorem nonuniformSupportTrace_reachable
    (c : Config (AgentState L K))
    (trace : List (Config (AgentState L K))) :
    nonuniformSupportTrace L K c trace →
      (NonuniformMajority L K).Reachable c
        (nonuniformSupportTraceEndpoint L K c trace) := by
  induction trace generalizing c with
  | nil =>
      intro _
      exact Relation.ReflTransGen.refl
  | cons c' rest ih =>
      intro htrace
      rcases htrace with ⟨hsupp, hrest⟩
      exact Relation.ReflTransGen.trans
        (nonuniformStepDistOrSelf_support_reachable (L := L) (K := K) c c' hsupp)
        (ih c' hrest)

/-- A finite stochastic support trace preserves population size. -/
theorem nonuniformSupportTrace_card_eq
    (c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (htrace : nonuniformSupportTrace L K c trace) :
    (nonuniformSupportTraceEndpoint L K c trace).card = c.card :=
  Protocol.reachable_card_eq
    (nonuniformSupportTrace_reachable (L := L) (K := K) c trace htrace)

/-- A finite stochastic support trace preserves the input gap. -/
theorem nonuniformSupportTrace_initialGap_eq
    (c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (htrace : nonuniformSupportTrace L K c trace) :
    initialGap (nonuniformSupportTraceEndpoint L K c trace) = initialGap c :=
  reachable_initialGap_invariant (L := L) (K := K) c
    (nonuniformSupportTraceEndpoint L K c trace)
    (nonuniformSupportTrace_reachable (L := L) (K := K) c trace htrace)

/-- A finite stochastic support trace preserves the majority verdict. -/
theorem nonuniformSupportTrace_majorityVerdict_eq
    (c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (htrace : nonuniformSupportTrace L K c trace) :
    majorityVerdict (nonuniformSupportTraceEndpoint L K c trace) =
      majorityVerdict c :=
  majorityVerdict_reachable_invariant (L := L) (K := K) c
    (nonuniformSupportTraceEndpoint L K c trace)
    (nonuniformSupportTrace_reachable (L := L) (K := K) c trace htrace)

/-- A finite stochastic support trace preserves well-formedness. -/
theorem nonuniformSupportTrace_well_formed_config
    (c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (hwell : well_formed_config c)
    (htrace : nonuniformSupportTrace L K c trace) :
    well_formed_config (nonuniformSupportTraceEndpoint L K c trace) :=
  well_formed_config_preserved_by_reachable (L := L) (K := K) c
    (nonuniformSupportTraceEndpoint L K c trace) hwell
    (nonuniformSupportTrace_reachable (L := L) (K := K) c trace htrace)

/-- If a finite stochastic support trace starts from a configuration reachable
from a valid initial configuration, then its endpoint remains reachable from
that initial configuration. -/
theorem validInitial_nonuniformSupportTrace_reachable
    (init c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (_hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (htrace : nonuniformSupportTrace L K c trace) :
    (NonuniformMajority L K).Reachable init
      (nonuniformSupportTraceEndpoint L K c trace) :=
  Relation.ReflTransGen.trans hreach
    (nonuniformSupportTrace_reachable (L := L) (K := K) c trace htrace)

/-- If a finite stochastic support trace starts from a configuration reachable
from a valid initial configuration, then its endpoint has the initial majority
verdict. -/
theorem validInitial_nonuniformSupportTrace_majorityVerdict_eq
    (init c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (_hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (htrace : nonuniformSupportTrace L K c trace) :
    majorityVerdict (nonuniformSupportTraceEndpoint L K c trace) =
      majorityVerdict init := by
  exact majorityVerdict_reachable_invariant (L := L) (K := K) init
    (nonuniformSupportTraceEndpoint L K c trace)
    (validInitial_nonuniformSupportTrace_reachable
      (L := L) (K := K) init c trace (by assumption) hreach htrace)

/-- If a finite stochastic support trace starts from a configuration reachable
from a valid initial configuration, then its endpoint has the original initial
input gap. -/
theorem validInitial_nonuniformSupportTrace_initialGap_eq
    (init c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (_hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (htrace : nonuniformSupportTrace L K c trace) :
    initialGap (nonuniformSupportTraceEndpoint L K c trace) =
      initialGap init := by
  exact reachable_initialGap_invariant (L := L) (K := K) init
    (nonuniformSupportTraceEndpoint L K c trace)
    (validInitial_nonuniformSupportTrace_reachable
      (L := L) (K := K) init c trace (by assumption) hreach htrace)

/-- If a finite stochastic support trace starts from a configuration reachable
from a valid initial configuration, then its endpoint is well formed. -/
theorem validInitial_nonuniformSupportTrace_well_formed_config
    (init c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (htrace : nonuniformSupportTrace L K c trace) :
    well_formed_config (nonuniformSupportTraceEndpoint L K c trace) :=
  validInitial_well_formed_config_of_reachable (L := L) (K := K) init
    (nonuniformSupportTraceEndpoint L K c trace) hvalid
    (validInitial_nonuniformSupportTrace_reachable
      (L := L) (K := K) init c trace hvalid hreach htrace)

/-- Finite stochastic support traces preserve all core deterministic
correctness invariants from the original valid initial configuration. -/
theorem validInitial_nonuniformSupportTrace_core_invariants
    (init c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (htrace : nonuniformSupportTrace L K c trace) :
    well_formed_config (nonuniformSupportTraceEndpoint L K c trace) ∧
      majorityVerdict (nonuniformSupportTraceEndpoint L K c trace) =
        majorityVerdict init ∧
      initialGap (nonuniformSupportTraceEndpoint L K c trace) =
        initialGap init :=
  ⟨validInitial_nonuniformSupportTrace_well_formed_config
      (L := L) (K := K) init c trace hvalid hreach htrace,
    validInitial_nonuniformSupportTrace_majorityVerdict_eq
      (L := L) (K := K) init c trace hvalid hreach htrace,
    validInitial_nonuniformSupportTrace_initialGap_eq
      (L := L) (K := K) init c trace hvalid hreach htrace⟩

/-- Stable witness produced by a finite stochastic support trace whose endpoint
is a Phase-10 majority witness. -/
theorem stable_witness_of_nonuniformSupportTrace_phase10MajorityWitness
    (init c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (htrace : nonuniformSupportTrace L K c trace)
    (hwitness :
      phase10MajorityWitness (L := L) (K := K) init
        (nonuniformSupportTraceEndpoint L K c trace)) :
    ∃ o, (NonuniformMajority L K).Reachable c o ∧
      (doutPartition L K).output (majorityVerdict init) o ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) o :=
  stable_witness_of_phase10MajorityWitness (L := L) (K := K) init c
    (nonuniformSupportTraceEndpoint L K c trace)
    (nonuniformSupportTrace_reachable (L := L) (K := K) c trace htrace)
    hwitness

/-- Direct stable-output package for a finite stochastic support trace whose
endpoint is a Phase-10 majority witness. -/
theorem stable_output_of_nonuniformSupportTrace_phase10MajorityWitness
    (init c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (hwitness :
      phase10MajorityWitness (L := L) (K := K) init
        (nonuniformSupportTraceEndpoint L K c trace)) :
    (doutPartition L K).output (majorityVerdict init)
        (nonuniformSupportTraceEndpoint L K c trace) ∧
      (NonuniformMajority L K).IsStable (doutPartition L K)
        (nonuniformSupportTraceEndpoint L K c trace) :=
  stable_output_of_phase10MajorityWitness (L := L) (K := K) init
    (nonuniformSupportTraceEndpoint L K c trace) hwitness

/-- Stable witness produced by a finite stochastic support trace whose endpoint
is in Phase 10 and has the majority output in partition form. -/
theorem stable_witness_of_nonuniformSupportTrace_phase10_partition_output
    (init c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (htrace : nonuniformSupportTrace L K c trace)
    (hphase :
      ∀ a ∈ nonuniformSupportTraceEndpoint L K c trace, a.phase.val = 10)
    (hout :
      (doutPartition L K).output (majorityVerdict init)
        (nonuniformSupportTraceEndpoint L K c trace)) :
    ∃ o, (NonuniformMajority L K).Reachable c o ∧
      (doutPartition L K).output (majorityVerdict init) o ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) o :=
  stable_witness_of_phase10_partition_output (L := L) (K := K) init c
    (nonuniformSupportTraceEndpoint L K c trace)
    (nonuniformSupportTrace_reachable (L := L) (K := K) c trace htrace)
    hphase hout

/-- Direct stable-output package for a finite stochastic support trace whose
endpoint is in Phase 10 and has the majority output in partition form. -/
theorem stable_output_of_nonuniformSupportTrace_phase10_partition_output
    (init c : Config (AgentState L K))
    (trace : List (Config (AgentState L K)))
    (hphase :
      ∀ a ∈ nonuniformSupportTraceEndpoint L K c trace, a.phase.val = 10)
    (hout :
      (doutPartition L K).output (majorityVerdict init)
        (nonuniformSupportTraceEndpoint L K c trace)) :
    (doutPartition L K).output (majorityVerdict init)
        (nonuniformSupportTraceEndpoint L K c trace) ∧
      (NonuniformMajority L K).IsStable (doutPartition L K)
        (nonuniformSupportTraceEndpoint L K c trace) :=
  stable_output_of_phase10_partition_output (L := L) (K := K) init
    (nonuniformSupportTraceEndpoint L K c trace) hphase hout

/-- Correctness reduction for phase analyses that produce finite stochastic
support traces ending at Phase-10 majority-witness configurations. -/
theorem stable_majority_correct_of_supportTrace_phase10MajorityWitness
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ trace : List (Config (AgentState L K)),
              nonuniformSupportTrace L K c trace ∧
                phase10MajorityWitness (L := L) (K := K) init
                  (nonuniformSupportTraceEndpoint L K c trace)) :
    stable_majority_correct_target L K := by
  intro init hinit c hreach
  rcases hphase init hinit c hreach with ⟨trace, htrace, hwitness⟩
  exact stable_witness_of_nonuniformSupportTrace_phase10MajorityWitness
    (L := L) (K := K) init c trace htrace hwitness

/-- Correctness reduction for phase analyses that produce finite stochastic
support traces ending at Phase-10 endpoints with output stated through
`doutPartition`. -/
theorem stable_majority_correct_of_supportTrace_phase10_partition_output
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ trace : List (Config (AgentState L K)),
              nonuniformSupportTrace L K c trace ∧
                (∀ a ∈ nonuniformSupportTraceEndpoint L K c trace,
                  a.phase.val = 10) ∧
                (doutPartition L K).output (majorityVerdict init)
                  (nonuniformSupportTraceEndpoint L K c trace)) :
    stable_majority_correct_target L K := by
  intro init hinit c hreach
  rcases hphase init hinit c hreach with ⟨trace, htrace, hphase10, hout⟩
  exact stable_witness_of_nonuniformSupportTrace_phase10_partition_output
    (L := L) (K := K) init c trace htrace hphase10 hout

theorem nonuniform_majority_correctness_of_supportTrace_phase10MajorityWitness
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ trace : List (Config (AgentState L K)),
              nonuniformSupportTrace L K c trace ∧
                phase10MajorityWitness (L := L) (K := K) init
                  (nonuniformSupportTraceEndpoint L K c trace)) :
    nonuniform_majority_correctness_target L K :=
  stable_majority_correct_of_supportTrace_phase10MajorityWitness
    (L := L) (K := K) hphase

theorem nonuniform_majority_correctness_of_supportTrace_phase10_partition_output
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ trace : List (Config (AgentState L K)),
              nonuniformSupportTrace L K c trace ∧
                (∀ a ∈ nonuniformSupportTraceEndpoint L K c trace,
                  a.phase.val = 10) ∧
                (doutPartition L K).output (majorityVerdict init)
                  (nonuniformSupportTraceEndpoint L K c trace)) :
    nonuniform_majority_correctness_target L K :=
  stable_majority_correct_of_supportTrace_phase10_partition_output
    (L := L) (K := K) hphase

end ExactMajority

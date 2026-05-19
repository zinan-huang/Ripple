/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Scheduled Pair Traces

A random scheduler samples a finite sequence of ordered state pairs.  This file
defines the deterministic execution obtained from such a realized schedule and
proves that it is a genuine protocol-reachable configuration.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SupportInvariants

namespace ExactMajority

namespace Protocol

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Execute a finite realized schedule of ordered state pairs.  Non-applicable
pairs are interpreted by `stepOrSelf`, so they leave the configuration
unchanged. -/
noncomputable def runPairs (P : Protocol Λ) :
    Config Λ → List (Λ × Λ) → Config Λ
  | c, [] => c
  | c, pair :: rest => runPairs P (stepOrSelf P c pair.1 pair.2) rest

/-- Running a finite realized schedule always lands in a protocol-reachable
configuration. -/
theorem reachable_runPairs (P : Protocol Λ) (c : Config Λ)
    (pairs : List (Λ × Λ)) :
    P.Reachable c (runPairs P c pairs) := by
  induction pairs generalizing c with
  | nil =>
      exact Relation.ReflTransGen.refl
  | cons pair rest ih =>
      exact Relation.ReflTransGen.trans
        (reachable_stepOrSelf (P := P) c pair.1 pair.2)
        (ih (stepOrSelf P c pair.1 pair.2))

/-- A finite realized schedule preserves population size. -/
theorem runPairs_card_eq (P : Protocol Λ) (c : Config Λ)
    (pairs : List (Λ × Λ)) :
    (runPairs P c pairs).card = c.card :=
  reachable_card_eq (reachable_runPairs P c pairs)

/-- A finite realized schedule preserves every additive state observable that
is preserved by every pair transition. -/
theorem runPairs_sumOf_eq {M : Type*} [AddCommMonoid M]
    (P : Protocol Λ) {f : Λ → M}
    (hδ : ∀ r₁ r₂, let p := P.δ r₁ r₂; f p.1 + f p.2 = f r₁ + f r₂)
    (c : Config Λ) (pairs : List (Λ × Λ)) :
    (runPairs P c pairs).sumOf f = c.sumOf f :=
  reachable_sumOf_eq hδ (reachable_runPairs P c pairs)

end Protocol

variable {L K : ℕ}

/-- Concrete finite scheduled execution for the nonuniform exact-majority
protocol. -/
noncomputable def nonuniformRunPairs (L K : ℕ) :
    Config (AgentState L K) → List (AgentState L K × AgentState L K) →
      Config (AgentState L K) :=
  Protocol.runPairs (NonuniformMajority L K)

/-- A concrete finite scheduled execution is reachable in the nonuniform
majority protocol. -/
theorem nonuniformRunPairs_reachable
    (c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K)) :
    (NonuniformMajority L K).Reachable c (nonuniformRunPairs L K c pairs) :=
  Protocol.reachable_runPairs (NonuniformMajority L K) c pairs

/-- A concrete finite scheduled execution preserves population size. -/
theorem nonuniformRunPairs_card_eq
    (c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K)) :
    (nonuniformRunPairs L K c pairs).card = c.card :=
  Protocol.runPairs_card_eq (NonuniformMajority L K) c pairs

/-- A concrete finite scheduled execution preserves the initial input gap. -/
theorem nonuniformRunPairs_initialGap_eq
    (c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K)) :
    initialGap (nonuniformRunPairs L K c pairs) = initialGap c :=
  reachable_initialGap_invariant (L := L) (K := K) c
    (nonuniformRunPairs L K c pairs)
    (nonuniformRunPairs_reachable (L := L) (K := K) c pairs)

/-- A concrete finite scheduled execution preserves the majority verdict. -/
theorem nonuniformRunPairs_majorityVerdict_eq
    (c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K)) :
    majorityVerdict (nonuniformRunPairs L K c pairs) = majorityVerdict c :=
  majorityVerdict_reachable_invariant (L := L) (K := K) c
    (nonuniformRunPairs L K c pairs)
    (nonuniformRunPairs_reachable (L := L) (K := K) c pairs)

/-- A concrete finite scheduled execution preserves configuration
well-formedness. -/
theorem nonuniformRunPairs_well_formed_config
    (c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K))
    (hwell : well_formed_config c) :
    well_formed_config (nonuniformRunPairs L K c pairs) :=
  well_formed_config_preserved_by_reachable (L := L) (K := K) c
    (nonuniformRunPairs L K c pairs) hwell
    (nonuniformRunPairs_reachable (L := L) (K := K) c pairs)

/-- If a finite realized schedule starts from a configuration reachable from a
valid initial configuration, then its endpoint remains reachable from that
initial configuration. -/
theorem validInitial_nonuniformRunPairs_reachable
    (init c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K))
    (_hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    (NonuniformMajority L K).Reachable init (nonuniformRunPairs L K c pairs) :=
  Relation.ReflTransGen.trans hreach
    (nonuniformRunPairs_reachable (L := L) (K := K) c pairs)

/-- A finite realized schedule from a reachable configuration preserves the
original initial input gap. -/
theorem validInitial_nonuniformRunPairs_initialGap_eq
    (init c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K))
    (_hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    initialGap (nonuniformRunPairs L K c pairs) = initialGap init :=
  reachable_initialGap_invariant (L := L) (K := K) init
    (nonuniformRunPairs L K c pairs)
    (validInitial_nonuniformRunPairs_reachable
      (L := L) (K := K) init c pairs (by assumption) hreach)

/-- A finite realized schedule from a reachable configuration preserves the
original majority verdict. -/
theorem validInitial_nonuniformRunPairs_majorityVerdict_eq
    (init c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K))
    (_hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    majorityVerdict (nonuniformRunPairs L K c pairs) = majorityVerdict init :=
  majorityVerdict_reachable_invariant (L := L) (K := K) init
    (nonuniformRunPairs L K c pairs)
    (validInitial_nonuniformRunPairs_reachable
      (L := L) (K := K) init c pairs (by assumption) hreach)

/-- A finite realized schedule from a reachable configuration preserves
well-formedness inherited from a valid initial configuration. -/
theorem validInitial_nonuniformRunPairs_well_formed_config
    (init c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K))
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    well_formed_config (nonuniformRunPairs L K c pairs) :=
  validInitial_well_formed_config_of_reachable (L := L) (K := K) init
    (nonuniformRunPairs L K c pairs) hvalid
    (validInitial_nonuniformRunPairs_reachable
      (L := L) (K := K) init c pairs hvalid hreach)

/-- Finite realized schedules preserve all core deterministic correctness
invariants from the original valid initial configuration. -/
theorem validInitial_nonuniformRunPairs_core_invariants
    (init c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K))
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    well_formed_config (nonuniformRunPairs L K c pairs) ∧
      majorityVerdict (nonuniformRunPairs L K c pairs) = majorityVerdict init ∧
      initialGap (nonuniformRunPairs L K c pairs) = initialGap init :=
  ⟨validInitial_nonuniformRunPairs_well_formed_config
      (L := L) (K := K) init c pairs hvalid hreach,
    validInitial_nonuniformRunPairs_majorityVerdict_eq
      (L := L) (K := K) init c pairs hvalid hreach,
    validInitial_nonuniformRunPairs_initialGap_eq
      (L := L) (K := K) init c pairs hvalid hreach⟩

/-- Stable witness produced by a finite realized schedule whose endpoint is a
Phase-10 majority witness. -/
theorem stable_witness_of_nonuniformRunPairs_phase10MajorityWitness
    (init c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K))
    (hwitness :
      phase10MajorityWitness (L := L) (K := K) init
        (nonuniformRunPairs L K c pairs)) :
    ∃ o, (NonuniformMajority L K).Reachable c o ∧
      (doutPartition L K).output (majorityVerdict init) o ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) o :=
  stable_witness_of_phase10MajorityWitness (L := L) (K := K) init c
    (nonuniformRunPairs L K c pairs)
    (nonuniformRunPairs_reachable (L := L) (K := K) c pairs)
    hwitness

/-- Direct stable-output package for a finite realized schedule whose endpoint
is a Phase-10 majority witness. -/
theorem stable_output_of_nonuniformRunPairs_phase10MajorityWitness
    (init c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K))
    (hwitness :
      phase10MajorityWitness (L := L) (K := K) init
        (nonuniformRunPairs L K c pairs)) :
    (doutPartition L K).output (majorityVerdict init)
        (nonuniformRunPairs L K c pairs) ∧
      (NonuniformMajority L K).IsStable (doutPartition L K)
        (nonuniformRunPairs L K c pairs) :=
  stable_output_of_phase10MajorityWitness (L := L) (K := K) init
    (nonuniformRunPairs L K c pairs) hwitness

/-- Stable witness produced by a finite realized schedule whose endpoint is in
Phase 10 and has the majority output in the generic partition form. -/
theorem stable_witness_of_nonuniformRunPairs_phase10_partition_output
    (init c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K))
    (hphase : ∀ a ∈ nonuniformRunPairs L K c pairs, a.phase.val = 10)
    (hout :
      (doutPartition L K).output (majorityVerdict init)
        (nonuniformRunPairs L K c pairs)) :
    ∃ o, (NonuniformMajority L K).Reachable c o ∧
      (doutPartition L K).output (majorityVerdict init) o ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) o :=
  stable_witness_of_phase10_partition_output (L := L) (K := K) init c
    (nonuniformRunPairs L K c pairs)
    (nonuniformRunPairs_reachable (L := L) (K := K) c pairs)
    hphase hout

/-- Direct stable-output package for a finite realized schedule whose endpoint
is in Phase 10 and has the majority output in the generic partition form. -/
theorem stable_output_of_nonuniformRunPairs_phase10_partition_output
    (init c : Config (AgentState L K))
    (pairs : List (AgentState L K × AgentState L K))
    (hphase : ∀ a ∈ nonuniformRunPairs L K c pairs, a.phase.val = 10)
    (hout :
      (doutPartition L K).output (majorityVerdict init)
        (nonuniformRunPairs L K c pairs)) :
    (doutPartition L K).output (majorityVerdict init)
        (nonuniformRunPairs L K c pairs) ∧
      (NonuniformMajority L K).IsStable (doutPartition L K)
        (nonuniformRunPairs L K c pairs) :=
  stable_output_of_phase10_partition_output (L := L) (K := K) init
    (nonuniformRunPairs L K c pairs) hphase hout

/-- Correctness reduction for phase analyses that produce finite scheduled
Phase-10 majority-witness endpoints. -/
theorem stable_majority_correct_of_scheduled_phase10MajorityWitness
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ pairs : List (AgentState L K × AgentState L K),
              phase10MajorityWitness (L := L) (K := K) init
                (nonuniformRunPairs L K c pairs)) :
    stable_majority_correct_target L K := by
  intro init hinit c hreach
  rcases hphase init hinit c hreach with ⟨pairs, hpairs⟩
  exact stable_witness_of_nonuniformRunPairs_phase10MajorityWitness
    (L := L) (K := K) init c pairs hpairs

/-- Correctness reduction for phase analyses that produce finite scheduled
Phase-10 endpoints with output stated through `doutPartition`. -/
theorem stable_majority_correct_of_scheduled_phase10_partition_output
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ pairs : List (AgentState L K × AgentState L K),
              (∀ a ∈ nonuniformRunPairs L K c pairs, a.phase.val = 10) ∧
                (doutPartition L K).output (majorityVerdict init)
                  (nonuniformRunPairs L K c pairs)) :
    stable_majority_correct_target L K := by
  intro init hinit c hreach
  rcases hphase init hinit c hreach with ⟨pairs, hphase10, hout⟩
  exact stable_witness_of_nonuniformRunPairs_phase10_partition_output
    (L := L) (K := K) init c pairs hphase10 hout

theorem nonuniform_majority_correctness_of_scheduled_phase10MajorityWitness
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ pairs : List (AgentState L K × AgentState L K),
              phase10MajorityWitness (L := L) (K := K) init
                (nonuniformRunPairs L K c pairs)) :
    nonuniform_majority_correctness_target L K :=
  stable_majority_correct_of_scheduled_phase10MajorityWitness
    (L := L) (K := K) hphase

theorem nonuniform_majority_correctness_of_scheduled_phase10_partition_output
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ pairs : List (AgentState L K × AgentState L K),
              (∀ a ∈ nonuniformRunPairs L K c pairs, a.phase.val = 10) ∧
                (doutPartition L K).output (majorityVerdict init)
                  (nonuniformRunPairs L K c pairs)) :
    nonuniform_majority_correctness_target L K :=
  stable_majority_correct_of_scheduled_phase10_partition_output
    (L := L) (K := K) hphase

end ExactMajority

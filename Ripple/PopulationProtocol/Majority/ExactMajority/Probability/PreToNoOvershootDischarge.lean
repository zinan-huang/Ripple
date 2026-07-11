import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamNoOvershoot

/-!
# PreToNoOvershootDischarge

The old `hPreToNoOvershoot` surface was

```
∀ (k : Fin 10) (c : Config _),
  (allPhaseGe (seamP k) n c ∧ advTriggered (seamP k + 1) c) →
  SeamNoOvershoot.NoOvershoot (seamP k) c
```

This is a blanket `∀ c` over all configurations.  It has the same risk profile as
the retired `hReach10` field: it quantifies over adversarial, non-reachable states.

This file records the adversarial check and the honest replacement.

Result:

* the blanket statement is refutable by a simple non-reachable overshot
  configuration;
* the sharp true replacement is the chain-restricted residual

```
PreToNoOvershootReachableResidual init n seamP
```

which asks for the implication only on configurations reachable from the actual
initial configuration;
* this chain-restricted residual suffices measure-theoretically: at every finite
  horizon, the mass of seam-pre states that violate `NoOvershoot` is zero.

No global `∀ c` well-formedness claim is introduced.
-/

namespace ExactMajority
namespace PreToNoOvershootDischarge

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The seam precondition whose blanket-to-`NoOvershoot` implication is suspect. -/
def SeamPre (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
    SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c

/-- The genuine seam-entry predicate.  Unlike `SeamPre`, this is a proper start
state for the no-overshoot tail: it includes the seam shape, no already-overshot
agent, and no phase-`p+1` clock already sitting at counter zero. -/
def SeamEntry (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  SeamPre (L := L) (K := K) p n c ∧
    SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c ∧
      ¬ SeamNoOvershoot.AtRiskClockZero (L := L) (K := K) p c

/-- Projection from genuine seam-entry to the weak seam shape. -/
theorem SeamEntry.seamPre {p n : ℕ} {c : Config (AgentState L K)}
    (h : SeamEntry (L := L) (K := K) p n c) :
    SeamPre (L := L) (K := K) p n c :=
  h.1

/-- Projection from genuine seam-entry to no-overshoot at entry. -/
theorem SeamEntry.noOvershoot {p n : ℕ} {c : Config (AgentState L K)}
    (h : SeamEntry (L := L) (K := K) p n c) :
    SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c :=
  h.2.1

/-- Projection from genuine seam-entry to the no-at-risk freshness fact. -/
theorem SeamEntry.notAtRiskClockZero {p n : ℕ} {c : Config (AgentState L K)}
    (h : SeamEntry (L := L) (K := K) p n c) :
    ¬ SeamNoOvershoot.AtRiskClockZero (L := L) (K := K) p c :=
  h.2.2

/-- The work-to-seam entry residual.  From the work `Post`, the one-step seed handoff
must land in a genuine `SeamEntry` state almost surely, not merely in weak
`SeamPre`.  This is the satisfiable replacement for the old implicit
`work.Post → SeamPre` handoff when the current work-post interface has not yet
exposed the no-overshoot-at-entry and counter-freshness facts. -/
def SeamEntryFromWorkPost (p n : ℕ) (workPost : Config (AgentState L K) → Prop) : Prop :=
  ∀ c : Config (AgentState L K), workPost c →
    ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ SeamEntry (L := L) (K := K) p n c'} = 0

/-- A canonical adversarial agent already overshot to phase `p+2`. -/
def overshotAgent (p : ℕ) (hp : p + 2 < 11) : AgentState L K :=
  { input := .A
    output := .A
    phase := ⟨p + 2, hp⟩
    role := .main
    assigned := false
    bias := .zero
    smallBias := ⟨0, by decide⟩
    hour := ⟨0, by omega⟩
    minute := ⟨0, by omega⟩
    full := false
    opinions := ⟨0, by decide⟩
    counter := ⟨0, by omega⟩ }

private theorem mem_replicate_eq {α : Type*} {a b : α} {n : ℕ} :
    b ∈ Multiset.replicate n a → b = a :=
  Multiset.eq_of_mem_replicate

private theorem one_le_countP_replicate_of_true
    {α : Type*} (P : α → Prop) [DecidablePred P] {a : α} {n : ℕ}
    (hn : 0 < n) (ha : P a) :
    1 ≤ Multiset.countP P (Multiset.replicate n a) := by
  exact Nat.succ_le_of_lt
    (Multiset.countP_pos_of_mem
      (p := P)
      (s := Multiset.replicate n a)
      (a := a)
      (Multiset.mem_replicate.2 ⟨Nat.ne_of_gt hn, rfl⟩)
      ha)

set_option maxHeartbeats 4000000 in
/--
A concrete non-reachable-style counterexample to the blanket implication.

For any positive population size and any seam with `p+2` still a valid phase,
take every agent to already be at phase `p+2`.  Then the seam precondition
`allPhaseGe p n ∧ advTriggered (p+1)` holds, but `NoOvershoot p` fails.
-/
theorem overshot_config_counterexample
    {p n : ℕ} (hp : p + 2 < 11) (hn : 0 < n) :
    ∃ c : Config (AgentState L K),
      SeamPre (L := L) (K := K) p n c ∧
        ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c := by
  classical
  let a : AgentState L K := overshotAgent (L := L) (K := K) p hp
  let c : Config (AgentState L K) := Multiset.replicate n a
  refine ⟨c, ?_, ?_⟩
  · constructor
    · constructor
      · simp [c]
      · intro b hb
        have hb_eq : b = a := mem_replicate_eq hb
        rw [hb_eq]
        simp [a, overshotAgent]
    · unfold SeamEpidemics.advTriggered
      have ha :
          (fun b : AgentState L K => decide (p + 1 ≤ b.phase.val)) a := by
        simp [a, overshotAgent]
      exact
        one_le_countP_replicate_of_true
          (fun b : AgentState L K => decide (p + 1 ≤ b.phase.val))
          hn ha
  · intro hno
    have ha_mem : a ∈ c := by
      exact Multiset.mem_replicate.2 ⟨Nat.ne_of_gt hn, rfl⟩
    have hlt := hno a ha_mem
    simp [a, overshotAgent] at hlt

set_option maxHeartbeats 4000000 in
/--
The blanket `hPreToNoOvershoot` implication is refutable.

This theorem is the adversarial audit result: the old all-config statement cannot
be honestly discharged from the bare seam precondition alone.
-/
theorem blanket_hPreToNoOvershoot_refutable
    {p n : ℕ} (hp : p + 2 < 11) (hn : 0 < n) :
    ¬ (∀ c : Config (AgentState L K),
      SeamPre (L := L) (K := K) p n c →
        SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c) := by
  intro hblanket
  rcases overshot_config_counterexample (L := L) (K := K) hp hn with
    ⟨c, hpre, hbad⟩
  exact hbad (hblanket c hpre)

/--
The sharp honest replacement for the blanket field.

The implication is required only on configurations reachable from the actual
initial configuration.  This is the same pattern as the `hReach10` repair:
global adversarial states are not asserted to satisfy the invariant.
-/
def PreToNoOvershootReachableResidual
    (init : Config (AgentState L K)) (n : ℕ) (seamP : Fin 10 → ℕ) : Prop :=
  ∀ (k : Fin 10) (c : Config (AgentState L K)),
    (NonuniformMajority L K).Reachable init c →
    SeamPre (L := L) (K := K) (seamP k) n c →
    SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c

/-- Projection form of the chain-restricted replacement. -/
theorem preToNoOvershoot_reachable
    {init : Config (AgentState L K)} {n : ℕ} {seamP : Fin 10 → ℕ}
    (h : PreToNoOvershootReachableResidual
      (L := L) (K := K) init n seamP) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (NonuniformMajority L K).Reachable init c →
      SeamPre (L := L) (K := K) (seamP k) n c →
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c :=
  h

/--
The bad seam-pre/no-overshoot set is contained in the non-reachable set, under the
chain-restricted residual.
-/
theorem preToNoOvershoot_bad_subset_not_reachable
    {init : Config (AgentState L K)} {n : ℕ} {seamP : Fin 10 → ℕ}
    (h : PreToNoOvershootReachableResidual
      (L := L) (K := K) init n seamP)
    (k : Fin 10) :
    {c : Config (AgentState L K) |
      SeamPre (L := L) (K := K) (seamP k) n c ∧
        ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c}
      ⊆
    {c : Config (AgentState L K) |
      ¬ (NonuniformMajority L K).Reachable init c} := by
  intro c hc hreach
  exact hc.2 (h k c hreach hc.1)

set_option maxHeartbeats 4000000 in
/--
Measure-level sufficiency of the chain-restricted replacement.

At every finite horizon from the actual initial configuration, the chain assigns
zero mass to seam-pre configurations that violate `NoOvershoot`.
-/
theorem preToNoOvershoot_bad_mass_eq_zero
    {init : Config (AgentState L K)} {n : ℕ} {seamP : Fin 10 → ℕ}
    (h : PreToNoOvershootReachableResidual
      (L := L) (K := K) init n seamP)
    (k : Fin 10) (T : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ T) init
      {c : Config (AgentState L K) |
        SeamPre (L := L) (K := K) (seamP k) n c ∧
          ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c}
      = 0 := by
  have hle :
      ((NonuniformMajority L K).transitionKernel ^ T) init
        {c : Config (AgentState L K) |
          SeamPre (L := L) (K := K) (seamP k) n c ∧
            ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c}
        ≤ 0 := by
    calc
      ((NonuniformMajority L K).transitionKernel ^ T) init
        {c : Config (AgentState L K) |
          SeamPre (L := L) (K := K) (seamP k) n c ∧
            ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c}
          ≤
        ((NonuniformMajority L K).transitionKernel ^ T) init
          {c : Config (AgentState L K) |
            ¬ (NonuniformMajority L K).Reachable init c} :=
          measure_mono
            (preToNoOvershoot_bad_subset_not_reachable
              (L := L) (K := K) h k)
      _ = 0 :=
          nonuniformTransitionKernel_pow_not_reachable_eq_zero L K init T
  exact le_antisymm hle bot_le

/--
A frequently useful corollary: the bad seam-pre/no-overshoot event has any
announced budget, because its chain mass is zero.
-/
theorem preToNoOvershoot_bad_mass_le
    {init : Config (AgentState L K)} {n : ℕ} {seamP : Fin 10 → ℕ}
    (h : PreToNoOvershootReachableResidual
      (L := L) (K := K) init n seamP)
    (k : Fin 10) (T : ℕ) (ε : ℝ≥0∞) :
    ((NonuniformMajority L K).transitionKernel ^ T) init
      {c : Config (AgentState L K) |
        SeamPre (L := L) (K := K) (seamP k) n c ∧
          ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c}
      ≤ ε := by
  rw [preToNoOvershoot_bad_mass_eq_zero (L := L) (K := K) h k T]
  exact bot_le

/--
If a legacy interface still demands the blanket field, this is the exact bridge
needed to recover it: every state satisfying the seam precondition must itself be
reachable.  The new chain-restricted route avoids needing this global bridge.
-/
theorem hPreToNoOvershoot_of_reachable_residual_and_all_pre_reachable
    {init : Config (AgentState L K)} {n : ℕ} {seamP : Fin 10 → ℕ}
    (h : PreToNoOvershootReachableResidual
      (L := L) (K := K) init n seamP)
    (hReachPre :
      ∀ (k : Fin 10) (c : Config (AgentState L K)),
        SeamPre (L := L) (K := K) (seamP k) n c →
        (NonuniformMajority L K).Reachable init c) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c := by
  intro k c hpre
  exact h k c (hReachPre k c hpre) hpre

/-! ## Axiom audit. -/

#print axioms overshot_config_counterexample
#print axioms blanket_hPreToNoOvershoot_refutable
#print axioms SeamEntry.seamPre
#print axioms SeamEntry.noOvershoot
#print axioms SeamEntry.notAtRiskClockZero
#print axioms preToNoOvershoot_reachable
#print axioms preToNoOvershoot_bad_subset_not_reachable
#print axioms preToNoOvershoot_bad_mass_eq_zero
#print axioms preToNoOvershoot_bad_mass_le
#print axioms hPreToNoOvershoot_of_reachable_residual_and_all_pre_reachable

end PreToNoOvershootDischarge
end ExactMajority

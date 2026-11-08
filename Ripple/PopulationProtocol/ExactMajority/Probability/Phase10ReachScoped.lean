import Ripple.PopulationProtocol.ExactMajority.Probability.Phase10SignResolved
import Ripple.PopulationProtocol.ExactMajority.Probability.NonuniformMarkovChain

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

namespace Phase10ReachScoped

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The empty configuration satisfies `Phase10Post` vacuously. -/
theorem phase10Post_empty :
    Phase10Drop.Phase10Post
      (L := L) (K := K) (0 : Config (AgentState L K)) := by
  refine ⟨Output.A, ?_⟩
  intro a ha
  exact False.elim ((Multiset.notMem_zero a) ha)

/--
A nonempty configuration cannot reach the empty configuration, because protocol
reachability preserves multiset cardinality.
-/
theorem not_reachable_empty_of_card_pos
    {c₀ : Config (AgentState L K)} (hpos : 0 < c₀.card) :
    ¬ (NonuniformMajority L K).Reachable
        c₀ (0 : Config (AgentState L K)) := by
  intro hreach
  have hcard :
      (0 : Config (AgentState L K)).card = c₀.card :=
    Protocol.reachable_card_eq
      (P := NonuniformMajority L K) hreach
  simp at hcard
  omega

/--
Therefore the blanket `hReach10` surface is false for every nonempty start:
`Phase10Post 0` holds, but `0` is not reachable from a nonempty `c₀`.
-/
theorem hReach10_blanket_false_of_card_pos
    (c₀ : Config (AgentState L K)) (hpos : 0 < c₀.card) :
    ¬ (∀ c,
        Phase10Drop.Phase10Post (L := L) (K := K) c →
          (NonuniformMajority L K).Reachable c₀ c) := by
  intro h
  exact
    not_reachable_empty_of_card_pos
      (L := L) (K := K) hpos
      (h (0 : Config (AgentState L K))
        (phase10Post_empty (L := L) (K := K)))

/--
The corrected scoped C11 sign surface: only reachable `Phase10Post` states need
to match the valid initial gap.
-/
def Phase10SignMatchOnReachable
    (init : Config (AgentState L K)) : Prop :=
  ∀ c,
    (NonuniformMajority L K).Reachable init c →
    Phase10Drop.Phase10Post (L := L) (K := K) c →
    phase10MajorityWitness (L := L) (K := K) init c

/--
Scoped phase-10 sign match from the landed `Phase10SignResolved` ingredients.

This is the non-overstrong replacement for the blanket
`AtomsV2.Phase10SignMatch init`.  The reachable hypothesis is supplied only for
the endpoint state under consideration.
-/
theorem phase10MajorityWitness_of_validInitial_reachable_post
    {init c : Config (AgentState L K)}
    (hinit : validInitial init)
    (hreachc : (NonuniformMajority L K).Reachable init c)
    (hPost : Phase10Drop.Phase10Post (L := L) (K := K) c) :
    phase10MajorityWitness (L := L) (K := K) init c := by
  rcases Phase10SignResolved.cardZero_or_active_of_post
      (L := L) (K := K) hinit hreachc hPost with hz | hact
  · subst hz
    exact Phase10SignResolved.witness_of_empty (L := L) (K := K) (init := init)
  · obtain ⟨o, ho⟩ := hPost
    have hphase : ∀ a ∈ c, a.phase.val = 10 :=
      fun a ha => (ho a ha).1
    have hcons :
        phase10ActiveSignedSum c =
          initialGap (L := L) (K := K) init :=
      phase10ActiveSignedSum_eq_initialGap_of_reachable
        (L := L) (K := K) init c hinit hreachc hphase
    exact
      SignMatch.witness_of_post_conservation
        (L := L) (K := K) ⟨o, ho⟩ hcons hact

/--
Packaged reachable-scoped sign match.
-/
theorem phase10SignMatch_onReachable_of_validInitial
    {init : Config (AgentState L K)}
    (hinit : validInitial init) :
    Phase10SignMatchOnReachable (L := L) (K := K) init := by
  intro c hreachc hPost
  exact
    phase10MajorityWitness_of_validInitial_reachable_post
      (L := L) (K := K) hinit hreachc hPost

/--
Generic support-scoped replacement for a pointwise final-post bridge.

If `Post → Stable` is known only on states reachable from `c₀`, then at any
finite time `t` the bad-stable mass is still bounded by the bad-post mass, because
the non-reachable region has kernel-power mass zero.
-/
theorem bad_stable_le_bad_post_of_reachable_support
    (c₀ : Config (AgentState L K)) (t : ℕ)
    (Post Stable : Config (AgentState L K) → Prop)
    (hStable :
      ∀ c,
        (NonuniformMajority L K).Reachable c₀ c →
        Post c →
        Stable c) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ Stable c}
      ≤
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ Post c} := by
  let Reach : Config (AgentState L K) → Prop :=
    fun c => (NonuniformMajority L K).Reachable c₀ c
  have hnull :
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ Reach c} = 0 := by
    simpa [Reach, nonuniformTransitionKernel] using
      (nonuniformTransitionKernel_pow_not_reachable_eq_zero
        (L := L) (K := K) c₀ t)
  have hcover :
      {c : Config (AgentState L K) | ¬ Stable c}
        ⊆
      {c : Config (AgentState L K) | ¬ Post c} ∪
      {c : Config (AgentState L K) | ¬ Reach c} := by
    intro c hcBad
    by_cases hR : Reach c
    · by_cases hP : Post c
      · exact False.elim (hcBad (hStable c hR hP))
      · exact Or.inl hP
    · exact Or.inr hR
  calc
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ Stable c}
      ≤
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        ({c : Config (AgentState L K) | ¬ Post c} ∪
         {c : Config (AgentState L K) | ¬ Reach c}) :=
      measure_mono hcover
    _ ≤
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) | ¬ Post c}
      +
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) | ¬ Reach c} :=
      measure_union_le _ _
    _ =
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) | ¬ Post c} := by
      rw [hnull, add_zero]

#print axioms phase10Post_empty
#print axioms not_reachable_empty_of_card_pos
#print axioms hReach10_blanket_false_of_card_pos
#print axioms phase10MajorityWitness_of_validInitial_reachable_post
#print axioms phase10SignMatch_onReachable_of_validInitial
#print axioms bad_stable_le_bad_post_of_reachable_support

end Phase10ReachScoped

end Ripple.PopulationProtocol.ExactMajority

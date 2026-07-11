import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CounterSurvivalConc

/-!
# `¬ WinN` failure-mode decomposition (a building block for `hcover`)

`survival_union_bound` / `clockCounter_survival` carry the trajectory cover
`hcover : {¬ WinN N n} ⊆ ⋃ j ∈ Clocks, {Depleted j}` as a hypothesis.  Every route
to that cover first splits `¬ WinN` into its three De-Morgan failure modes:

* `card ≠ n` — impossible on a trajectory from a `card = n` start (card is conserved
  by `stepDistOrSelf_support_card_eq`), so this mode is vacuous on the reachable set;
* `∃ a ∈ c, a.phase.val ≠ N` — a promoted agent (a clock that fired its counter-`0`
  guard), and
* `∃ a ∈ c, a.role = clock ∧ a.counter.val = 0` — a clock currently at counter `0`.

Both surviving modes are witnessed by a clock having reached counter `0` (directly, or
via the promotion that produced the off-phase agent), which is the depletion event the
union bound covers.
-/

namespace ExactMajority
namespace WinNFailDecomp

open scoped BigOperators

variable {L K : ℕ}

/-- **De-Morgan decomposition of a `WinN` failure.** -/
theorem not_winN_iff (N n : ℕ) (c : Config (AgentState L K)) :
    ¬ CounterSurvivalConc.WinN (L := L) (K := K) N n c ↔
      c.card ≠ n
      ∨ (∃ a ∈ c, a.phase.val ≠ N)
      ∨ (∃ a ∈ c, a.role = Role.clock ∧ a.counter.val = 0) := by
  classical
  unfold CounterSurvivalConc.WinN
  constructor
  · intro h
    by_cases hcard : c.card = n
    · by_cases hphase : ∀ a ∈ c, a.phase.val = N
      · -- card and phase hold, so the clock-positivity conjunct must fail
        right; right
        by_contra hcon
        push_neg at hcon
        exact h ⟨hcard, hphase, fun a ha hcl => by
          have := hcon a ha hcl
          omega⟩
      · push_neg at hphase
        obtain ⟨a, ha, hne⟩ := hphase
        exact Or.inr (Or.inl ⟨a, ha, hne⟩)
    · exact Or.inl hcard
  · rintro (hcard | ⟨a, ha, hne⟩ | ⟨a, ha, hcl, h0⟩) hwin
    · exact hcard hwin.1
    · exact hne (hwin.2.1 a ha)
    · have := hwin.2.2 a ha hcl
      omega

/-- On a `card = n` config the card mode is excluded, so a `WinN` failure is a clock
at counter `0` or an off-phase agent.  (Card is conserved along the chain, so this is
the form the trajectory cover uses.) -/
theorem not_winN_of_card_eq (N n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n)
    (h : ¬ CounterSurvivalConc.WinN (L := L) (K := K) N n c) :
    (∃ a ∈ c, a.phase.val ≠ N)
      ∨ (∃ a ∈ c, a.role = Role.clock ∧ a.counter.val = 0) := by
  rcases (not_winN_iff N n c).mp h with hbad | hphase | hclock
  · exact absurd hcard hbad
  · exact Or.inl hphase
  · exact Or.inr hclock

end WinNFailDecomp
end ExactMajority

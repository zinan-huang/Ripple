/-
Main theorem of Doty et al. (Theorem 3.1).

  There is a nonuniform population protocol Nonuniform Majority, using O(log n)
  states, that stably computes majority in O(log n) stabilization time, both in
  expectation and with high probability.

This file formalizes the finite state-space bounds.  The stable-computation
and stochastic stabilization-time parts of Theorem 3.1 are recorded below only
as target propositions until the phase analysis is connected to the protocol
Markov-chain semantics.

Reference: Doty et al., §3 and §§5–7.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition
import Mathlib.Tactic

namespace ExactMajority

private lemma card_opinion : Fintype.card Opinion = 2 := by decide
private lemma card_output : Fintype.card Output = 3 := by decide
private lemma card_role : Fintype.card Role = 5 := by decide
private lemma card_sign : Fintype.card Sign = 2 := by decide

/-- Cardinality of the dyadic-bias type. -/
lemma card_bias_eq (L : ℕ) : Fintype.card (Bias L) = 2 * L + 3 := by
  have h₁ : Fintype.card (Bias L) =
      Fintype.card (Option (Sign × Fin (L + 1))) := by
    apply Fintype.card_congr
    exact
      { toFun := Bias.toOption
        invFun := Bias.ofOption
        left_inv := Bias.ofOption_toOption
        right_inv := Bias.toOption_ofOption }
  rw [h₁, Fintype.card_option, Fintype.card_prod, Fintype.card_fin, card_sign]
  ring

/-- Exact cardinality of `AgentState L K`, derived from the product equiv used
to define its `Fintype` instance.

  |Opinion| · |Output| · |Phase| · |Role| · |Bool(assigned)| · |Bias L| ·
  |Fin 7| · |Fin (L+1)| · |Fin (K(L+1)+1)| · |Bool(full)| · |Fin 8| ·
  |Fin (50(L+1)+1)|
  =  2 · 3 · 11 · 5 · 2 · (2L+3) · 7 · (L+1) · (K(L+1)+1) · 2 · 8 ·
     (50(L+1)+1). -/
theorem state_count_eq (L K : ℕ) :
    Fintype.card (AgentState L K) =
      2 * 3 * 11 * 5 * 2 * (2 * L + 3) * 7 * (L + 1) *
        (K * (L + 1) + 1) * 2 * 8 * (50 * (L + 1) + 1) := by
  have hcong : Fintype.card (AgentState L K) =
      Fintype.card (AgentTuple L K) := by
    apply Fintype.card_congr
    exact
      { toFun := AgentState.toTuple
        invFun := AgentState.ofTuple
        left_inv := AgentState.ofTuple_toTuple
        right_inv := AgentState.toTuple_ofTuple }
  rw [hcong]
  simp only [AgentTuple, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    card_opinion, card_output, card_role, card_bias_eq,
    show Fintype.card Phase = 11 from rfl]
  ring

/-- State complexity is polynomial in `L = ⌈log₂ n⌉`: |Λ| ≤ C · (L+1)^4 with
`K` fixed. The flat-record encoding gives O((log n)^4); the paper's Θ(log n)
requires a phase-indexed sigma type (future refinement). -/
theorem state_count_poly_bound (L K : ℕ) (hL : 1 ≤ L) (_hK : 1 ≤ K) :
    Fintype.card (AgentState L K) ≤
      2 * 3 * 11 * 5 * 2 * 7 * 2 * 8 * 3 * (K + 1) * 51 * (L + 1) ^ 4 := by
  rw [state_count_eq L K]
  have h1 : 2 * L + 3 ≤ 3 * (L + 1) := by omega
  have h2 : K * (L + 1) + 1 ≤ (K + 1) * (L + 1) := by
    have : 1 ≤ L + 1 := by omega
    nlinarith
  have h3 : 50 * (L + 1) + 1 ≤ 51 * (L + 1) := by
    have : 1 ≤ L + 1 := by omega
    nlinarith
  have key :
      2 * 3 * 11 * 5 * 2 * (2 * L + 3) * 7 * (L + 1) * (K * (L + 1) + 1) * 2 *
        8 * (50 * (L + 1) + 1)
        ≤ 2 * 3 * 11 * 5 * 2 * (3 * (L + 1)) * 7 * (L + 1) *
          ((K + 1) * (L + 1)) * 2 * 8 * (51 * (L + 1)) := by
    gcongr
  calc
    _ ≤ 2 * 3 * 11 * 5 * 2 * (3 * (L + 1)) * 7 * (L + 1) *
          ((K + 1) * (L + 1)) * 2 * 8 * (51 * (L + 1)) := key
    _ = 2 * 3 * 11 * 5 * 2 * 7 * 2 * 8 * 3 * (K + 1) * 51 * (L + 1) ^ 4 := by ring

/-- Output partition for the Doty exact-majority protocol: an agent
outputs `A`/`B`/`T` based on its `output` field. -/
def doutPartition (L K : ℕ) : OutputPartition (AgentState L K) where
  isA a := match a.output with | .A => true | _ => false
  isB a := match a.output with | .B => true | _ => false
  isT a := match a.output with | .T => true | _ => false
  partition a := by cases a.output <;> decide

/-- Validity predicate for an initial configuration: every agent is in
phase 0, role MCR, with `assigned = false`, neutral opinion bits, and the
smallBias initialized from the input opinion (A → +1 = Fin 4, B → −1 = Fin 2). -/
def validInitial {L K : ℕ} (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, (a.phase = ⟨0, by decide⟩) ∧ (a.role = .mcr) ∧
    (a.assigned = false) ∧
    (a.opinions = (⟨0, by decide⟩ : Fin 8)) ∧
    (a.input = .A → a.smallBias = ⟨4, by decide⟩) ∧
    (a.input = .B → a.smallBias = ⟨2, by decide⟩)

/-- Majority "verdict" function on an initial valid configuration: counts
`input = A` vs `input = B` and returns the OutputPartition output triple
(true, false, false) for A, (false, true, false) for B, (false, false, true)
for tie. -/
def majorityVerdict {L K : ℕ} (c : Config (AgentState L K)) : Bool × Bool × Bool :=
  let nA := (c.filter (fun a => a.input = .A)).card
  let nB := (c.filter (fun a => a.input = .B)).card
  if nA > nB then (true, false, false)
  else if nA < nB then (false, true, false)
  else (false, false, true)

/- **Stable correctness** (Doty Theorem 3.1, correctness part).
The theorem `stable_majority_correct` is proved in `DeterministicChain.lean`
using `stable_majority_correct_of_majorityStableEndpoint_reachability`. -/

/- **Time complexity (Doty Theorem 3.1, time part).** Expected stabilization
time, measured as parallel time = (# interactions) / n, is O(log n) on every
valid initial configuration.

The "expected" wrapper requires a probability space over interaction
schedules. We state it abstractly as: there exists a constant `C` and a
schedule-time random variable `S` whose expectation is bounded by
`C · (L + 1)`.

TODO: full proof depends on the §4 probability framework + §§5–7 phase
durations. The constant `C` is implicit and depends on the `cᵢ` constants
in each phase.

No Lean theorem is exported here yet: the current development does not have a
typed random schedule and stopping-time API for this protocol. -/

/- **Main theorem goal (Doty et al. Theorem 3.1).** Combination of state count,
stable correctness, and O(log n) time.

  There is a (nonuniform) population protocol Nonuniform Majority on
  `AgentState L K`, of cardinality `Fintype.card (AgentState L K) ≤
  C₁ (K + 1) (L + 1)^4`, that stably computes majority on every valid
  initial configuration in expected stabilization time `O(L)`.

The `O((L + 1)^4)` state bound is the looser bound we get from a flat
record; the paper's Θ(L) bound requires per-phase state-space narrowing
(future refinement).

No combined theorem is exported until both correctness and stochastic time are
proved from the protocol dynamics. -/

end ExactMajority

/-
Agent state for the Doty et al. exact majority protocol.

An agent's full state is a record of fields, only some of which are active in
each phase. The state space size is Θ(log n) because the dominant fields
(`exponent`, `hour`, `minute`, `counter`) range over O(log n) values.

Fields (Doty et al. §3.4):
  input    : initial opinion {A, B}, read-only
  output   : reported output {A, B, T}
  phase    : current phase 0..10
  role     : Main / Reserve / Clock / MCR / CR
  assigned : Phase 0's per-agent quota flag — toggled True after the agent
             has executed its one allowed assignment action (lines 5/8 of
             Phase 0 pseudocode). Independent of role.
  bias     : dyadic in {0, ±1, ±1/2, ..., ±1/2^L} (Phases 3+)
  smallBias: small-integer bias in {−3, ..., +3} (Phases 0–1), Fin 7 encoded
  hour     : Main agent's hour, in {0, ..., L} (Phase 3)
  minute   : Clock agent's minute, in {0, ..., L'} where L' = k·L (Phase 3)
  full     : Phase 8's "consumed" flag. Reused in Phase 10 as `active`
             (the two phases never coexist; rename via `AgentState.active`
             accessor below).
  opinions : subset of {−1, 0, +1} seen so far, used in Phases 2 and 9.
             Encoded as `Fin 8` interpreting the bit pattern (b_{−1}, b_0, b_{+1}).
  counter  : countdown in timed phases

For scaffolding we use a single record with all fields. A future refinement
could split the state space per phase to keep |Λ| = Θ(log n) sharp; as
written here it is O(L^4) ⋅ K = O((log n)^4 · k).

Reference: Doty et al., §3.4.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Basic.Role
import Ripple.PopulationProtocol.Majority.ExactMajority.Basic.Bias

namespace ExactMajority

/-- Initial opinion. -/
inductive Opinion | A | B
  deriving DecidableEq, Repr

instance : Fintype Opinion where
  elems := {.A, .B}
  complete o := by cases o <;> simp

/-- Reported output. -/
inductive Output | A | B | T
  deriving DecidableEq, Repr

instance : Fintype Output where
  elems := {.A, .B, .T}
  complete o := by cases o <;> simp

/-- Phase index, 0..10. -/
abbrev Phase := Fin 11

/-- Full agent state. `L` is `⌈log₂ n⌉`; `K` is the minutes-per-hour constant
from the fixed-resolution clock (paper uses k = 45 for the proof, k = 2 in
simulations). -/
structure AgentState (L K : ℕ) where
  input : Opinion
  output : Output
  phase : Phase
  role : Role
  /-- Phase-0 per-agent assignment quota flag (lines 5/8 of pseudocode):
  set to `true` once the agent has executed its one allowed assignment
  reaction. Independent of `role`. -/
  assigned : Bool
  /-- Bias as dyadic sign × exponent, valid for Phases 3+. -/
  bias     : Bias L
  /-- Small-integer bias used in Phases 0–1: range −3..+3. -/
  smallBias : Fin 7
  /-- Hour for Main agents in Phase 3 onward. -/
  hour     : Fin (L + 1)
  /-- Minute for Clock agents in Phase 3 onward. -/
  minute   : Fin (K * (L + 1) + 1)
  /-- Phase 8 "consumed" flag, also used as Phase 10's `active`. The two
  phases never coexist, so a single Bool is sufficient. Use the
  `AgentState.active` accessor for Phase-10 reads. -/
  full     : Bool
  /-- Subset of opinion signs `{−1, 0, +1}` accumulated by epidemic union in
  Phases 2 and 9. Encoded as `Fin 8` via the bit pattern (b_{−1}, b_0, b_{+1});
  e.g. `1` = {−1}, `4` = {+1}, `5` = {−1, +1}. -/
  opinions : Fin 8
  /-- Generic counter for timed phases. -/
  counter  : Fin (50 * (L + 1) + 1)
  deriving DecidableEq, Repr

/-- The product type used as the canonical equiv target for `AgentState`. -/
abbrev AgentTuple (L K : ℕ) :=
  Opinion × Output × Phase × Role × Bool × Bias L × Fin 7 ×
    Fin (L + 1) × Fin (K * (L + 1) + 1) × Bool × Fin 8 ×
    Fin (50 * (L + 1) + 1)

/-- AgentState as a (long) iterated product, used to derive Fintype. -/
def AgentState.toTuple {L K : ℕ} (a : AgentState L K) : AgentTuple L K :=
  (a.input, a.output, a.phase, a.role, a.assigned, a.bias, a.smallBias,
    a.hour, a.minute, a.full, a.opinions, a.counter)

def AgentState.ofTuple {L K : ℕ} (t : AgentTuple L K) : AgentState L K :=
  { input := t.1, output := t.2.1, phase := t.2.2.1, role := t.2.2.2.1,
    assigned := t.2.2.2.2.1,
    bias := t.2.2.2.2.2.1, smallBias := t.2.2.2.2.2.2.1,
    hour := t.2.2.2.2.2.2.2.1, minute := t.2.2.2.2.2.2.2.2.1,
    full := t.2.2.2.2.2.2.2.2.2.1,
    opinions := t.2.2.2.2.2.2.2.2.2.2.1,
    counter := t.2.2.2.2.2.2.2.2.2.2.2 }

@[simp] lemma AgentState.ofTuple_toTuple {L K : ℕ} (a : AgentState L K) :
    AgentState.ofTuple (AgentState.toTuple a) = a := by
  cases a; rfl

@[simp] lemma AgentState.toTuple_ofTuple {L K : ℕ} (t : AgentTuple L K) :
    AgentState.toTuple (AgentState.ofTuple (L := L) (K := K) t) = t := by
  rcases t with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩; rfl

instance (L K : ℕ) : Fintype (AgentState L K) :=
  Fintype.ofEquiv _
    { toFun := AgentState.ofTuple (L := L) (K := K)
      invFun := AgentState.toTuple
      left_inv := AgentState.toTuple_ofTuple
      right_inv := AgentState.ofTuple_toTuple }

/-- "Assigned externally"-style predicate combining role and the explicit
`assigned` flag: useful for cleanup phases that read the assignment bit
indirectly via role. -/
def AgentState.roleAssigned {L K : ℕ} (a : AgentState L K) : Bool :=
  match a.role with
  | .main | .reserve | .clock => true
  | .mcr | .cr => false

/-- Phase-10 "active" flag, an alias for `full`. The two phases never coexist
so a single boolean carries both meanings without conflict. -/
def AgentState.active {L K : ℕ} (a : AgentState L K) : Bool := a.full

/-- Phase-5/6 "sample" field: the exponent a Reserve agent sampled from the
first biased Main agent it met in Phase 5. Reuses `hour` (Reserve agents do
not participate in Phase 3 hour semantics). -/
def AgentState.sample {L K : ℕ} (a : AgentState L K) : Fin (L + 1) := a.hour

/-- Sentinel value meaning "not yet sampled" for a Reserve agent's `sample`.
We use the maximum `Fin (L + 1)` value (`L`), which Phase-3 Main agents never
reach as an hour value in practice. -/
def sampleUnset {L : ℕ} : Fin (L + 1) := ⟨L, by omega⟩

end ExactMajority

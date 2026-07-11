/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Agent State for Protocol P_EM

Each agent in P_EM has:
  - input ∈ {A, B}  (read-only)
  - Variables from Optimal-Silent-SSR (ranking protocol):
    · role ∈ {Resetting, Settled, Unsettled}
    · rank ∈ [1, n]
    · leader ∈ {L, F}
    · resetcount ∈ [0, R_max]   where R_max = 60 log n
  - answer ∈ {φ, T, A, B}   (φ = undecided)
  - timer ∈ [0, 7(t_rank + 4)]  where t_rank ≤ t_rank · n, t_rank = O(1)
-/

import Ripple.PopulationProtocol.Majority.SSEM.Defs.Protocol

namespace SSEM

/-- The role of an agent in the ranking subprotocol. -/
inductive Role
  | Resetting
  | Settled
  | Unsettled
  deriving DecidableEq, Repr

/-- The leader status. -/
inductive Leader
  | L   -- leader
  | F   -- follower
  deriving DecidableEq, Repr

/-- The answer variable: φ (undecided), or an output opinion. -/
inductive Answer
  | phi     -- φ, undecided
  | outT    -- T (tie)
  | outA    -- A
  | outB    -- B
  deriving DecidableEq, Repr

namespace Answer

def toOutput : Answer → Output
  | .phi  => .T
  | .outT => .T
  | .outA => .A
  | .outB => .B

end Answer

/-- The full state of an agent in P_EM, parametric in n.
Includes fields from Optimal-Silent-SSR (Burman et al. PODC 2021):
  * `children` — number of children recruited in the binary-tree ranking (0, 1, or 2)
  * `errorcount` — error counter for Unsettled agents (triggers reset when 0)
  * `delaytimer` — delay timer for Resetting agents (ensures dormancy before wake) -/
structure AgentState (n : ℕ) where
  role : Role
  rank : Fin n
  leader : Leader
  resetcount : ℕ
  answer : Answer
  timer : ℕ
  children : ℕ := 0
  errorcount : ℕ := 0
  delaytimer : ℕ := 0
  deriving DecidableEq, Repr

@[simp] theorem AgentState.role_with_answer (s : AgentState n) (a : Answer) :
    ({ s with answer := a } : AgentState n).role = s.role := rfl
@[simp] theorem AgentState.role_with_timer (s : AgentState n) (t : ℕ) :
    ({ s with timer := t } : AgentState n).role = s.role := rfl
@[simp] theorem AgentState.errorcount_with_answer (s : AgentState n) (a : Answer) :
    ({ s with answer := a } : AgentState n).errorcount = s.errorcount := rfl
@[simp] theorem AgentState.errorcount_with_timer (s : AgentState n) (t : ℕ) :
    ({ s with timer := t } : AgentState n).errorcount = s.errorcount := rfl

-- Field projections through { s with answer := a }
@[simp] theorem AgentState.rank_with_answer (s : AgentState n) (a : Answer) :
    ({ s with answer := a } : AgentState n).rank = s.rank := rfl
@[simp] theorem AgentState.timer_with_answer (s : AgentState n) (a : Answer) :
    ({ s with answer := a } : AgentState n).timer = s.timer := rfl
@[simp] theorem AgentState.leader_with_answer (s : AgentState n) (a : Answer) :
    ({ s with answer := a } : AgentState n).leader = s.leader := rfl
@[simp] theorem AgentState.resetcount_with_answer (s : AgentState n) (a : Answer) :
    ({ s with answer := a } : AgentState n).resetcount = s.resetcount := rfl
@[simp] theorem AgentState.answer_with_answer (s : AgentState n) (a : Answer) :
    ({ s with answer := a } : AgentState n).answer = a := rfl
@[simp] theorem AgentState.children_with_answer (s : AgentState n) (a : Answer) :
    ({ s with answer := a } : AgentState n).children = s.children := rfl
@[simp] theorem AgentState.delaytimer_with_answer (s : AgentState n) (a : Answer) :
    ({ s with answer := a } : AgentState n).delaytimer = s.delaytimer := rfl

-- Field projections through { s with timer := t }
@[simp] theorem AgentState.rank_with_timer (s : AgentState n) (t : ℕ) :
    ({ s with timer := t } : AgentState n).rank = s.rank := rfl
@[simp] theorem AgentState.answer_with_timer (s : AgentState n) (t : ℕ) :
    ({ s with timer := t } : AgentState n).answer = s.answer := rfl
@[simp] theorem AgentState.leader_with_timer (s : AgentState n) (t : ℕ) :
    ({ s with timer := t } : AgentState n).leader = s.leader := rfl
@[simp] theorem AgentState.resetcount_with_timer (s : AgentState n) (t : ℕ) :
    ({ s with timer := t } : AgentState n).resetcount = s.resetcount := rfl
@[simp] theorem AgentState.timer_with_timer (s : AgentState n) (t : ℕ) :
    ({ s with timer := t } : AgentState n).timer = t := rfl

/-- The output function: if answer = φ, output T; otherwise output answer. -/
def agentOutput (s : AgentState n) : Output :=
  s.answer.toOutput

end SSEM

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Correctness Properties for P_EM

Structural lemmas for the protocol P_EM (Algorithm 1 of Kanaya et al. 2025).
The full convergence proof (Theorem 4) additionally requires convergence
of the ranking subprotocol (Optimal-Silent-SSR, Burman et al. PODC 2021),
which is parameterized here, not axiomatized.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Protocol.Transition
import Ripple.PopulationProtocol.Majority.SSEM.Defs.Execution

namespace SSEM

/-! ### Fintype instances for protocol components -/

instance : Fintype Role where
  elems := {.Resetting, .Settled, .Unsettled}
  complete s := by cases s <;> simp

instance : Fintype Leader where
  elems := {.L, .F}
  complete s := by cases s <;> simp

instance : Fintype Answer where
  elems := {.phi, .outT, .outA, .outB}
  complete s := by cases s <;> simp

/-! ### opinionToAnswer properties -/

@[simp] theorem opinionToAnswer_A : opinionToAnswer .A = .outA := rfl
@[simp] theorem opinionToAnswer_B : opinionToAnswer .B = .outB := rfl

theorem opinionToAnswer_injective : Function.Injective opinionToAnswer := by
  intro a b h; cases a <;> cases b <;> simp_all [opinionToAnswer]

theorem output_opinion_roundtrip (x : Opinion) :
    (opinionToAnswer x).toOutput = match x with | .A => Output.A | .B => Output.B := by
  cases x <;> rfl

/-! ### ceilHalf arithmetic -/

@[simp] theorem ceilHalf_zero : ceilHalf 0 = 0 := rfl
@[simp] theorem ceilHalf_one : ceilHalf 1 = 1 := rfl

theorem ceilHalf_even (k : ℕ) : ceilHalf (2 * k) = k := by
  unfold ceilHalf; omega

theorem ceilHalf_odd (k : ℕ) : ceilHalf (2 * k + 1) = k + 1 := by
  unfold ceilHalf; omega

theorem ceilHalf_le (n : ℕ) : ceilHalf n ≤ n := by
  unfold ceilHalf; omega

theorem ceilHalf_pos {n : ℕ} (hn : n > 0) : ceilHalf n > 0 := by
  unfold ceilHalf; omega

/-! ### Output function properties -/

theorem outputPEM_eq_answer_toOutput {n : ℕ} (s : AgentState n) (x : Opinion) :
    outputPEM n (s, x) = s.answer.toOutput := rfl

theorem allOutput_of_all_answer {n : ℕ} {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {C : Config (AgentState n) Opinion n} {a : Answer}
    (h : ∀ v : Fin n, (C v).1.answer = a) :
    C.allOutput (protocolPEM n trank Rmax rankDelta) a.toOutput := by
  intro v
  change (protocolPEM n trank Rmax rankDelta).π_out (C v) = a.toOutput
  change (C v).1.answer.toOutput = a.toOutput
  exact congr_arg Answer.toOutput (h v)

/-! ### Ranking convergence assumptions

The protocol P_EM is correct assuming a ranking subprotocol that
eventually assigns unique ranks 0..n−1 to all agents in Settled role.
This is provided by Optimal-Silent-SSR (Burman et al. PODC 2021).

We parameterize `transitionPEM` and `protocolPEM` by `rankDelta`
rather than axiomatizing its properties, so the encoding is
axiom-free.  The full convergence proof (Theorem 4 of Kanaya et al.)
additionally requires:

1. rankDelta eventually stabilizes all agents to role = Settled
   with pairwise distinct ranks in Fin n.
2. After ranking stabilizes, swapping orders A-agents below B-agents.
3. The median agent(s) then decide the majority opinion.
4. Propagation spreads the decision; disagreement triggers reset.

The interaction of these four phases is inherently sequential and
requires an intricate scheduler construction; a full formal proof
is future work (the paper proof is ≈3 pages of case analysis).
-/

end SSEM

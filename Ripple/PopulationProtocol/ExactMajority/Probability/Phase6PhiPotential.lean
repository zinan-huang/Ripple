/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase6PhiPotential — Doty Lemma 7.2's actual Phase-6 potential.

Doty et al. Lemma 7.2 does **not** use the dyadic high-mass potential
`Phase6Convergence.highMass l` (weight `2^(l-i)`), whose interior split is
conserved.  It uses the stronger potential

  `phi(> -l) = sum_{biased exponent -i > -l} 4^(l-1-i)`.

For an applicable Reserve split of a high Main at index `j < l`, both outputs
move to index `j+1`.  If `j+1 < l`, the pair weight changes

  `4^(l-1-j) -> 2 * 4^(l-1-(j+1)) = (1/2) * 4^(l-1-j)`;

if `j+1 = l`, the output leaves the high band and the weight drops to `0`.
This file pins that arithmetic against the actual `doSplit` rule.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6Convergence

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6PhiPotential

open scoped BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- Doty's Phase-6 Lemma 7.2 weight for a single bias:
`4^(l-1-i)` for a dyadic Main at index `i < l`, and `0` otherwise. -/
def biasPhiW (l : ℕ) (b : Bias L) : ℕ :=
  match b with
  | .zero => 0
  | .dyadic _ i => if i.val < l then 4 ^ (l - 1 - i.val) else 0

/-- Doty's Phase-6 potential contribution of one agent.  Only Main agents count. -/
def agentPhiW (l : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = Role.main then biasPhiW (L := L) l a.bias else 0

/-- Doty's Phase-6 Lemma 7.2 potential `phi(> -l)`. -/
def phiMass (l : ℕ) (c : Config (AgentState L K)) : ℕ :=
  (c.map (fun a => agentPhiW (L := L) (K := K) l a)).sum

/-- A high agent has positive Doty-`phi` weight. -/
theorem agentPhiW_pos_of_high (l : ℕ) (a : AgentState L K)
    (h : Phase6Convergence.highSt (L := L) (K := K) l a) :
    1 ≤ agentPhiW (L := L) (K := K) l a := by
  obtain ⟨hr, σ, i, hb, hi⟩ := h
  unfold agentPhiW
  rw [if_pos hr, hb]
  simp only [biasPhiW, if_pos hi]
  exact Nat.one_le_pow (l - 1 - i.val) 4 (by norm_num)

/-- Non-high agents have zero Doty-`phi` weight. -/
theorem agentPhiW_eq_zero_of_not_high (l : ℕ) (a : AgentState L K)
    (h : ¬ Phase6Convergence.highSt (L := L) (K := K) l a) :
    agentPhiW (L := L) (K := K) l a = 0 := by
  unfold agentPhiW
  by_cases hr : a.role = Role.main
  · rw [if_pos hr]
    cases hb : a.bias with
    | zero => rfl
    | dyadic σ i =>
        by_cases hi : i.val < l
        · exact absurd
            (Phase6Convergence.highSt_of (L := L) (K := K) l a σ i hr hb hi) h
        · simp only [biasPhiW, if_neg hi]
  · rw [if_neg hr]

/-- `phiMass l c = 0` iff no high biased Main remains.  Thus it has the same
zero-set as `Phase6Convergence.highMass l`, but a different drift behavior. -/
theorem phiMass_eq_zero_iff (l : ℕ) (c : Config (AgentState L K)) :
    phiMass (L := L) (K := K) l c = 0 ↔
      ∀ a ∈ c, ¬ Phase6Convergence.highSt (L := L) (K := K) l a := by
  unfold phiMass
  rw [Multiset.sum_eq_zero_iff]
  constructor
  · intro h a ha hhigh
    have hz := h (agentPhiW (L := L) (K := K) l a) (Multiset.mem_map_of_mem _ ha)
    have hpos := agentPhiW_pos_of_high (L := L) (K := K) l a hhigh
    omega
  · intro h x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact agentPhiW_eq_zero_of_not_high (L := L) (K := K) l a (h a ha)

/-- A Reserve contributes zero Doty-`phi` weight. -/
theorem agentPhiW_reserve (l : ℕ) (r : AgentState L K) (hr : r.role = Role.reserve) :
    agentPhiW (L := L) (K := K) l r = 0 := by
  unfold agentPhiW
  rw [if_neg (by rw [hr]; decide)]

/-- The arithmetic core of Doty Lemma 7.2: an applicable Phase-6 Reserve split of
a high Main reduces the two-agent `phi` mass by at least a factor `2`.

The statement is multiplicative in natural-number form:
`2 * after ≤ before`.  For interior splits this is equality; at the band top the
right side is positive and the left side is `0`. -/
theorem doSplit_phi_pair_half (l : ℕ) (r m : AgentState L K) {σ : Sign}
    {j : Fin (L + 1)}
    (hrR : r.role = Role.reserve) (hmM : m.role = Role.main)
    (hb : m.bias = Bias.dyadic σ j) (hjlt : j.val < l)
    (hne : r.hour.val ≠ L) (hgt : r.hour.val > j.val) (hlt : j.val < L) :
    2 * (agentPhiW (L := L) (K := K) l (doSplit L K r m).1
        + agentPhiW (L := L) (K := K) l (doSplit L K r m).2)
      ≤ agentPhiW (L := L) (K := K) l r + agentPhiW (L := L) (K := K) l m := by
  rw [Phase6Convergence.doSplit_apply (L := L) (K := K) r m hb hne hgt hlt]
  rw [agentPhiW_reserve (L := L) (K := K) l r hrR, zero_add]
  have hout1 :
      agentPhiW (L := L) (K := K) l
          ({ r with role := Role.main, bias := Bias.dyadic σ ⟨j.val + 1, by omega⟩ }) =
        biasPhiW (L := L) l (Bias.dyadic σ ⟨j.val + 1, by omega⟩ : Bias L) := by
    unfold agentPhiW
    rw [if_pos rfl]
  have hout2 :
      agentPhiW (L := L) (K := K) l
          ({ m with bias := Bias.dyadic σ ⟨j.val + 1, by omega⟩ }) =
        biasPhiW (L := L) l (Bias.dyadic σ ⟨j.val + 1, by omega⟩ : Bias L) := by
    unfold agentPhiW
    rw [if_pos (by simp [hmM])]
  have hin :
      agentPhiW (L := L) (K := K) l m =
        4 ^ (l - 1 - j.val) := by
    unfold agentPhiW
    rw [if_pos hmM, hb]
    simp only [biasPhiW, if_pos hjlt]
  rw [hout1, hout2, hin]
  simp only [biasPhiW]
  by_cases hjnext : j.val + 1 < l
  · rw [if_pos (by simpa using hjnext)]
    have hstep : l - 1 - j.val = (l - 1 - (j.val + 1)) + 1 := by omega
    rw [hstep, pow_succ]
    ring_nf
    exact le_rfl
  · rw [if_neg (by simpa using hjnext)]
    positivity

#print axioms agentPhiW_pos_of_high
#print axioms phiMass_eq_zero_iff
#print axioms doSplit_phi_pair_half

end Phase6PhiPotential
end Ripple.PopulationProtocol.ExactMajority

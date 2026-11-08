/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase6PhiDrift

Doty's base-4 Phase-6 potential drift surface.

This file starts from the landed arithmetic in `Phase6PhiPotential`: an applicable
Reserve split of a high Main cuts the two-agent `phi` mass by a factor at least
two.  We lift the arithmetic to the actual phase-6 transition and package the
generic weighted-drop-sum bridge needed for the kernel multiplicative drift.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiPotential
import Ripple.PopulationProtocol.ExactMajority.Probability.WeightedDriftDropSum
import Ripple.PopulationProtocol.ExactMajority.Probability.Supermartingale

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6PhiDrift

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Pair-level and config-level monotonicity. -/

/-- The trailing phase-6 clock branch preserves Doty's `phi` weight. -/
theorem clockBranch_agentPhiW_eq (l : ℕ) (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    Phase6PhiPotential.agentPhiW (L := L) (K := K) l
        (if a.role = Role.clock then stdCounterSubroutine L K a else a)
      = Phase6PhiPotential.agentPhiW (L := L) (K := K) l a := by
  by_cases hc : a.role = Role.clock
  · rw [if_pos hc]
    unfold Phase6PhiPotential.agentPhiW
    rw [Phase6Convergence.stdCounterSubroutine_role_ge_five6 (L := L) (K := K) a ha,
        Phase6Convergence.stdCounterSubroutine_bias_ge_five (L := L) (K := K) a ha]
  · rw [if_neg hc]

/-- A Reserve-fuelled split is non-increasing for the base-4 `phi` pair mass. -/
theorem doSplit_phi_pair_le (l : ℕ) (r m : AgentState L K)
    (hrR : r.role = Role.reserve) (hmM : m.role = Role.main) :
    Phase6PhiPotential.agentPhiW (L := L) (K := K) l (doSplit L K r m).1
        + Phase6PhiPotential.agentPhiW (L := L) (K := K) l (doSplit L K r m).2
      ≤ Phase6PhiPotential.agentPhiW (L := L) (K := K) l r
          + Phase6PhiPotential.agentPhiW (L := L) (K := K) l m := by
  by_cases happ : Phase6Convergence.DoSplitApplicable (L := L) (K := K) r m
  · obtain ⟨σ, j, hb, hne, hgt, hlt⟩ := happ
    by_cases hjlt : j.val < l
    · have hhalf := Phase6PhiPotential.doSplit_phi_pair_half (L := L) (K := K)
        l r m hrR hmM hb hjlt hne hgt hlt
      have hle :
          Phase6PhiPotential.agentPhiW (L := L) (K := K) l (doSplit L K r m).1
              + Phase6PhiPotential.agentPhiW (L := L) (K := K) l (doSplit L K r m).2
            ≤
          2 * (Phase6PhiPotential.agentPhiW (L := L) (K := K) l (doSplit L K r m).1
              + Phase6PhiPotential.agentPhiW (L := L) (K := K) l (doSplit L K r m).2) := by
        omega
      exact le_trans hle hhalf
    · rw [Phase6Convergence.doSplit_apply (L := L) (K := K) r m hb hne hgt hlt]
      rw [Phase6PhiPotential.agentPhiW_reserve (L := L) (K := K) l r hrR]
      have hin :
          Phase6PhiPotential.agentPhiW (L := L) (K := K) l m = 0 := by
        unfold Phase6PhiPotential.agentPhiW
        rw [if_pos hmM, hb]
        simp only [Phase6PhiPotential.biasPhiW, if_neg hjlt]
      have hout1 :
          Phase6PhiPotential.agentPhiW (L := L) (K := K) l
              ({ r with role := Role.main, bias := Bias.dyadic σ ⟨j.val + 1, by omega⟩ } :
                AgentState L K) = 0 := by
        unfold Phase6PhiPotential.agentPhiW
        rw [if_pos rfl]
        have hjnext : ¬ (⟨j.val + 1, by omega⟩ : Fin (L + 1)).val < l := by
          change ¬ j.val + 1 < l
          omega
        simp only [Phase6PhiPotential.biasPhiW, if_neg hjnext]
      have hout2 :
          Phase6PhiPotential.agentPhiW (L := L) (K := K) l
              ({ m with bias := Bias.dyadic σ ⟨j.val + 1, by omega⟩ } :
                AgentState L K) = 0 := by
        unfold Phase6PhiPotential.agentPhiW
        rw [if_pos (by simp [hmM])]
        have hjnext : ¬ (⟨j.val + 1, by omega⟩ : Fin (L + 1)).val < l := by
          change ¬ j.val + 1 < l
          omega
        simp only [Phase6PhiPotential.biasPhiW, if_neg hjnext]
      rw [hout1, hout2, hin]
  · rw [Phase6Convergence.doSplit_eq_self_of_not_applicable (L := L) (K := K) r m happ]

/-- The pair `phi` mass of `{x,y}` is the sum of the two weights. -/
theorem phiMass_pair (l : ℕ) (x y : AgentState L K) :
    ((({x, y} : Multiset (AgentState L K))).map
        (fun a => Phase6PhiPotential.agentPhiW (L := L) (K := K) l a)).sum
      = Phase6PhiPotential.agentPhiW (L := L) (K := K) l x
          + Phase6PhiPotential.agentPhiW (L := L) (K := K) l y := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  simp [Multiset.map_cons, Multiset.sum_cons]

/-- The base-4 `phi` mass is additive over multiset addition. -/
theorem phiMass_add (l : ℕ) (a b : Config (AgentState L K)) :
    Phase6PhiPotential.phiMass (L := L) (K := K) l (a + b)
      = Phase6PhiPotential.phiMass (L := L) (K := K) l a
          + Phase6PhiPotential.phiMass (L := L) (K := K) l b := by
  unfold Phase6PhiPotential.phiMass
  rw [Multiset.map_add, Multiset.sum_add]

/-- Expand `phiMass` as a finite sum over state multiplicities. -/
theorem phiMass_eq_sum_count_agentPhiW (l : ℕ) (c : Config (AgentState L K)) :
    Phase6PhiPotential.phiMass (L := L) (K := K) l c =
      ∑ a : AgentState L K,
        c.count a * Phase6PhiPotential.agentPhiW (L := L) (K := K) l a := by
  classical
  unfold Phase6PhiPotential.phiMass
  calc
    (c.map (fun a => Phase6PhiPotential.agentPhiW (L := L) (K := K) l a)).sum
        = ∑ a ∈ c.toFinset,
            c.count a * Phase6PhiPotential.agentPhiW (L := L) (K := K) l a := by
          rw [Finset.sum_multiset_map_count]
          simp [Config.count]
    _ = ∑ a : AgentState L K,
        c.count a * Phase6PhiPotential.agentPhiW (L := L) (K := K) l a := by
          refine Finset.sum_subset (Finset.subset_univ c.toFinset) ?_
          intro a _ ha
          have hcount : c.count a = 0 := by
            rw [Config.count, Multiset.count_eq_zero]
            simpa using ha
          simp [hcount]

/-- Per-pair `phi` non-increase under the phase-6 dispatch. -/
theorem Phase6Transition_phi_pair_le (l : ℕ) (s t : AgentState L K)
    (hs6 : 6 ≤ s.phase.val) (ht6 : 6 ≤ t.phase.val) :
    Phase6PhiPotential.agentPhiW (L := L) (K := K) l (Phase6Transition L K s t).1
        + Phase6PhiPotential.agentPhiW (L := L) (K := K) l (Phase6Transition L K s t).2
      ≤ Phase6PhiPotential.agentPhiW (L := L) (K := K) l s
          + Phase6PhiPotential.agentPhiW (L := L) (K := K) l t := by
  unfold Phase6Transition
  simp only
  set s1 :=
    (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).1
    else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).2
    else s) with hs1def
  set t1 :=
    (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).2
    else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).1
    else t) with ht1def
  have hpre :
      Phase6PhiPotential.agentPhiW (L := L) (K := K) l s1
          + Phase6PhiPotential.agentPhiW (L := L) (K := K) l t1
        ≤ Phase6PhiPotential.agentPhiW (L := L) (K := K) l s
            + Phase6PhiPotential.agentPhiW (L := L) (K := K) l t := by
    rw [hs1def, ht1def]
    split_ifs with h1 h2
    · have h := doSplit_phi_pair_le (L := L) (K := K) l s t h1.1 h1.2.1
      linarith [h]
    · have h := doSplit_phi_pair_le (L := L) (K := K) l t s h2.1 h2.2.1
      linarith [h]
    · exact le_rfl
  have hs1p : 6 ≤ s1.phase.val := by
    rw [hs1def]
    split_ifs with h1 h2
    · rw [Phase6Convergence.doSplit_phase_fst_eq (L := L) (K := K) s t]
      exact hs6
    · rw [Phase6Convergence.doSplit_phase_snd_eq (L := L) (K := K) t s]
      exact hs6
    · exact hs6
  have ht1p : 6 ≤ t1.phase.val := by
    rw [ht1def]
    split_ifs with h1 h2
    · rw [Phase6Convergence.doSplit_phase_snd_eq (L := L) (K := K) s t]
      exact ht6
    · rw [Phase6Convergence.doSplit_phase_fst_eq (L := L) (K := K) t s]
      exact ht6
    · exact ht6
  rw [clockBranch_agentPhiW_eq (L := L) (K := K) l s1 (by omega),
      clockBranch_agentPhiW_eq (L := L) (K := K) l t1 (by omega)]
  exact hpre

private theorem mem_of_app_left6Phi {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right6Phi {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- `phiMass l` is non-increasing under any chosen-pair update on `Phase6Win`. -/
theorem phiMass_stepOrSelf_le (l n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (r₁ r₂ : AgentState L K) :
    Phase6PhiPotential.phiMass (L := L) (K := K) l
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ Phase6PhiPotential.phiMass (L := L) (K := K) l c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left6Phi happ
    have hm2 := mem_of_app_right6Phi happ
    have h16 : r₁.phase.val = 6 := hph r₁ hm1
    have h26 : r₂.phase.val = 6 := hph r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have htr : Transition L K r₁ r₂ = Phase6Transition L K r₁ r₂ :=
      Phase6Convergence.Transition_eq_Phase6Transition_of_phase6 (L := L) (K := K)
        r₁ r₂ h16 h26
    have hcsplit : c = (c - {r₁, r₂}) + {r₁, r₂} :=
      (tsub_add_cancel_of_le hsub).symm
    have hpairle : Phase6PhiPotential.phiMass (L := L) (K := K) l
        {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
          ≤ Phase6PhiPotential.phiMass (L := L) (K := K) l {r₁, r₂} := by
      unfold Phase6PhiPotential.phiMass
      rw [phiMass_pair, phiMass_pair, htr]
      exact Phase6Transition_phi_pair_le (L := L) (K := K) l r₁ r₂
        (by omega) (by omega)
    rw [hc', phiMass_add]
    calc
      Phase6PhiPotential.phiMass (L := L) (K := K) l (c - {r₁, r₂})
          + Phase6PhiPotential.phiMass (L := L) (K := K) l
              {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
        ≤ Phase6PhiPotential.phiMass (L := L) (K := K) l (c - {r₁, r₂})
          + Phase6PhiPotential.phiMass (L := L) (K := K) l {r₁, r₂} := by
            exact Nat.add_le_add_left hpairle _
      _ = Phase6PhiPotential.phiMass (L := L) (K := K) l c := by
            rw [← phiMass_add]
            rw [← hcsplit]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-! ## Weighted-drop bridge. -/

/-- A weighted-drop-sum lower bound yields kernel multiplicative drift for the
base-4 phase-6 potential.  The real rectangle proof supplies `hdrop`; this theorem
keeps the analytic bridge separate from the counting argument. -/
theorem phase6_phi_weighted_dyadic_mass_drift_of_dropSum
    (l n : ℕ) (hn : 2 ≤ n)
    (β : ℝ≥0∞) (hβtop : β ≠ ∞)
    (hdrop : ∀ b : Config (AgentState L K),
      Phase6Convergence.Phase6Win (L := L) (K := K) n b →
        β * (Phase6PhiPotential.phiMass (L := L) (K := K) l b : ℝ≥0∞)
          ≤ WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
              (fun c => Phase6PhiPotential.phiMass (L := L) (K := K) l c) b) :
    DyadicMassDrainTight.WeightedDyadicMassDrift (L := L) (K := K)
      (Phase6Convergence.Phase6Win (L := L) (K := K) n)
      (fun c => Phase6PhiPotential.phiMass (L := L) (K := K) l c)
      (1 - β) := by
  refine WeightedDriftDropSum.weighted_dyadic_mass_drift_on_of_dropSum
    (L := L) (K := K)
    (Phase6Convergence.Phase6Win (L := L) (K := K) n)
    (fun c => Phase6PhiPotential.phiMass (L := L) (K := K) l c)
    β hβtop ?_ ?_ hdrop
  · intro b hb
    rw [hb.1]
    exact hn
  · intro b hb pair
    exact phiMass_stepOrSelf_le (L := L) (K := K) l n b hb pair.1 pair.2

/-! ## Zero-set and guard sanity checks. -/

/-- Doty's base-4 potential has the same zero-set as the landed slot-6
`highMass` potential. -/
theorem highMass_eq_zero_of_phiMass_eq_zero
    (l : ℕ) (c : Config (AgentState L K))
    (hφ : Phase6PhiPotential.phiMass (L := L) (K := K) l c = 0) :
    Phase6Convergence.highMass (L := L) (K := K) l c = 0 := by
  rw [Phase6Convergence.highMass_eq_zero_iff]
  exact (Phase6PhiPotential.phiMass_eq_zero_iff (L := L) (K := K) l c).mp hφ

/-- With the current `doSplit` guard, no reserve hour can split a Main already at
index `L - 1`: `hour = L` is the only hour above `L - 1`, and it is excluded by
the sentinel guard `hour ≠ L`. -/
theorem no_reserve_hour_splits_top_index
    (r : AgentState L K) (hne : r.hour.val ≠ L) :
    ¬ r.hour.val > L - 1 := by
  have hle : r.hour.val ≤ L := Nat.le_of_lt_succ r.hour.isLt
  omega

/-- Consequently a Main whose bias index is `L - 1` cannot satisfy
`DoSplitApplicable` with any reserve.  This is a formal guard obstruction for a
terminal `l = L` Phase-6 drain. -/
theorem not_doSplitApplicable_top_index
    (r m : AgentState L K) {σ : Sign}
    (hLpos : 0 < L)
    (hbtop : m.bias = Bias.dyadic σ ⟨L - 1, by omega⟩) :
    ¬ Phase6Convergence.DoSplitApplicable (L := L) (K := K) r m := by
  rintro ⟨σ', j, hb, hne, hgt, _hlt⟩
  rw [hbtop] at hb
  rw [Bias.dyadic.injEq] at hb
  obtain ⟨_, hj⟩ := hb
  have hjval : j.val = L - 1 := by
    simpa using (congrArg Fin.val hj).symm
  have hbad : ¬ r.hour.val > L - 1 :=
    no_reserve_hour_splits_top_index (L := L) (K := K) r hne
  exact hbad (by simpa [hjval] using hgt)

/-! ## Axiom audit. -/

#print axioms clockBranch_agentPhiW_eq
#print axioms doSplit_phi_pair_le
#print axioms Phase6Transition_phi_pair_le
#print axioms phiMass_stepOrSelf_le
#print axioms phiMass_eq_sum_count_agentPhiW
#print axioms phase6_phi_weighted_dyadic_mass_drift_of_dropSum
#print axioms highMass_eq_zero_of_phiMass_eq_zero
#print axioms no_reserve_hour_splits_top_index
#print axioms not_doSplitApplicable_top_index

end Phase6PhiDrift
end Ripple.PopulationProtocol.ExactMajority

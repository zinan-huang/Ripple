/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-1 far-mass potential on the chain-genuine window

The historical `FarMassResidual` module found the right potential

  `farPhi v = max (|v - 3| - 1) 0`,

whose zero set is exactly `{2,3,4}`.  Its old lift used the unsatisfiable
`Phase1AllMain` window.  This file re-proves the usable core on
`PhaseOnlyWindows.Phase1Win`, where clocks and reserves coexist with Mains.

Only Main agents contribute to the potential.  A mixed-role phase-1 pair leaves
the Main endpoint unchanged, while a Main/Main pair applies `avgFin7`; hence the
potential is non-increasing for every phase-1 interaction.  No all-Main premise,
survival assumption, or protocol-definition change is used here.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOnlyWindows

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase1FarPhi

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The clamped distance from the safe interval `{2,3,4}`. -/
def farPhi (v : Fin 7) : ℕ :=
  (if v.val ≤ 3 then 3 - v.val else v.val - 3) - 1

/-- `farPhi` vanishes exactly on the values accepted by phase-2 init. -/
theorem farPhi_zero_iff_in234 (v : Fin 7) :
    farPhi v = 0 ↔ v.val ∈ ({2, 3, 4} : Finset ℕ) := by
  revert v
  decide

/-- A value outside `{2,3,4}` has positive far mass. -/
theorem farPhi_pos_of_not_in234 (v : Fin 7)
    (h : v.val ∉ ({2, 3, 4} : Finset ℕ)) :
    0 < farPhi v := by
  revert h
  revert v
  decide

/-- The naive far-value count is not monotone: `avgFin7 0 2 = (1,1)`. -/
theorem farCount_not_monotone :
    ¬ (∀ x y : Fin 7,
      (if (avgFin7 x y).1.val ≤ 1 ∨ 5 ≤ (avgFin7 x y).1.val then 1 else 0) +
          (if (avgFin7 x y).2.val ≤ 1 ∨ 5 ≤ (avgFin7 x y).2.val then 1 else 0)
        ≤ (if x.val ≤ 1 ∨ 5 ≤ x.val then 1 else 0) +
          (if y.val ≤ 1 ∨ 5 ≤ y.val then 1 else 0)) := by
  intro h
  have h02 := h ⟨0, by decide⟩ ⟨2, by decide⟩
  revert h02
  decide

/-- Averaging never increases the total clamped far mass. -/
theorem avgFin7_farPhi_pair_le (x y : Fin 7) :
    farPhi (avgFin7 x y).1 + farPhi (avgFin7 x y).2 ≤ farPhi x + farPhi y := by
  revert x y
  decide

/-- A far-high/Main-low interaction drops the far mass by at least one. -/
theorem avgFin7_farPhi_pair_drop_high (x y : Fin 7)
    (hx : 5 ≤ x.val) (hy : y.val ≤ 3) :
    farPhi (avgFin7 x y).1 + farPhi (avgFin7 x y).2 + 1 ≤ farPhi x + farPhi y := by
  revert hx hy
  revert x y
  decide

/-- A far-low/Main-high interaction drops the far mass by at least one. -/
theorem avgFin7_farPhi_pair_drop_low (x y : Fin 7)
    (hx : x.val ≤ 1) (hy : 3 ≤ y.val) :
    farPhi (avgFin7 x y).1 + farPhi (avgFin7 x y).2 + 1 ≤ farPhi x + farPhi y := by
  revert hx hy
  revert x y
  decide

/-- Per-agent contribution: only Main agents participate in integer averaging. -/
def farPhiMainN (a : AgentState L K) : ℕ :=
  if a.role = Role.main then farPhi a.smallBias else 0

/-- Total far mass of the Main subpopulation. -/
def farPhiN (c : Config (AgentState L K)) : ℕ :=
  (c.map (fun a => farPhiMainN a)).sum

/-- Two-element expansion for `farPhiMainN`. -/
theorem farPhiMainN_pair (x y : AgentState L K) :
    ((({x, y} : Multiset (AgentState L K)).map (fun a => farPhiMainN a)).sum)
      = farPhiMainN x + farPhiMainN y := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  simp [Multiset.map_cons, Multiset.sum_cons]

/-- Main/Main phase-1 averaging does not increase far mass. -/
theorem Transition_farPhi_pair_le_of_both_main (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    ((({(Transition L K s t).1, (Transition L K s t).2}
        : Multiset (AgentState L K)).map (fun a => farPhiMainN a)).sum)
      ≤ ((({s, t} : Multiset (AgentState L K)).map (fun a => farPhiMainN a)).sum) := by
  rw [Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs1 ht1 hsM htM]
  rw [farPhiMainN_pair, farPhiMainN_pair]
  simp only [farPhiMainN, hsM, htM, if_pos]
  exact avgFin7_farPhi_pair_le s.smallBias t.smallBias

/-- In a mixed-role phase-1 pair, each Main endpoint is unchanged by the full transition. -/
private theorem main_endpoints_fixed_of_not_both_main (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    (s.role = Role.main → (Transition L K s t).1 = s) ∧
      (t.role = Role.main → (Transition L K s t).2 = t) := by
  constructor
  · intro hsM
    have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
      (L := L) (K := K) s t hs1 ht1
    have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs1
    have hp1 : (Phase1Transition L K s t).1 = s := by
      unfold Phase1Transition
      rw [if_neg hnb]
      simp only []
      exact Phase1Convergence.clockCounterStep_eq_self_of_main s hsM
    unfold Transition
    rw [hepi]
    simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _
      (by rw [hp1, hs1]; decide)]
    exact hp1
  · intro htM
    have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
      (L := L) (K := K) s t hs1 ht1
    have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs1
    have hp1 : (Phase1Transition L K s t).2 = t := by
      unfold Phase1Transition
      rw [if_neg hnb]
      simp only []
      exact Phase1Convergence.clockCounterStep_eq_self_of_main t htM
    unfold Transition
    rw [hepi]
    simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _
      (by rw [hp1, ht1]; decide)]
    exact hp1

/-- Mixed-role phase-1 interactions preserve the total Main far mass exactly. -/
theorem Transition_farPhi_pair_eq_of_not_both_main (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    ((({(Transition L K s t).1, (Transition L K s t).2}
        : Multiset (AgentState L K)).map (fun a => farPhiMainN a)).sum)
      = ((({s, t} : Multiset (AgentState L K)).map (fun a => farPhiMainN a)).sum) := by
  rw [farPhiMainN_pair, farPhiMainN_pair]
  obtain ⟨hr1, hr2⟩ := PhaseOnlyWindows.Transition_role_phase1
    (L := L) (K := K) s t hs1 ht1
  obtain ⟨hfix1, hfix2⟩ := main_endpoints_fixed_of_not_both_main s t hs1 ht1 hnb
  have hside1 : farPhiMainN (Transition L K s t).1 = farPhiMainN s := by
    by_cases hsM : s.role = Role.main
    · rw [hfix1 hsM]
    · unfold farPhiMainN
      rw [if_neg hsM, if_neg]
      intro hout
      rw [hr1] at hout
      exact hsM hout
  have hside2 : farPhiMainN (Transition L K s t).2 = farPhiMainN t := by
    by_cases htM : t.role = Role.main
    · rw [hfix2 htM]
    · unfold farPhiMainN
      rw [if_neg htM, if_neg]
      intro hout
      rw [hr2] at hout
      exact htM hout
  rw [hside1, hside2]

/-- Far mass is non-increasing for every pair in the phase-only genuine window. -/
theorem Transition_farPhi_pair_le_of_phase1 (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1) :
    ((({(Transition L K s t).1, (Transition L K s t).2}
        : Multiset (AgentState L K)).map (fun a => farPhiMainN a)).sum)
      ≤ ((({s, t} : Multiset (AgentState L K)).map (fun a => farPhiMainN a)).sum) := by
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · exact Transition_farPhi_pair_le_of_both_main s t hs1 ht1 hboth.1 hboth.2
  · exact le_of_eq (Transition_farPhi_pair_eq_of_not_both_main s t hs1 ht1 hboth)

private theorem mem_of_app_left {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- Config-level far-mass non-increase on the chain-genuine phase-1 window. -/
theorem farPhiN_stepOrSelf_le_of_phase1Win (n : ℕ) (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (r₁ r₂ : AgentState L K) :
    farPhiN (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) ≤ farPhiN c := by
  obtain ⟨_, hphase⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left happ
    have hm2 := mem_of_app_right happ
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hsplit : c = (c - {r₁, r₂}) + ({r₁, r₂} : Multiset (AgentState L K)) := by
      rw [Multiset.sub_add_cancel hsub]
    have hpair := Transition_farPhi_pair_le_of_phase1 r₁ r₂
      (hphase r₁ hm1) (hphase r₂ hm2)
    unfold farPhiN
    rw [hc', Multiset.map_add, Multiset.sum_add]
    calc
      ((c - {r₁, r₂}).map (fun a => farPhiMainN a)).sum +
          (({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K)).map (fun a => farPhiMainN a)).sum
        ≤ ((c - {r₁, r₂}).map (fun a => farPhiMainN a)).sum +
            (({r₁, r₂} : Multiset (AgentState L K)).map (fun a => farPhiMainN a)).sum :=
          Nat.add_le_add_left hpair _
      _ = (c.map (fun a => farPhiMainN a)).sum := by
          conv_rhs => rw [hsplit]
          rw [Multiset.map_add, Multiset.sum_add]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- One-step support form of genuine far-mass non-increase. -/
theorem farPhiN_le_on_support_of_phase1Win (n m : ℕ)
    (c c' : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (hle : farPhiN c ≤ m)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    farPhiN c' ≤ m := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf
        rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support
      (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact (farPhiN_stepOrSelf_le_of_phase1Win n c hInv r₁ r₂).trans hle
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf
        rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst c'
    exact hle

/-- Kernel-level non-increase on the satisfiable phase-only window. -/
theorem farPhiN_kernel_noincr_of_phase1Win (n : ℕ) (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c) :
    (NonuniformMajority L K).transitionKernel c {x | farPhiN c < farPhiN x} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | farPhiN c < farPhiN x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  simp only [Set.mem_setOf_eq] at hx
  have hle : farPhiN x ≤ farPhiN c :=
    farPhiN_le_on_support_of_phase1Win n (farPhiN c) c x hInv le_rfl hsupp
  omega

/-- Engine packaging of the genuine-window supermartingale fact. -/
theorem potNonincrOn_farPhiN_phase1Win (n : ℕ) :
    OneSidedCancel.PotNonincrOn
      (fun c => PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel farPhiN :=
  fun c hInv => farPhiN_kernel_noincr_of_phase1Win n c hInv

/-- Every Main has a phase-2-safe integer bias. -/
def MainBiasSafe (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.main → a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)

/-- The far-mass zero set is exactly `MainBiasSafe`, without an all-Main assumption. -/
theorem farPhiN_eq_zero_iff_mainBiasSafe (c : Config (AgentState L K)) :
    farPhiN c = 0 ↔ MainBiasSafe c := by
  constructor
  · intro h a ha hmain
    unfold farPhiN at h
    rw [Multiset.sum_eq_zero_iff] at h
    have hterm : farPhiMainN a = 0 := h _ (Multiset.mem_map_of_mem _ ha)
    unfold farPhiMainN at hterm
    rw [if_pos hmain] at hterm
    exact (farPhi_zero_iff_in234 a.smallBias).1 hterm
  · intro h
    unfold farPhiN
    rw [Multiset.sum_eq_zero_iff]
    intro b hb
    rw [Multiset.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    unfold farPhiMainN
    by_cases hmain : a.role = Role.main
    · rw [if_pos hmain]
      exact (farPhi_zero_iff_in234 a.smallBias).2 (h a ha hmain)
    · rw [if_neg hmain]

/-- Non-Mains must separately carry the neutral small-bias provenance. -/
def NonMainNeutral (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role ≠ Role.main → a.smallBias.val = 3

/-- The genuine safe endpoint needed before phase-2 initialization. -/
def Phase1Safe (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c ∧
    NonMainNeutral c ∧ farPhiN c = 0

/-- A `Phase1Safe` endpoint gives the phase-2 init range for every agent. -/
theorem all_bias_in234_of_phase1Safe (n : ℕ) (c : Config (AgentState L K))
    (h : Phase1Safe (L := L) (K := K) n c) :
    ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  intro a ha
  by_cases hmain : a.role = Role.main
  · exact (farPhiN_eq_zero_iff_mainBiasSafe c).1 h.2.2 a ha hmain
  · have hneutral := h.2.1 a ha hmain
    rw [hneutral]
    decide

#print axioms farPhi_zero_iff_in234
#print axioms farCount_not_monotone
#print axioms avgFin7_farPhi_pair_le
#print axioms avgFin7_farPhi_pair_drop_high
#print axioms avgFin7_farPhi_pair_drop_low
#print axioms Transition_farPhi_pair_le_of_phase1
#print axioms farPhiN_stepOrSelf_le_of_phase1Win
#print axioms farPhiN_kernel_noincr_of_phase1Win
#print axioms potNonincrOn_farPhiN_phase1Win
#print axioms farPhiN_eq_zero_iff_mainBiasSafe
#print axioms all_bias_in234_of_phase1Safe

end Phase1FarPhi
end Ripple.PopulationProtocol.ExactMajority

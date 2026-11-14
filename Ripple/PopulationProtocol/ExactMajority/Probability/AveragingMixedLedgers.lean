import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingMixedAlgebra
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoSparse
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5To6FuelProducer

/-!
# Mixed ledgers and the double-pending potential

The absolute-mass transition audit is reused from PhaseTwoSparse.
The new equalities retain pending mass and inactive Main charges explicitly.
The final local inequalities concern the actual initialized Phase-3 rule;
they do not assert an augmented-potential kernel drift.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingMixedLedgers

open TimeTheorem P3DeterministicAlgebra AveragingMixedAlgebra

variable {L K : ℕ}

def inactiveMainWeight (a : AgentState L K) : ℕ :=
  if a.role = .main ∧ a.phase.val < 3 then 1 else 0

def inactiveMainCount (c : Config (AgentState L K)) : ℕ :=
  (c.map inactiveMainWeight).sum

def pendingAgentMass (a : AgentState L K) : ℚ :=
  if a.phase.val < 3 then |(AgentState.smallBiasInt a : ℚ)| else 0

def pendingMass (c : Config (AgentState L K)) : ℚ :=
  (c.map pendingAgentMass).sum

def lowHourZeroWeight (h : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = .main ∧ ¬ a.phase.val < 3 ∧
      a.bias = .zero ∧ a.hour.val < h then 1 else 0

def lowHourZeroCount (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  (c.map (lowHourZeroWeight h)).sum

def changingZeroFuel (h : ℕ) (c : Config (AgentState L K)) : ℚ :=
  (c.map (mainFuel h)).sum

theorem pendingAgentMass_nonneg (a : AgentState L K) :
    0 ≤ pendingAgentMass a := by
  unfold pendingAgentMass
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

theorem pendingAgentMass_le_inactiveMainWeight (a : AgentState L K)
    (hsafe : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4)
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3) :
    pendingAgentMass a ≤ (inactiveMainWeight a : ℚ) := by
  by_cases hp : a.phase.val < 3
  · by_cases hm : a.role = .main
    · simpa [pendingAgentMass, inactiveMainWeight, hp, hm] using
        safe_small_mass_le_one a hsafe
    · simp [pendingAgentMass, inactiveMainWeight, hp, hm,
        AgentState.smallBiasInt, hcarrier hm]
  · simp [pendingAgentMass, inactiveMainWeight, hp]

theorem pendingMass_le_inactiveMainCount (c : Config (AgentState L K))
    (hsafe : ∀ a ∈ c, 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4)
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3) :
    pendingMass c ≤ (inactiveMainCount c : ℚ) := by
  revert hsafe hcarrier
  induction c using Multiset.induction_on with
  | empty =>
      intro _ _
      simp [pendingMass, inactiveMainCount]
  | cons a c ih =>
      intro hsafe hcarrier
      have ha : a ∈ a ::ₘ c := Multiset.mem_cons_self _ _
      have hhead := pendingAgentMass_le_inactiveMainWeight a
        (hsafe a ha) (hcarrier a ha)
      have htail := ih
        (fun b hb => hsafe b (Multiset.mem_cons_of_mem hb))
        (fun b hb => hcarrier b (Multiset.mem_cons_of_mem hb))
      simpa only [pendingMass, inactiveMainCount, Multiset.map_cons,
        Multiset.sum_cons, Nat.cast_add] using add_le_add hhead htail

theorem inactiveMainWeight_le_of_fields (before after : AgentState L K)
    (hr : after.role = before.role)
    (hp : before.phase.val ≤ after.phase.val) :
    inactiveMainWeight after ≤ inactiveMainWeight before := by
  by_cases hb : before.role = .main ∧ before.phase.val < 3
  · simp only [inactiveMainWeight, if_pos hb]
    split_ifs <;> omega
  · have ha : ¬ (after.role = .main ∧ after.phase.val < 3) := by
      intro ha
      apply hb
      exact ⟨hr.symm.trans ha.1, lt_of_le_of_lt hp ha.2⟩
    simp only [inactiveMainWeight, if_neg hb, if_neg ha, le_refl]

/-- Roles are fixed throughout the mixed 1/2/3 window. The premise is on the
actual poststate, so no clock-height or future-success premise is hidden. -/
theorem transition_roles_before_exit
    (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hlcap : (Transition L 256 s t).1.phase.val ≤ 3)
    (hrcap : (Transition L 256 s t).2.phase.val ≤ 3) :
    (Transition L 256 s t).1.role = s.role ∧
      (Transition L 256 s t).2.role = t.role := by
  by_cases hmax : max s.phase.val t.phase.val ≤ 2
  · exact PhaseTwoSeedProfile.mixed_transition_roles s t
      ⟨hs.1, (le_max_left _ _).trans hmax⟩
      ⟨ht.1, (le_max_right _ _).trans hmax⟩ hlcap hrcap
  · have hmaxeq : max s.phase.val t.phase.val = 3 := by omega
    have hdata := PhaseTwoActivationLocal.epidemic_three_fields s t hs ht hmaxeq
    have hphases := PhaseTwoActivationLocal.epidemic_three_phases_of_success
      s t hs ht hmaxeq (by omega) (by omega)
    rcases he : phaseEpidemicUpdate L 256 s t with ⟨a, b⟩
    have ha : a.phase.val = 3 := by simpa only [he] using hphases.1
    have hb : b.phase.val = 3 := by simpa only [he] using hphases.2
    have har : a.role = s.role := by simpa only [he] using hdata.1.1
    have hbr : b.role = t.role := by simpa only [he] using hdata.2.1
    have hpa : a.phase = ⟨3, by decide⟩ := Fin.ext ha
    have hactual : Transition L 256 s t =
        (finishPhase10Entry L 256 a (Phase3Transition L 256 a b).1,
         finishPhase10Entry L 256 b (Phase3Transition L 256 a b).2) := by
      unfold Transition
      rw [he]
      simp only [hpa]
    rw [hactual]
    simpa only [finishPhase10Entry_role, har, hbr] using
      Phase5To6FuelProducer.Phase3Transition_roles a b ha hb

theorem inactiveMainCount_add_pair
    (c : Config (AgentState L K)) (s t : AgentState L K) :
    inactiveMainCount (c + {s, t}) =
      inactiveMainCount c + (inactiveMainWeight s + inactiveMainWeight t) := by
  simp [inactiveMainCount, Multiset.map_add, Multiset.sum_add,
    add_assoc, add_left_comm]

theorem inactiveMainCount_stepOrSelf
    (c : Cfg L 256) (s t : AgentState L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hcap : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      a.phase.val ≤ 3) :
    inactiveMainCount (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) ≤
      inactiveMainCount c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
        c - {s, t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    have hlmem : (Transition L 256 s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L 256) c s t := by rw [hstep]; simp
    have hrmem : (Transition L 256 s t).2 ∈
        Protocol.stepOrSelf (NonuniformMajority L 256) c s t := by rw [hstep]; simp
    have hroles := transition_roles_before_exit s t (hrange s hs) (hrange t ht)
      (hcap _ hlmem) (hcap _ hrmem)
    have hmono :
        s.phase.val ≤ (Transition L 256 s t).1.phase.val ∧
          t.phase.val ≤ (Transition L 256 s t).2.phase.val := by
      simpa using Transition_phase_monotone (L := L) (K := 256) s t
    have hpair := add_le_add
      (inactiveMainWeight_le_of_fields s _ hroles.1 hmono.1)
      (inactiveMainWeight_le_of_fields t _ hroles.2 hmono.2)
    have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L 256)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
    rw [hstep, inactiveMainCount_add_pair]
    conv_rhs => rw [hsplit]
    rw [inactiveMainCount_add_pair]
    exact add_le_add le_rfl hpair
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ] <;> exact le_rfl

theorem inactiveMainCount_draw
    (c : Cfg L 256) (d : Draw L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hcap : ∀ a ∈ applyDraw c d, a.phase.val ≤ 3) :
    inactiveMainCount (applyDraw c d) ≤ inactiveMainCount c := by
  cases d with
  | none => exact le_rfl
  | some p => exact inactiveMainCount_stepOrSelf c p.1.1 p.2.1 hrange hcap

theorem trace_inactiveMainCount_le
    (init : Cfg L 256) (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3) :
    inactiveMainCount (trace init ω t) ≤ inactiveMainCount (trace init ω s) := by
  revert hrange
  induction t, hst using Nat.le_induction with
  | base =>
      intro _
      exact le_rfl
  | succ t hst ih =>
      intro hrange
      have hprev := ih (fun u hsu hut => hrange u hsu (by omega))
      have hnext : inactiveMainCount (trace init ω (t + 1)) ≤
          inactiveMainCount (trace init ω t) := by
        rw [TimeTheorem.trace_succ]
        apply inactiveMainCount_draw _ (ω (t + 1)) (hrange t hst (by omega))
        intro a ha
        have ha' : a ∈ trace init ω (t + 1) := by
          simpa only [TimeTheorem.trace_succ] using ha
        exact (hrange (t + 1) (by omega) le_rfl a ha').2
      exact hnext.trans hprev

theorem mainFuel_eq_mass_add_counts (h : ℕ) (a : AgentState L K)
    (hcarrier : a.role ≠ .main → prePhase4Mass a = 0) :
    mainFuel h a =
      (2 : ℚ) ^ h * |prePhase4Mass a| +
        (lowHourZeroWeight h a : ℚ) + (inactiveMainWeight a : ℚ) := by
  by_cases hm : a.role = .main
  · by_cases hp : a.phase.val < 3 <;>
      by_cases hz : a.bias = .zero <;>
      by_cases hh : a.hour.val < h <;>
      simp [mainFuel, lowHourZeroWeight, inactiveMainWeight, hm, hp, hz, hh] <;>
      ring
  · simp [mainFuel, lowHourZeroWeight, inactiveMainWeight, hm, hcarrier hm]

theorem changingZeroFuel_eq (h : ℕ) (c : Config (AgentState L K))
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → prePhase4Mass a = 0) :
    changingZeroFuel h c =
      (2 : ℚ) ^ h * mixedAbsoluteMass c +
        (lowHourZeroCount h c : ℚ) + (inactiveMainCount c : ℚ) := by
  revert hcarrier
  induction c using Multiset.induction_on with
  | empty =>
      intro _
      simp [changingZeroFuel, mixedAbsoluteMass, lowHourZeroCount, inactiveMainCount]
  | cons a c ih =>
      intro hcarrier
      have ha := mainFuel_eq_mass_add_counts h a
        (hcarrier a (Multiset.mem_cons_self _ _))
      have ht := ih (fun b hb => hcarrier b (Multiset.mem_cons_of_mem hb))
      simp only [changingZeroFuel, mixedAbsoluteMass, lowHourZeroCount,
        inactiveMainCount, Multiset.map_cons, Multiset.sum_cons,
        Nat.cast_add] at ha ht ⊢
      rw [ha, ht]
      ring

/-- Actual mixed signed-side monotonicity on a safe pre-exit trace window.
The absolute-mass audit is the existing N11 sparse-entry audit. -/
theorem trace_mixedSides_le
    (init : Cfg L 256) (hinit : validInitial init)
    (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    mixedPositiveMass (trace init ω t) ≤ mixedPositiveMass (trace init ω s) ∧
      mixedNegativeMass (trace init ω t) ≤ mixedNegativeMass (trace init ω s) := by
  apply mixedSides_le_of_absolute_le
  · have hs := trace_mixedSigned_eq_initialGap init hinit ω s
      (fun a ha => (hrange s le_rfl hst a ha).2.trans (by omega))
    have ht := trace_mixedSigned_eq_initialGap init hinit ω t
      (fun a ha => (hrange t hst le_rfl a ha).2.trans (by omega))
    exact ht.trans hs.symm
  · exact PhaseTwoSparse.absolute_mass_trace init ω s t hst hrange hsafe hcarrier

/-- Active bias potential plus twice the index-zero pending charge.
On reachable safe states, non-Mains contribute zero to both branches. -/
def augmentedAgentPhi (h : ℕ) (a : AgentState L K) : ℚ :=
  if a.phase.val < 3 then pendingPotentialWeight h a else agentPhiAboveQ h a

def augmentedPhi (h : ℕ) (c : Config (AgentState L K)) : ℚ :=
  (c.map (augmentedAgentPhi h)).sum

def activeLevelWeight (h : ℕ) (a : AgentState L K) : ℚ :=
  if a.phase.val < 3 then 0 else
    match a.bias with
    | .zero => 0
    | .dyadic _ i => if i.val = h then 1 else 0

def activeLevelCount (h : ℕ) (c : Config (AgentState L K)) : ℚ :=
  (c.map (activeLevelWeight h)).sum

def mixedShallowWeight (h : ℕ) (a : AgentState L K) : ℚ :=
  if a.phase.val < 3 then |(AgentState.smallBiasInt a : ℚ)|
  else agentMassAboveQ h a

def mixedShallowMass (h : ℕ) (c : Config (AgentState L K)) : ℚ :=
  (c.map (mixedShallowWeight h)).sum

theorem agentPhiAbove_nonneg (h : ℕ) (a : AgentState L K) :
    0 ≤ agentPhiAboveQ h a := by
  unfold agentPhiAboveQ phiBiasWeightQ
  cases a.bias with
  | zero => exact le_rfl
  | dyadic sigma i =>
      dsimp only
      split_ifs <;> positivity

theorem augmentedAgentPhi_nonneg (h : ℕ) (a : AgentState L K) :
    0 ≤ augmentedAgentPhi h a := by
  unfold augmentedAgentPhi
  split_ifs
  · unfold pendingPotentialWeight
    positivity
  · exact agentPhiAbove_nonneg h a

theorem augmentedPhi_nonneg (h : ℕ) (c : Config (AgentState L K)) :
    0 ≤ augmentedPhi h c := by
  induction c using Multiset.induction_on with
  | empty => simp [augmentedPhi]
  | cons a c ih =>
      simpa only [augmentedPhi, Multiset.map_cons, Multiset.sum_cons] using
        add_nonneg (augmentedAgentPhi_nonneg h a) ih

theorem augmentedAgentPhi_eq_zero_of_nonMain
    (h : ℕ) (a : AgentState L K)
    (hs : a.smallBias.val = 3) (hb : a.bias = .zero) :
    augmentedAgentPhi h a = 0 := by
  simp [augmentedAgentPhi, pendingPotentialWeight, AgentState.smallBiasInt,
    hs, hb, agentPhiAboveQ, phiBiasWeightQ]

theorem initialize_augmentedPhi_eq_half
    (h : ℕ) (hh : 1 ≤ h) (a : AgentState L K)
    (hp : a.phase.val < 3)
    (hsafe : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4)
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3) :
    augmentedAgentPhi h (initializeAtPhaseThree a) =
      (1 / 2 : ℚ) * augmentedAgentPhi h a := by
  by_cases hm : a.role = .main
  · simpa [augmentedAgentPhi, hp, initializeAtPhaseThree_phase] using
      initializeAtPhaseThree_phi_eq_half_pending h hh a hm hsafe
  · have hb : a.smallBias.val = 3 := hcarrier hm
    have hz : (initializeAtPhaseThree a).bias = .zero := by
      cases hr : a.role <;>
        simp [initializeAtPhaseThree, phaseInit, hr] at hm ⊢
    simp [augmentedAgentPhi, initializeAtPhaseThree_phase, hp,
      pendingPotentialWeight, AgentState.smallBiasInt, hb,
      agentPhiAboveQ, phiBiasWeightQ, hz]

theorem augmentedAgentPhi_successor
    (h : ℕ) (hh : 1 ≤ h) (a : AgentState L K) :
    augmentedAgentPhi (h + 1) a =
      4 * augmentedAgentPhi h a + activeLevelWeight h a := by
  by_cases hp : a.phase.val < 3
  · have hpow : (4 : ℚ) ^ h = 4 * (4 : ℚ) ^ (h - 1) := by
      calc
        (4 : ℚ) ^ h = (4 : ℚ) ^ ((h - 1) + 1) := by congr 1; omega
        _ = 4 * (4 : ℚ) ^ (h - 1) := by rw [pow_succ]; ring
    simp only [augmentedAgentPhi, activeLevelWeight, if_pos hp, pendingPotentialWeight,
      Nat.add_sub_cancel]
    rw [hpow]
    ring
  · cases hb : a.bias with
    | zero =>
        simp [augmentedAgentPhi, activeLevelWeight, hp, hb,
          agentPhiAboveQ, phiBiasWeightQ]
    | dyadic sigma i =>
        by_cases hi : i.val < h
        · have his : i.val < h + 1 := by omega
          have hne : ¬ i.val = h := by omega
          have he : h + 1 - 1 - i.val = (h - 1 - i.val) + 1 := by omega
          simp only [augmentedAgentPhi, activeLevelWeight, if_neg hp,
            agentPhiAboveQ, phiBiasWeightQ, hb, if_pos hi, if_pos his,
            if_neg hne, add_zero]
          rw [he, pow_succ]
          ring
        · by_cases heq : i.val = h
          · simp [augmentedAgentPhi, activeLevelWeight, hp, hb,
              agentPhiAboveQ, phiBiasWeightQ, heq]
          · have his : ¬ i.val < h + 1 := by omega
            simp [augmentedAgentPhi, activeLevelWeight, hp, hb,
              agentPhiAboveQ, phiBiasWeightQ, hi, his, heq]

theorem augmentedPhi_successor
    (h : ℕ) (hh : 1 ≤ h) (c : Config (AgentState L K)) :
    augmentedPhi (h + 1) c =
      4 * augmentedPhi h c + activeLevelCount h c := by
  induction c using Multiset.induction_on with
  | empty => simp [augmentedPhi, activeLevelCount]
  | cons a c ih =>
      have ha := augmentedAgentPhi_successor h hh a
      simp only [augmentedPhi, activeLevelCount,
        Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      rw [ha, ih]
      ring

theorem scaled_shallow_bias_le_phi (h : ℕ) (b : Bias L) :
    (2 : ℚ) ^ h * biasMassAboveQ h b ≤ 2 * phiBiasWeightQ h b := by
  cases b with
  | zero => simp [biasMassAboveQ, phiBiasWeightQ]
  | dyadic sigma i =>
      by_cases hi : i.val < h
      · let k := h - 1 - i.val
        have he : h = i.val + k + 1 := by dsimp [k]; omega
        have hid : (2 : ℚ) ^ h * weightQ i = 2 * (2 : ℚ) ^ k := by
          rw [he, weightQ, pow_succ, pow_add]
          have hden : (2 : ℚ) ^ i.val ≠ 0 := by positivity
          field_simp [hden]
          <;> ring
        have hp : (2 : ℚ) ^ k ≤ (4 : ℚ) ^ k := by
          gcongr <;> norm_num
        simp only [biasMassAboveQ, phiBiasWeightQ, if_pos hi]
        rw [hid]
        change 2 * (2 : ℚ) ^ k ≤ 2 * (4 : ℚ) ^ k
        nlinarith
      · simp [biasMassAboveQ, phiBiasWeightQ, hi]

theorem scaled_mixedShallowWeight_le_phi
    (h : ℕ) (hh : 1 ≤ h) (a : AgentState L K) :
    (2 : ℚ) ^ h * mixedShallowWeight h a ≤ 2 * augmentedAgentPhi h a := by
  by_cases hp : a.phase.val < 3
  · have hpowers : (2 : ℚ) ^ h ≤ (4 : ℚ) ^ h := by
      gcongr <;> norm_num
    have he : (4 : ℚ) ^ h = 4 * (4 : ℚ) ^ (h - 1) := by
      calc
        (4 : ℚ) ^ h = (4 : ℚ) ^ ((h - 1) + 1) := by
          congr 1
          omega
        _ = 4 * (4 : ℚ) ^ (h - 1) := by rw [pow_succ]; ring
    have hm := mul_le_mul_of_nonneg_right hpowers
      (abs_nonneg (AgentState.smallBiasInt a : ℚ))
    rw [he] at hm
    simp only [mixedShallowWeight, augmentedAgentPhi, if_pos hp,
      pendingPotentialWeight]
    nlinarith
  · simpa only [mixedShallowWeight, augmentedAgentPhi, if_neg hp,
      agentMassAboveQ, agentPhiAboveQ] using scaled_shallow_bias_le_phi h a.bias

theorem scaled_mixedShallowMass_le_phi
    (h : ℕ) (hh : 1 ≤ h) (c : Config (AgentState L K)) :
    (2 : ℚ) ^ h * mixedShallowMass h c ≤ 2 * augmentedPhi h c := by
  induction c using Multiset.induction_on with
  | empty => simp [mixedShallowMass, augmentedPhi]
  | cons a c ih =>
      have ha := scaled_mixedShallowWeight_le_phi h hh a
      simp only [mixedShallowMass, augmentedPhi,
        Multiset.map_cons, Multiset.sum_cons] at ih ⊢
      nlinarith

theorem cancelSplit_phi_pair_le
    (h : ℕ) (s t : AgentState L K) :
    pairPhiAboveQ h (phase3CancelSplit L K s t).1
        (phase3CancelSplit L K s t).2 ≤ pairPhiAboveQ h s t := by
  have hnonneg : 0 ≤ pairPhiAboveQ h s t :=
    add_nonneg (agentPhiAbove_nonneg h s) (agentPhiAbove_nonneg h t)
  cases hs : s.bias with
  | zero =>
      cases ht : t.bias with
      | zero => simp [phase3CancelSplit, hs, ht]
      | dyadic sigma i =>
          by_cases hgt : s.hour.val > i.val
          · by_cases hi : i.val < h
            · have hdrop := p3_phiAbove_split_delta_left h s t sigma i hs ht hgt hi
              have hp : 0 ≤ (4 : ℚ) ^ (h - 1 - i.val) := by positivity
              exact hdrop.trans (by linarith)
            · have his : ¬ i.val + 1 < h := by omega
              simp [phase3CancelSplit, hs, ht, hgt, pairPhiAboveQ,
                agentPhiAboveQ, phiBiasWeightQ, hi, his]
          · simp [phase3CancelSplit, hs, ht, hgt]
  | dyadic sigma i =>
      cases ht : t.bias with
      | zero =>
          by_cases hgt : t.hour.val > i.val
          · by_cases hi : i.val < h
            · have hdrop := p3_phiAbove_split_delta_right h s t sigma i hs ht hgt hi
              have hp : 0 ≤ (4 : ℚ) ^ (h - 1 - i.val) := by positivity
              exact hdrop.trans (by linarith)
            · have his : ¬ i.val + 1 < h := by omega
              simp [phase3CancelSplit, hs, ht, hgt, pairPhiAboveQ,
                agentPhiAboveQ, phiBiasWeightQ, hi, his]
          · simp [phase3CancelSplit, hs, ht, hgt]
      | dyadic tau j =>
          cases sigma <;> cases tau
          · simp [phase3CancelSplit, hs, ht]
          · by_cases hij : i.val = j.val
            · calc
                pairPhiAboveQ h (phase3CancelSplit L K s t).1
                    (phase3CancelSplit L K s t).2 = 0 := by
                  simp [phase3CancelSplit, hs, ht, hij, pairPhiAboveQ,
                    agentPhiAboveQ, phiBiasWeightQ]
                _ ≤ pairPhiAboveQ h s t := hnonneg
            · simp [phase3CancelSplit, hs, ht, hij]
          · by_cases hij : i.val = j.val
            · calc
                pairPhiAboveQ h (phase3CancelSplit L K s t).1
                    (phase3CancelSplit L K s t).2 = 0 := by
                  simp [phase3CancelSplit, hs, ht, hij, pairPhiAboveQ,
                    agentPhiAboveQ, phiBiasWeightQ]
                _ ≤ pairPhiAboveQ h s t := hnonneg
            · simp [phase3CancelSplit, hs, ht, hij]
          · simp [phase3CancelSplit, hs, ht]

/-- The full selected Phase-3 rule, including dragging and clock counters,
cannot increase the initialized shallow potential. -/
theorem phaseThree_phi_pair_le
    (h : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    pairPhiAboveQ h (Phase3Transition L K s t).1
        (Phase3Transition L K s t).2 ≤ pairPhiAboveQ h s t := by
  by_cases hm : s.role = .main ∧ t.role = .main
  · simpa [Phase3Transition, hm.1, hm.2] using cancelSplit_phi_pair_le h s t
  · have hb := Phase5To6FuelProducer.Phase3Transition_biases_of_not_both_main
      s t hs ht hm
    simp only [pairPhiAboveQ, agentPhiAboveQ, hb.1, hb.2, le_refl]

theorem phaseThree_augmentedPhi_pair_le
    (h : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    augmentedAgentPhi h (Phase3Transition L K s t).1 +
        augmentedAgentPhi h (Phase3Transition L K s t).2 ≤
      augmentedAgentPhi h s + augmentedAgentPhi h t := by
  have hm :
      s.phase.val ≤ (Phase3Transition L K s t).1.phase.val ∧
        t.phase.val ≤ (Phase3Transition L K s t).2.phase.val :=
    Phase3Transition_phase_nondec L K s t
  have hnleft : ¬ (Phase3Transition L K s t).1.phase.val < 3 := by omega
  have hnright : ¬ (Phase3Transition L K s t).2.phase.val < 3 := by omega
  simpa [augmentedAgentPhi, hs, ht, hnleft, hnright, pairPhiAboveQ] using
    phaseThree_phi_pair_le h s t hs ht

end Ripple.PopulationProtocol.ExactMajority.AveragingMixedLedgers

end

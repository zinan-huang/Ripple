-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingMajorityPartners.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCreditCount

/-!
# A persistent supply of majority partners near the terminal scale

The two-index capacity estimate includes pending mass in the shallow term.
A .4 M scaled gap and .002 M shallow allowance force at least .19 M active
majority Mains at indices ell and ell+1.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingMajorityPartners

open TimeTheorem P3DeterministicAlgebra AveragingMixedAlgebra AveragingMixedLedgers
open AveragingPendingCredit AveragingCreditTransitions AveragingTerminalDebt
open AveragingCreditCount

variable {L K : ℕ}

def majorityPart : Sign → ℚ → ℚ
  | .pos, x => max x 0
  | .neg, x => max (-x) 0

def majorityMass : Sign → Cfg L K → ℚ
  | .pos, c => mixedPositiveMass c
  | .neg, c => mixedNegativeMass c

def nearMajorityWeight (σ : Sign) (ell : ℕ) (s : AgentState L K) : ℕ :=
  if s.role = .main ∧ ¬ s.phase.val < 3 then
    match s.bias with
    | .zero => 0
    | .dyadic tau i =>
        if tau = σ ∧ ell ≤ i.val ∧ i.val ≤ ell + 1 then 1 else 0
  else 0

def nearMajorityCount (σ : Sign) (ell : ℕ) (c : Cfg L K) : ℕ :=
  (c.map (nearMajorityWeight σ ell)).sum

theorem majorityPart_le_abs (σ : Sign) (x : ℚ) :
    majorityPart σ x ≤ |x| := by
  cases σ
  · exact max_le (le_abs_self x) (abs_nonneg x)
  · have hx : -x ≤ |x| := by simpa only [abs_neg] using le_abs_self (-x)
    exact max_le hx (abs_nonneg x)

theorem majorityPart_dyadic (σ tau : Sign) (i : Fin (L + 1)) :
    majorityPart σ (Bias.toRat (.dyadic tau i)) =
      if tau = σ then weightQ i else 0 := by
  have hw := weightQ_nonneg i
  cases σ <;> cases tau <;>
    simp [majorityPart, Bias.toRat, weightQ, neg_div,
      max_eq_left hw, max_eq_right (neg_nonpos.mpr hw)]

theorem scaledWeight_le_one_of_le {ell j : ℕ} (hj : ell ≤ j) :
    scaledWeight ell j ≤ (1 : ℚ) := by
  unfold scaledWeight
  apply (div_le_one (by positivity : (0 : ℚ) < (2 : ℚ) ^ j)).2
  exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hj

theorem scaledWeight_le_quarter_of_two_le {ell j : ℕ} (hj : ell + 2 ≤ j) :
    scaledWeight ell j ≤ (1 / 4 : ℚ) := by
  have hp : (2 : ℚ) ^ (ell + 2) ≤ (2 : ℚ) ^ j :=
    pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hj
  unfold scaledWeight
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ j)).2
  norm_num [pow_add] at hp
  linarith

theorem near_majority_capacity_agent (σ : Sign) (ell : ℕ) (s : AgentState L K)
    (hcarrier : ¬ s.phase.val < 3 → s.role ≠ .main → s.bias = .zero) :
    (2 : ℚ) ^ ell *
        (majorityPart σ (prePhase4Mass s) - mixedShallowWeight ell s) ≤
      (mainUnit s + 3 * (nearMajorityWeight σ ell s : ℚ)) / 4 := by
  have hmz : majorityPart σ 0 = 0 := by cases σ <;> simp [majorityPart]
  by_cases hp : s.phase.val < 3
  · have hpart := majorityPart_le_abs σ (AgentState.smallBiasInt s : ℚ)
    have hleft := mul_nonpos_of_nonneg_of_nonpos
      (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ ell)
      (sub_nonpos.mpr hpart)
    have hright : (0 : ℚ) ≤ mainUnit s / 4 := by
      unfold mainUnit
      split_ifs <;> norm_num
    simpa [prePhase4Mass, mixedShallowWeight, hp, nearMajorityWeight] using
      hleft.trans hright
  · by_cases hm : s.role = .main
    · cases hb : s.bias with
      | zero =>
          simp [prePhase4Mass, mixedShallowWeight, hp, mainUnit, hm,
            nearMajorityWeight, hb, agentMassAboveQ, biasMassAboveQ,
            hmz, Bias.toRat]
      | dyadic tau i =>
          have hw := weightQ_nonneg i
          by_cases hsign : tau = σ
          · by_cases hlow : i.val < ell
            · simp [prePhase4Mass, mixedShallowWeight, hp, mainUnit, hm,
                nearMajorityWeight, hb, agentMassAboveQ, biasMassAboveQ,
                majorityPart_dyadic, hsign, hlow, show ¬ ell ≤ i.val by omega]
            · by_cases hnear : i.val ≤ ell + 1
              · have hs := scaledWeight_le_one_of_le (show ell ≤ i.val by omega)
                simpa [prePhase4Mass, mixedShallowWeight, hp, mainUnit, hm,
                  nearMajorityWeight, hb, agentMassAboveQ, biasMassAboveQ,
                  majorityPart_dyadic, hsign, hlow, show ell ≤ i.val by omega,
                  hnear, scaledWeight, weightQ, mul_div_assoc, div_eq_mul_inv] using
                  hs.trans (by norm_num : (1 : ℚ) ≤ (1 + 3) / 4)
              · have hs := scaledWeight_le_quarter_of_two_le
                  (show ell + 2 ≤ i.val by omega)
                simpa [prePhase4Mass, mixedShallowWeight, hp, mainUnit, hm,
                  nearMajorityWeight, hb, agentMassAboveQ, biasMassAboveQ,
                  majorityPart_dyadic, hsign, hlow, hnear,
                  scaledWeight, weightQ, mul_div_assoc] using hs
          · have hshallow : (0 : ℚ) ≤ mixedShallowWeight ell s := by
              simp only [mixedShallowWeight, if_neg hp, agentMassAboveQ,
                hb, biasMassAboveQ]
              split_ifs <;> positivity
            have hleft : (2 : ℚ) ^ ell *
                (majorityPart σ (prePhase4Mass s) - mixedShallowWeight ell s) ≤ 0 := by
              have hz : majorityPart σ (prePhase4Mass s) = 0 := by
                simp [prePhase4Mass, hp, hb, majorityPart_dyadic, hsign]
              rw [hz]
              exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
            have hright : (0 : ℚ) ≤
                (mainUnit s + 3 * (nearMajorityWeight σ ell s : ℚ)) / 4 := by
              simp [mainUnit, hm, nearMajorityWeight, hp, hb, hsign]
            exact hleft.trans hright
    · have hb := hcarrier hp hm
      simp [prePhase4Mass, mixedShallowWeight, hp, mainUnit, hm,
        nearMajorityWeight, hb, agentMassAboveQ, biasMassAboveQ, hmz, Bias.toRat]

theorem majorityMass_cons (σ : Sign) (s : AgentState L K) (c : Cfg L K) :
    majorityMass σ (s ::ₘ c) =
      majorityPart σ (prePhase4Mass s) + majorityMass σ c := by
  cases σ <;> simp [majorityMass, majorityPart, mixedPositiveMass, mixedNegativeMass]

theorem near_majority_capacity (σ : Sign) (ell : ℕ) (c : Cfg L K)
    (hcarrier : ∀ s ∈ c, ¬ s.phase.val < 3 → s.role ≠ .main → s.bias = .zero) :
    (2 : ℚ) ^ ell * (majorityMass σ c - mixedShallowMass ell c) ≤
      ((RoleSplitConcentration.mainCount c : ℚ) +
        3 * (nearMajorityCount σ ell c : ℚ)) / 4 := by
  revert hcarrier
  induction c using Multiset.induction_on with
  | empty =>
      intro _
      cases σ <;> simp [majorityMass, mixedPositiveMass, mixedNegativeMass,
        mixedShallowMass, nearMajorityCount, RoleSplitConcentration.mainCount]
  | cons s c ih =>
      intro hcarrier
      have hs := near_majority_capacity_agent σ ell s
        (hcarrier s (Multiset.mem_cons_self s c))
      have ht := ih (fun a ha => hcarrier a (Multiset.mem_cons_of_mem ha))
      rw [majorityMass_cons, mainCount_cons_cast]
      simp only [mixedShallowMass, nearMajorityCount, Multiset.map_cons,
        Multiset.sum_cons, Nat.cast_add] at ht ⊢
      nlinarith only [hs, ht]

/-- The permanent .19 M partner floor derived from the mass targets. -/
theorem majority_partner_floor (σ : Sign) (ell M : ℕ) (c : Cfg L K)
    (hM : RoleSplitConcentration.mainCount c = M)
    (hcarrier : ∀ s ∈ c, ¬ s.phase.val < 3 → s.role ≠ .main → s.bias = .zero)
    (hmass : (2 : ℚ) ^ ell * majorityMass σ c ≥ (2 / 5 : ℚ) * M)
    (hshallow : (2 : ℚ) ^ ell * mixedShallowMass ell c ≤ (1 / 500 : ℚ) * M) :
    19 * M ≤ 100 * nearMajorityCount σ ell c := by
  have hcap := near_majority_capacity σ ell c hcarrier
  rw [hM] at hcap
  have hnonneg : (0 : ℚ) ≤ (M : ℚ) := by positivity
  have hq : (19 : ℚ) * M ≤ 100 * (nearMajorityCount σ ell c : ℚ) := by
    nlinarith only [hcap, hmass, hshallow, hnonneg]
  exact_mod_cast hq

theorem majorityMass_ge_signed_gap (σ : Sign) (c : Cfg L K) (gap : ℚ)
    (hsigned : prePhase4MassSum c = if σ = .pos then gap else -gap) :
    gap ≤ majorityMass σ c := by
  have hi := (mixedMassIdentities c).1
  have hn := minorityMass_nonneg σ c
  cases σ <;> simp [majorityMass, minorityMass] at hsigned hn ⊢ <;> linarith

theorem majority_partner_floor_of_gap_and_phi
    (σ : Sign) (ell M : ℕ) (c : Cfg L K) (gap : ℚ)
    (hell : 1 ≤ ell) (hM : RoleSplitConcentration.mainCount c = M)
    (hcarrier : ∀ s ∈ c, ¬ s.phase.val < 3 → s.role ≠ .main → s.bias = .zero)
    (hsigned : prePhase4MassSum c = if σ = .pos then gap else -gap)
    (hscale : (2 / 5 : ℚ) * M ≤ (2 : ℚ) ^ ell * gap)
    (hphi : augmentedPhi ell c ≤ (1 / 1000 : ℚ) * M) :
    19 * M ≤ 100 * nearMajorityCount σ ell c := by
  have hm := majorityMass_ge_signed_gap σ c gap hsigned
  have hmass := hscale.trans (mul_le_mul_of_nonneg_left hm (by positivity))
  have hs := scaled_mixedShallowMass_le_phi ell hell c
  have hshallow : (2 : ℚ) ^ ell * mixedShallowMass ell c ≤ (1 / 500 : ℚ) * M := by
    linarith
  exact majority_partner_floor σ ell M c hM hcarrier hmass hshallow

/-- The active exact-hour-zero targets used by the second terminal drain. -/
def TerminalZero (k : ℕ) (s : AgentState L 256) : Prop :=
  s.phase.val = 3 ∧ s.role = .main ∧ s.bias = .zero ∧ s.hour.val = k

/-- The actual two-index majority service set. -/
def NearMajority (σ : Sign) (ell : ℕ) (s : AgentState L 256) : Prop :=
  s.phase.val = 3 ∧ s.role = .main ∧
    ∃ i : Fin (L + 1), s.bias = .dyadic σ i ∧ ell ≤ i.val ∧ i.val ≤ ell + 1

open Classical in
theorem exactZeroWeight_eq_indicator (k : ℕ) (s : AgentState L 256)
    (hcap : s.phase.val ≤ 3) :
    exactZeroWeight k s = if TerminalZero k s then 1 else 0 := by
  unfold exactZeroWeight TerminalZero
  have he : (s.role = .main ∧ ¬ s.phase.val < 3 ∧
      s.bias = .zero ∧ s.hour.val = k) ↔
      (s.phase.val = 3 ∧ s.role = .main ∧ s.bias = .zero ∧ s.hour.val = k) := by
    constructor
    · rintro ⟨hm, hp, hb, hh⟩
      exact ⟨by omega, hm, hb, hh⟩
    · rintro ⟨hp, hm, hb, hh⟩
      exact ⟨hm, by omega, hb, hh⟩
  by_cases hp : s.role = .main ∧ ¬ s.phase.val < 3 ∧
      s.bias = .zero ∧ s.hour.val = k
  · rw [if_pos hp, if_pos (he.mp hp)]
  · rw [if_neg hp, if_neg (mt he.mpr hp)]

open Classical in
theorem nearMajorityWeight_eq_indicator (σ : Sign) (ell : ℕ)
    (s : AgentState L 256) (hcap : s.phase.val ≤ 3) :
    nearMajorityWeight σ ell s = if NearMajority σ ell s then 1 else 0 := by
  by_cases hp : s.phase.val = 3
  · by_cases hm : s.role = .main
    · cases hb : s.bias with
      | zero => simp [nearMajorityWeight, NearMajority, hp, hm, hb]
      | dyadic tau i =>
          by_cases ht : tau = σ
          · subst tau
            by_cases hlo : ell ≤ i.val <;> by_cases hhi : i.val ≤ ell + 1 <;>
              simp [nearMajorityWeight, NearMajority, hp, hm, hb, hlo, hhi]
          · simp [nearMajorityWeight, NearMajority, hp, hm, hb, ht]
    · simp [nearMajorityWeight, NearMajority, hm]
  · have hlo : s.phase.val < 3 := by omega
    simp [nearMajorityWeight, NearMajority, hp, hlo]

theorem terminalZero_ne_nearMajority (σ : Sign) (ell : ℕ)
    (s t : AgentState L 256)
    (hs : TerminalZero (ell + 2) s) (ht : NearMajority σ ell t) : s ≠ t := by
  rintro rfl
  obtain ⟨i, hi, _, _⟩ := ht.2.2
  rw [hs.2.2.1] at hi
  cases hi

/-- First ordered rectangle for the actual Y service event. -/
theorem debtY_step_service_left (σ : Sign) (ell : ℕ)
    (c : Cfg L 256) (s t : AgentState L 256)
    (happ : Protocol.Applicable c s t)
    (hs : TerminalZero (ell + 2) s) (ht : NearMajority σ ell t) :
    debtY σ (ell + 2)
        (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 =
      debtY σ (ell + 2) c := by
  obtain ⟨i, hi, hlo, hhi⟩ := ht.2.2
  exact AveragingDebtService.totalDebt_step_service _ _ (ell + 2 + 1) c s t happ
    (AveragingDebtService.transition_split_service_left _ _ (ell + 2 + 1)
      s t σ i hs.1 ht.1 hs.2.1 ht.2.1 hs.2.2.1 hi
      (by rw [hs.2.2.2]; omega) (by rw [hs.2.2.2]; omega))

/-- Second ordered rectangle, retained explicitly for the factor two. -/
theorem debtY_step_service_right (σ : Sign) (ell : ℕ)
    (c : Cfg L 256) (s t : AgentState L 256)
    (happ : Protocol.Applicable c s t)
    (hs : NearMajority σ ell s) (ht : TerminalZero (ell + 2) t) :
    debtY σ (ell + 2)
        (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 =
      debtY σ (ell + 2) c := by
  obtain ⟨i, hi, hlo, hhi⟩ := hs.2.2
  exact AveragingDebtService.totalDebt_step_service _ _ (ell + 2 + 1) c s t happ
    (AveragingDebtService.transition_split_service_right _ _ (ell + 2 + 1)
      s t σ i hs.1 ht.1 hs.2.1 ht.2.1 hi ht.2.2.1
      (by rw [ht.2.2.2]; omega) (by rw [ht.2.2.2]; omega))

end Ripple.PopulationProtocol.ExactMajority.AveragingMajorityPartners

end

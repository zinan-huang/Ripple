-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedMixedPositive.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReadout
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingPendingCreditTransitions
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingLiveProduct

/-!
# The pending-aware two-level majority process

The majority mass at active indices at most ell is charged together with
pending majority small bias. Safe Init 3 preserves this charge exactly.
The literal mixed dispatcher can only decrease it. At an initialized
checkpoint the charge is the N16 scaledShallowPositive readout.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem AveragingMixedAlgebra AveragingMixedLedgers
open AveragingPendingCredit AveragingCreditTransitions
open PhaseTwoActivationLocal PhaseTwoProvenance PhaseTwoSparse

variable {L K n : ℕ}

def majorityPart : Sign → ℚ → ℚ
  | .pos, x => max x 0
  | .neg, x => max (-x) 0

def shallowWeight (ell j : ℕ) : ℚ :=
  if j ≤ ell then scaledWeight ell j else 0

def shallowBias (σ : Sign) (ell : ℕ) : Bias L → ℚ
  | .zero => 0
  | .dyadic τ j => if τ = σ then shallowWeight ell j.val else 0

def activeShallowAgent (σ : Sign) (ell : ℕ) (a : AgentState L K) : ℚ :=
  if a.role = .main then shallowBias σ ell a.bias else 0

def mixedShallowAgent (σ : Sign) (ell : ℕ) (a : AgentState L K) : ℚ :=
  if a.phase.val < 3 then
    (2 : ℚ) ^ ell * majorityPart σ (smallValue a.smallBias)
  else activeShallowAgent σ ell a

def mixedShallowPositive (σ : Sign) (ell : ℕ) (c : Cfg L K) : ℚ :=
  Config.sumOf (mixedShallowAgent σ ell) c

def shallowWeightNat (ell j : ℕ) : ℕ :=
  if j ≤ ell then 2 ^ (ell - j) else 0

def shallowBiasNat (σ : Sign) (ell : ℕ) : Bias L → ℕ
  | .zero => 0
  | .dyadic τ j => if τ = σ then shallowWeightNat ell j.val else 0

def pendingMajorityNat : Sign → Fin 7 → ℕ
  | .pos, x => x.val - 3
  | .neg, x => 3 - x.val

def mixedShallowAgentNat (σ : Sign) (ell : ℕ) (a : AgentState L K) : ℕ :=
  if a.phase.val < 3 then
    2 ^ ell * pendingMajorityNat σ a.smallBias
  else if a.role = .main then shallowBiasNat σ ell a.bias else 0

def mixedShallowPositiveNat (σ : Sign) (ell : ℕ) (c : Cfg L K) : ℕ :=
  Config.sumOf (mixedShallowAgentNat σ ell) c

theorem majorityPart_nonneg (σ : Sign) (x : ℚ) :
    0 ≤ majorityPart σ x := by
  cases σ <;> exact le_max_right _ _

theorem shallowWeight_nonneg (ell j : ℕ) : 0 ≤ shallowWeight ell j := by
  unfold shallowWeight
  split_ifs
  · exact scaledWeight_nonneg ell j
  · exact le_rfl

theorem shallowBias_nonneg (σ : Sign) (ell : ℕ) (b : Bias L) :
    0 ≤ shallowBias σ ell b := by
  cases b with
  | zero => exact le_rfl
  | dyadic τ j =>
      simp only [shallowBias]
      split_ifs
      · exact shallowWeight_nonneg ell j.val
      · exact le_rfl

theorem mixedShallowAgent_nonneg (σ : Sign) (ell : ℕ) (a : AgentState L K) :
    0 ≤ mixedShallowAgent σ ell a := by
  unfold mixedShallowAgent activeShallowAgent
  split_ifs
  · exact mul_nonneg (by positivity) (majorityPart_nonneg σ _)
  · exact shallowBias_nonneg σ ell a.bias
  · exact le_rfl

theorem mixedShallowPositive_nonneg (σ : Sign) (ell : ℕ) (c : Cfg L K) :
    0 ≤ mixedShallowPositive σ ell c := by
  unfold mixedShallowPositive Config.sumOf
  exact Multiset.sum_nonneg (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    exact mixedShallowAgent_nonneg σ ell a)

theorem shallowWeight_eq_pow (ell j : ℕ) (hj : j ≤ ell) :
    shallowWeight ell j = (2 : ℚ) ^ (ell - j) := by
  rw [shallowWeight, if_pos hj, scaledWeight]
  have hp : (2 : ℚ) ^ ell = (2 : ℚ) ^ (ell - j) * (2 : ℚ) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  rw [hp]
  have hz : (2 : ℚ) ^ j ≠ 0 := by positivity
  field_simp [hz]

theorem shallowWeight_eq_nat (ell j : ℕ) :
    shallowWeight ell j = (shallowWeightNat ell j : ℚ) := by
  by_cases hj : j ≤ ell
  · rw [shallowWeight_eq_pow ell j hj]
    simp [shallowWeightNat, hj]
  · simp [shallowWeight, shallowWeightNat, hj]

theorem shallowBias_eq_nat (σ : Sign) (ell : ℕ) (b : Bias L) :
    shallowBias σ ell b = (shallowBiasNat σ ell b : ℚ) := by
  cases b with
  | zero => rfl
  | dyadic τ j =>
      by_cases hτ : τ = σ <;>
        simp [shallowBias, shallowBiasNat, hτ, shallowWeight_eq_nat]

theorem mixedShallowAgent_eq_nat (σ : Sign) (ell : ℕ) (a : AgentState L K)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    mixedShallowAgent σ ell a = (mixedShallowAgentNat σ ell a : ℚ) := by
  by_cases hp : a.phase.val < 3
  · simp only [mixedShallowAgent, mixedShallowAgentNat, if_pos hp]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
    rcases hsafe with hv | hv | hv <;> cases σ <;>
      norm_num [majorityPart, smallValue, pendingMajorityNat, hv]
  · by_cases hm : a.role = .main <;>
      simp [mixedShallowAgent, mixedShallowAgentNat, activeShallowAgent,
        hp, hm, shallowBias_eq_nat]

theorem mixedShallowPositive_eq_nat (σ : Sign) (ell : ℕ) (c : Cfg L K)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    mixedShallowPositive σ ell c = (mixedShallowPositiveNat σ ell c : ℚ) := by
  revert hsafe
  induction c using Multiset.induction_on with
  | empty =>
      intro _
      simp [mixedShallowPositive, mixedShallowPositiveNat, Config.sumOf]
  | cons a c ih =>
      intro hsafe
      have ha := mixedShallowAgent_eq_nat σ ell a
        (hsafe a (Multiset.mem_cons_self a c))
      have hc := ih (fun b hb => hsafe b (Multiset.mem_cons_of_mem hb))
      simpa only [mixedShallowPositive, mixedShallowPositiveNat, Config.sumOf,
        Multiset.map_cons, Multiset.sum_cons, Nat.cast_add] using congrArg₂ (· + ·) ha hc

theorem shallowWeight_split_le (ell j : ℕ) :
    shallowWeight ell (j + 1) + shallowWeight ell (j + 1) ≤
      shallowWeight ell j := by
  by_cases hj : j + 1 ≤ ell
  · have hj' : j ≤ ell := by omega
    simp only [shallowWeight, if_pos hj, if_pos hj']
    exact (scaledWeight_split ell j).ge
  · simp only [shallowWeight, if_neg hj, zero_add]
    exact shallowWeight_nonneg ell j

theorem shallowBias_split_le (σ τ : Sign) (ell j : ℕ) :
    (if τ = σ then shallowWeight ell (j + 1) else 0) +
        (if τ = σ then shallowWeight ell (j + 1) else 0) ≤
      (if τ = σ then shallowWeight ell j else 0) := by
  by_cases hτ : τ = σ
  · simpa only [if_pos hτ] using shallowWeight_split_le ell j
  · simp only [if_neg hτ, zero_add, le_refl]

theorem phase3CancelSplit_shallow_pair_le
    (σ : Sign) (ell : ℕ) (s t : AgentState L K) :
    shallowBias σ ell (phase3CancelSplit L K s t).1.bias +
        shallowBias σ ell (phase3CancelSplit L K s t).2.bias ≤
      shallowBias σ ell s.bias + shallowBias σ ell t.bias := by
  cases hs : s.bias with
  | zero =>
      cases ht : t.bias with
      | zero => simp [phase3CancelSplit, hs, ht, shallowBias]
      | dyadic τ i =>
          by_cases hgt : s.hour.val > i.val
          · simpa [phase3CancelSplit, hs, ht, hgt, shallowBias] using
              shallowBias_split_le σ τ ell i.val
          · simp [phase3CancelSplit, hs, ht, hgt, shallowBias]
  | dyadic τ i =>
      cases ht : t.bias with
      | zero =>
          by_cases hgt : t.hour.val > i.val
          · simpa [phase3CancelSplit, hs, ht, hgt, shallowBias] using
              shallowBias_split_le σ τ ell i.val
          · simp [phase3CancelSplit, hs, ht, hgt, shallowBias]
      | dyadic υ j =>
          have hn := add_nonneg (shallowBias_nonneg σ ell s.bias)
            (shallowBias_nonneg σ ell t.bias)
          cases τ <;> cases υ
          · simp [phase3CancelSplit, hs, ht, shallowBias]
          · by_cases hij : i.val = j.val
            · simpa [phase3CancelSplit, hs, ht, hij, shallowBias] using hn
            · simp [phase3CancelSplit, hs, ht, hij, shallowBias]
          · by_cases hij : i.val = j.val
            · simpa [phase3CancelSplit, hs, ht, hij, shallowBias] using hn
            · simp [phase3CancelSplit, hs, ht, hij, shallowBias]
          · simp [phase3CancelSplit, hs, ht, shallowBias]

theorem Phase3Transition_shallow_pair_le
    (σ : Sign) (ell : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    activeShallowAgent σ ell (Phase3Transition L K s t).1 +
        activeShallowAgent σ ell (Phase3Transition L K s t).2 ≤
      activeShallowAgent σ ell s + activeShallowAgent σ ell t := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · have hroles := Phase5To6FuelProducer.phase3CancelSplit_roles s t
    have hhelper :
        activeShallowAgent σ ell (phase3CancelSplit L K s t).1 +
            activeShallowAgent σ ell (phase3CancelSplit L K s t).2 ≤
          activeShallowAgent σ ell s + activeShallowAgent σ ell t := by
      simpa [activeShallowAgent, hroles.1, hroles.2, hmain.1, hmain.2] using
        phase3CancelSplit_shallow_pair_le σ ell s t
    simpa [Phase3Transition, hmain.1, hmain.2] using hhelper
  · have hroles := Phase5To6FuelProducer.Phase3Transition_roles s t hs ht
    have hbias := Phase5To6FuelProducer.Phase3Transition_biases_of_not_both_main
      s t hs ht hmain
    simp only [activeShallowAgent, hroles.1, hroles.2, hbias.1, hbias.2, le_refl]

theorem phase3CancelSplit_shallow_pair_drop
    (σ : Sign) (ell : ℕ) (s t : AgentState L K) (i : Fin (L + 1))
    (hs : s.bias = .dyadic σ i) (ht : t.bias = .zero)
    (hi : i.val = ell) (hhot : ell < t.hour.val) :
    shallowBias σ ell (phase3CancelSplit L K s t).1.bias +
        shallowBias σ ell (phase3CancelSplit L K s t).2.bias =
      shallowBias σ ell s.bias + shallowBias σ ell t.bias - 1 := by
  have hgt : t.hour.val > i.val := by omega
  simp [phase3CancelSplit, hs, ht, hgt, hhot, shallowBias, shallowWeight,
    scaledWeight, hi]

theorem phase3CancelSplit_shallow_pair_drop_left
    (σ : Sign) (ell : ℕ) (s t : AgentState L K) (i : Fin (L + 1))
    (hs : s.bias = .zero) (ht : t.bias = .dyadic σ i)
    (hi : i.val = ell) (hhot : ell < s.hour.val) :
    shallowBias σ ell (phase3CancelSplit L K s t).1.bias +
        shallowBias σ ell (phase3CancelSplit L K s t).2.bias =
      shallowBias σ ell s.bias + shallowBias σ ell t.bias - 1 := by
  have hgt : s.hour.val > i.val := by omega
  simp [phase3CancelSplit, hs, ht, hgt, hhot, shallowBias, shallowWeight,
    scaledWeight, hi]

theorem initializeAtPhaseThree_shallow_eq
    (σ : Sign) (ell : ℕ) (a : AgentState L K)
    (hpending : a.phase.val < 3)
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3)
    (hsafe : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4) :
    mixedShallowAgent σ ell (initializeAtPhaseThree a) = mixedShallowAgent σ ell a := by
  have hinit : ¬ (initializeAtPhaseThree a).phase.val < 3 := by
    rw [initializeAtPhaseThree_phase]
    omega
  simp only [mixedShallowAgent, if_neg hinit, if_pos hpending]
  by_cases hm : a.role = .main
  · have hc : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4 := by
      omega
    rcases hc with hb | hb | hb <;> cases σ <;>
      norm_num [activeShallowAgent, initializeAtPhaseThree, phaseInit, hm, hb,
        shallowBias, shallowWeight, scaledWeight, smallValue, majorityPart] <;> simp
  · have hr : (initializeAtPhaseThree a).role ≠ .main := by
      simpa only [initializeAtPhaseThree_role] using hm
    have hz : smallValue a.smallBias = 0 := by
      norm_num [smallValue, hcarrier hm]
    rw [activeShallowAgent, if_neg hr, hz]
    cases σ <;> norm_num [majorityPart]

theorem avgFin7_majorityPart_le (σ : Sign) (x y : Fin 7) :
    majorityPart σ (smallValue (avgFin7 x y).1) +
        majorityPart σ (smallValue (avgFin7 x y).2) ≤
      majorityPart σ (smallValue x) + majorityPart σ (smallValue y) := by
  cases σ
  · exact avgFin7_minorityPart_le .neg x y
  · exact avgFin7_minorityPart_le .pos x y

theorem mixedShallowAgent_eq_scaled_atom
    (σ : Sign) (ell : ℕ) (a : AgentState L K) (hphase : 3 ≤ a.phase.val) :
    mixedShallowAgent σ ell a =
      (2 : ℚ) ^ ell * (if a.role = .main then
        match a.bias with
        | .zero => 0
        | .dyadic τ j =>
            if τ = σ ∧ j.val ≤ ell then (2 : ℚ) ^ (-(j.val : ℤ)) else 0
      else 0) := by
  have hp : ¬ a.phase.val < 3 := by omega
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero => simp [mixedShallowAgent, activeShallowAgent, hp, hm, hb, shallowBias]
    | dyadic τ j =>
        by_cases hτ : τ = σ <;> by_cases hj : j.val ≤ ell <;>
          simp [mixedShallowAgent, activeShallowAgent, hp, hm, hb,
            shallowBias, shallowWeight, scaledWeight, hτ, hj,
            zpow_neg, zpow_natCast, div_eq_mul_inv]
  · simp [mixedShallowAgent, activeShallowAgent, hp, hm]

theorem mixedShallowPositive_eq_scaledShallowPositive
    (σ : Sign) (ell : ℕ) (c : InputCfg n)
    (hphase : ∀ a ∈ c, 3 ≤ a.phase.val) :
    mixedShallowPositive σ ell c = scaledShallowPositive σ ell c := by
  classical
  revert hphase
  induction c using Multiset.induction_on with
  | empty =>
      intro _
      simp [mixedShallowPositive, Config.sumOf, scaledShallowPositive]
  | cons a c ih =>
      intro hphase
      have hc := ih (fun b hb => hphase b (Multiset.mem_cons_of_mem hb))
      have hp : ¬ a.phase.val < 3 := by
        have := hphase a (Multiset.mem_cons_self a c)
        omega
      simp only [mixedShallowPositive, Config.sumOf, scaledShallowPositive,
        Multiset.map_cons, Multiset.sum_cons] at hc ⊢
      rw [hc, mul_add]
      congr 1
      by_cases hm : a.role = .main
      · cases hb : a.bias with
        | zero => simp [mixedShallowAgent, activeShallowAgent, hp, hm, hb, shallowBias]
        | dyadic τ j =>
            by_cases hτ : τ = σ <;> by_cases hj : j.val ≤ ell <;>
              simp [mixedShallowAgent, activeShallowAgent, hp, hm, hb,
                shallowBias, shallowWeight, scaledWeight, hτ, hj,
                zpow_neg, zpow_natCast, div_eq_mul_inv]
      · simp [mixedShallowAgent, activeShallowAgent, hp, hm]

/-- A split of the majority at the cutoff removes exactly one unit of X. -/
theorem Phase3Transition_shallow_pair_drop
    (σ : Sign) (ell : ℕ) (s t : AgentState L K) (i : Fin (L + 1))
    (hsm : s.role = .main) (htm : t.role = .main)
    (hs : s.bias = .dyadic σ i) (ht : t.bias = .zero)
    (hi : i.val = ell) (hhot : ell < t.hour.val) :
    activeShallowAgent σ ell (Phase3Transition L K s t).1 +
        activeShallowAgent σ ell (Phase3Transition L K s t).2 =
      activeShallowAgent σ ell s + activeShallowAgent σ ell t - 1 := by
  have hroles := Phase5To6FuelProducer.phase3CancelSplit_roles s t
  have hhelper :
      activeShallowAgent σ ell (phase3CancelSplit L K s t).1 +
          activeShallowAgent σ ell (phase3CancelSplit L K s t).2 =
        activeShallowAgent σ ell s + activeShallowAgent σ ell t - 1 := by
    simpa [activeShallowAgent, hroles.1, hroles.2, hsm, htm] using
      phase3CancelSplit_shallow_pair_drop σ ell s t i hs ht hi hhot
  simpa [Phase3Transition, hsm, htm] using hhelper

theorem transition_shallow_pair_drop
    (σ : Sign) (ell : ℕ) (s t : AgentState L K) (i : Fin (L + 1))
    (hsp : s.phase.val = 3) (htp : t.phase.val = 3)
    (hsm : s.role = .main) (htm : t.role = .main)
    (hs : s.bias = .dyadic σ i) (ht : t.bias = .zero)
    (hi : i.val = ell) (hhot : ell < t.hour.val) :
    mixedShallowAgent σ ell (Transition L K s t).1 +
        mixedShallowAgent σ ell (Transition L K s t).2 =
      mixedShallowAgent σ ell s + mixedShallowAgent σ ell t - 1 := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hsp htp
  have hpa : s.phase = ⟨3, by decide⟩ := Fin.ext hsp
  have hactual : Transition L K s t =
      (finishPhase10Entry L K s (Phase3Transition L K s t).1,
       finishPhase10Entry L K t (Phase3Transition L K s t).2) := by
    unfold Transition
    rw [hepi]
    simp only [hpa]
  have hmono : s.phase.val ≤ (Phase3Transition L K s t).1.phase.val ∧
      t.phase.val ≤ (Phase3Transition L K s t).2.phase.val :=
    Phase3Transition_phase_nondec L K s t
  have hnl : ¬ (Phase3Transition L K s t).1.phase.val < 3 := by omega
  have hnr : ¬ (Phase3Transition L K s t).2.phase.val < 3 := by omega
  have hdispatch := Phase3Transition_shallow_pair_drop σ ell s t i
    hsm htm hs ht hi hhot
  rw [hactual]
  simpa only [mixedShallowAgent, hsp, htp, show ¬ (3 : ℕ) < 3 by omega,
    if_false, finishPhase10Entry_phase_val, if_neg hnl, if_neg hnr,
    activeShallowAgent, finishPhase10Entry_role, finishPhase10Entry_bias] using hdispatch

theorem Phase3Transition_shallow_pair_drop_left
    (σ : Sign) (ell : ℕ) (s t : AgentState L K) (i : Fin (L + 1))
    (hsm : s.role = .main) (htm : t.role = .main)
    (hs : s.bias = .zero) (ht : t.bias = .dyadic σ i)
    (hi : i.val = ell) (hhot : ell < s.hour.val) :
    activeShallowAgent σ ell (Phase3Transition L K s t).1 +
        activeShallowAgent σ ell (Phase3Transition L K s t).2 =
      activeShallowAgent σ ell s + activeShallowAgent σ ell t - 1 := by
  have hroles := Phase5To6FuelProducer.phase3CancelSplit_roles s t
  have hhelper :
      activeShallowAgent σ ell (phase3CancelSplit L K s t).1 +
          activeShallowAgent σ ell (phase3CancelSplit L K s t).2 =
        activeShallowAgent σ ell s + activeShallowAgent σ ell t - 1 := by
    simpa [activeShallowAgent, hroles.1, hroles.2, hsm, htm] using
      phase3CancelSplit_shallow_pair_drop_left σ ell s t i hs ht hi hhot
  simpa [Phase3Transition, hsm, htm] using hhelper

theorem transition_shallow_pair_drop_left
    (σ : Sign) (ell : ℕ) (s t : AgentState L K) (i : Fin (L + 1))
    (hsp : s.phase.val = 3) (htp : t.phase.val = 3)
    (hsm : s.role = .main) (htm : t.role = .main)
    (hs : s.bias = .zero) (ht : t.bias = .dyadic σ i)
    (hi : i.val = ell) (hhot : ell < s.hour.val) :
    mixedShallowAgent σ ell (Transition L K s t).1 +
        mixedShallowAgent σ ell (Transition L K s t).2 =
      mixedShallowAgent σ ell s + mixedShallowAgent σ ell t - 1 := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hsp htp
  have hpa : s.phase = ⟨3, by decide⟩ := Fin.ext hsp
  have hactual : Transition L K s t =
      (finishPhase10Entry L K s (Phase3Transition L K s t).1,
       finishPhase10Entry L K t (Phase3Transition L K s t).2) := by
    unfold Transition
    rw [hepi]
    simp only [hpa]
  have hmono : s.phase.val ≤ (Phase3Transition L K s t).1.phase.val ∧
      t.phase.val ≤ (Phase3Transition L K s t).2.phase.val :=
    Phase3Transition_phase_nondec L K s t
  have hnl : ¬ (Phase3Transition L K s t).1.phase.val < 3 := by omega
  have hnr : ¬ (Phase3Transition L K s t).2.phase.val < 3 := by omega
  have hdispatch := Phase3Transition_shallow_pair_drop_left σ ell s t i
    hsm htm hs ht hi hhot
  rw [hactual]
  simpa only [mixedShallowAgent, hsp, htp, show ¬ (3 : ℕ) < 3 by omega,
    if_false, finishPhase10Entry_phase_val, if_neg hnl, if_neg hnr,
    activeShallowAgent, finishPhase10Entry_role, finishPhase10Entry_bias] using hdispatch

theorem majorityPart_le_abs (σ : Sign) (x : ℚ) :
    majorityPart σ x ≤ |x| := by
  cases σ
  · exact max_le (le_abs_self x) (abs_nonneg x)
  · exact max_le (neg_le_abs x) (abs_nonneg x)

theorem mixedShallowAgent_le_level_phi
    (σ : Sign) (j : Fin (L + 1)) (hj : 1 ≤ j.val)
    (a : AgentState L K) (hphase : a.phase.val ≤ 3) :
    mixedShallowAgent σ j.val a ≤
      AveragingLiveProduct.levelWeight σ j a +
        2 * augmentedAgentPhi j.val a := by
  have hl := AveragingLiveProduct.levelWeight_nonneg σ j a
  have hphi := augmentedAgentPhi_nonneg j.val a
  by_cases hp : a.phase.val < 3
  · have h := scaled_mixedShallowWeight_le_phi j.val hj a
    have heq : smallValue a.smallBias = (AgentState.smallBiasInt a : ℚ) := by
      norm_num [smallValue, AgentState.smallBiasInt]
    have hm := mul_le_mul_of_nonneg_left
      (majorityPart_le_abs σ (smallValue a.smallBias))
      (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ j.val)
    simp only [mixedShallowAgent, if_pos hp]
    simp only [mixedShallowWeight, if_pos hp, ← heq] at h
    linarith
  · have hthree : a.phase.val = 3 := by omega
    by_cases hm : a.role = .main
    · cases hb : a.bias with
      | zero =>
          simp only [mixedShallowAgent, if_neg hp, activeShallowAgent,
            if_pos hm, hb, shallowBias]
          linarith
      | dyadic τ i =>
          by_cases hτ : τ = σ
          · subst τ
            by_cases hlt : i.val < j.val
            · have h := scaled_mixedShallowWeight_le_phi j.val hj a
              have hi : i.val ≤ j.val := by omega
              have heq : mixedShallowAgent σ j.val a =
                  (2 : ℚ) ^ j.val * mixedShallowWeight j.val a := by
                simp [mixedShallowAgent, activeShallowAgent, hp, hm, hb,
                  shallowBias, shallowWeight, scaledWeight, hi,
                  mixedShallowWeight, P3DeterministicAlgebra.agentMassAboveQ, P3DeterministicAlgebra.biasMassAboveQ, hlt,
                  P3DeterministicAlgebra.weightQ, div_eq_mul_inv]
              rw [heq]
              linarith
            · by_cases heq : i = j
              · subst i
                have hw : mixedShallowAgent σ j.val a = 1 := by
                  simp [mixedShallowAgent, activeShallowAgent, hp, hm, hb,
                    shallowBias, shallowWeight, scaledWeight]
                have hlone : AveragingLiveProduct.levelWeight σ j a = 1 := by
                  simp [AveragingLiveProduct.levelWeight, AveragingLiveProduct.AtLevel,
                    hthree, hm, hb]
                rw [hw, hlone]
                linarith
              · have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
                have hi : ¬ i.val ≤ j.val := by omega
                simp only [mixedShallowAgent, if_neg hp, activeShallowAgent,
                  if_pos hm, hb, shallowBias, ↓reduceIte, shallowWeight, if_neg hi]
                linarith
          · simp only [mixedShallowAgent, if_neg hp, activeShallowAgent,
              if_pos hm, hb, shallowBias, if_neg hτ]
            linarith
    · simp only [mixedShallowAgent, if_neg hp, activeShallowAgent, if_neg hm]
      linarith

/-- Pending and shallower majority mass costs at most twice the actual
augmented potential. The counted atoms are precisely active majority agents
at index j, including the phase and role tests used by the pair kernel. -/
theorem mixedShallowPositive_le_level_phi
    (σ : Sign) (j : Fin (L + 1)) (hj : 1 ≤ j.val) (c : Cfg L K)
    (hphase : ∀ a ∈ c, a.phase.val ≤ 3) :
    mixedShallowPositive σ j.val c ≤
      (AveragingLiveProduct.levelCount σ j c : ℚ) + 2 * augmentedPhi j.val c := by
  rw [← AveragingLiveProduct.sum_levelWeight]
  revert hphase
  induction c using Multiset.induction_on with
  | empty =>
      intro _
      simp [mixedShallowPositive, Config.sumOf, augmentedPhi]
  | cons a c ih =>
      intro hphase
      have ha := mixedShallowAgent_le_level_phi σ j hj a
        (hphase a (Multiset.mem_cons_self a c))
      have hc := ih (fun b hb => hphase b (Multiset.mem_cons_of_mem hb))
      simp only [mixedShallowPositive, Config.sumOf, augmentedPhi,
        Multiset.map_cons, Multiset.sum_cons] at hc ⊢
      linarith

theorem mixedShallowPositive_service_floor
    (σ : Sign) (j : Fin (L + 1)) (hj : 1 ≤ j.val) (M : ℕ) (c : Cfg L K)
    (hphase : ∀ a ∈ c, a.phase.val ≤ 3)
    (hphi : augmentedPhi j.val c ≤ (1 / 1000 : ℚ) * M) :
    mixedShallowPositive σ j.val c - (1 / 500 : ℚ) * M ≤
      (AveragingLiveProduct.levelCount σ j c : ℚ) := by
  have h := mixedShallowPositive_le_level_phi σ j hj c hphase
  linarith

theorem fresh_shallow_eq (σ : Sign) (ell : ℕ)
    (a : AgentState L 256) (hfresh : Phase3Pre3.Phase3EntryAgent a)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3) :
    mixedShallowAgent σ ell a =
      (2 : ℚ) ^ ell * majorityPart σ (smallValue a.smallBias) := by
  have hp : ¬ a.phase.val < 3 := by have := hfresh.1; omega
  simp only [mixedShallowAgent, if_neg hp]
  by_cases hm : a.role = .main
  · have hb := Phase3Pre3.main_bias_of_Phase3EntryAgent hfresh hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
    rcases hsafe with hv | hv | hv <;> cases σ <;>
      simp [activeShallowAgent, hm, hb, Phase3Pre3.phase3BiasOfSmallBias, hv,
        shallowBias, shallowWeight, scaledWeight,
        smallValue, majorityPart] <;> (try norm_num) <;> (try ring)
  · cases σ <;> simp [activeShallowAgent, hm, smallValue, hcarrier hm, majorityPart]

theorem pending_shallow_eq (σ : Sign) (ell : ℕ)
    (before after : AgentState L 256)
    (hb : before.phase.val ≤ 2) (ha : after.phase.val ≤ 3)
    (hrole : after.role = before.role) (hsmall : after.smallBias = before.smallBias)
    (hsafe : before.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : before.role ≠ .main → before.smallBias.val = 3)
    (hfresh : after.phase.val = 3 → Phase3Pre3.Phase3EntryAgent after) :
    mixedShallowAgent σ ell after = mixedShallowAgent σ ell before := by
  have hbp : before.phase.val < 3 := by omega
  by_cases hp : after.phase.val = 3
  · have hsa : after.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
      simpa only [hsmall] using hsafe
    have hca : after.role ≠ .main → after.smallBias.val = 3 := by
      intro hm
      have hm' : before.role ≠ .main := by simpa only [hrole] using hm
      simpa only [hsmall] using hcarrier hm'
    rw [fresh_shallow_eq σ ell after (hfresh hp) hsa hca]
    simp only [mixedShallowAgent, if_pos hbp, hsmall]
  · have hap : after.phase.val < 3 := by omega
    simp only [mixedShallowAgent, if_pos hbp, if_pos hap, hsmall]

theorem enterThree_shallow_eq_initialize (σ : Sign) (ell : ℕ)
    (a : AgentState L 256) (hp : 1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    mixedShallowAgent σ ell (enterThree a) =
      mixedShallowAgent σ ell (initializeAtPhaseThree a) := by
  have hcases : a.phase.val = 1 ∨ a.phase.val = 2 := by omega
  rcases hcases with hone | htwo
  · have hlist : (List.range 11).filter
        (fun k => decide (1 < k) && decide (k ≤ 3)) = [2, 3] := by decide
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
    rcases hsafe with hsmall | hsmall | hsmall <;> cases hr : a.role <;>
      simp [enterThree, hone, runInitsBetween, hlist, initializeAtPhaseThree,
        mixedShallowAgent, activeShallowAgent, phaseInit, hr, hsmall]
  · have hlist : (List.range 11).filter
        (fun k => decide (2 < k) && decide (k ≤ 3)) = [3] := by decide
    simp [enterThree, htwo, runInitsBetween, hlist, initializeAtPhaseThree]

theorem enterThree_shallow_eq (σ : Sign) (ell : ℕ)
    (a : AgentState L 256) (hp : 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3) :
    mixedShallowAgent σ ell (enterThree a) = mixedShallowAgent σ ell a := by
  by_cases hthree : a.phase.val = 3
  · have heq : enterThree a = a := by
      unfold enterThree
      rw [hthree, runInitsBetween_self]
      cases a
      simp_all
      exact Fin.ext (by simp [hthree])
    rw [heq]
  · have hsafe' : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
      omega
    rw [enterThree_shallow_eq_initialize σ ell a ⟨hp.1, by omega⟩ hsafe]
    exact initializeAtPhaseThree_shallow_eq σ ell a
      (by omega) hcarrier hsafe'

theorem epidemic_three_shallow_eq (σ : Sign) (ell : ℕ)
    (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hmax : max s.phase.val t.phase.val = 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hscarrier : s.role ≠ .main → s.smallBias.val = 3)
    (htcarrier : t.role ≠ .main → t.smallBias.val = 3) :
    mixedShallowAgent σ ell (phaseEpidemicUpdate L 256 s t).1 =
        mixedShallowAgent σ ell s ∧
      mixedShallowAgent σ ell (phaseEpidemicUpdate L 256 s t).2 =
        mixedShallowAgent σ ell t := by
  have hmaxFin : max s.phase t.phase = ⟨3, by decide⟩ := Fin.ext hmax
  let a := enterThree s
  let b := enterThree t
  have ha : mixedShallowAgent σ ell a = mixedShallowAgent σ ell s :=
    enterThree_shallow_eq σ ell s hs hssafe hscarrier
  have hb : mixedShallowAgent σ ell b = mixedShallowAgent σ ell t :=
    enterThree_shallow_eq σ ell t ht htsafe htcarrier
  have haf := enter_three_fields s hs
  have hbf := enter_three_fields t ht
  have hage : 3 ≤ a.phase.val := by
    show 3 ≤ (enterThree s).phase.val
    rcases haf.2.1 with hp | hp <;> omega
  have hbge : 3 ≤ b.phase.val := by
    show 3 ≤ (enterThree t).phase.val
    rcases hbf.2.1 with hp | hp <;> omega
  have hma : mixedShallowAgent σ ell (phase10EpidemicEntry L 256 s a) =
      mixedShallowAgent σ ell a := by
    have hp := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := 256) s a (by omega)
    simp only [mixedShallowAgent, hp, show ¬ (10 : ℕ) < 3 by omega, if_false,
      if_neg (show ¬ a.phase.val < 3 by omega), activeShallowAgent,
      phase10EpidemicEntry_role, phase10EpidemicEntry_bias]
  have hmb : mixedShallowAgent σ ell (phase10EpidemicEntry L 256 t b) =
      mixedShallowAgent σ ell b := by
    have hp := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := 256) t b (by omega)
    simp only [mixedShallowAgent, hp, show ¬ (10 : ℕ) < 3 by omega, if_false,
      if_neg (show ¬ b.phase.val < 3 by omega), activeShallowAgent,
      phase10EpidemicEntry_role, phase10EpidemicEntry_bias]
  have hepi : phaseEpidemicUpdate L 256 s t =
      if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (a.phase.val = 10 ∨ b.phase.val = 10) then
        (phase10EpidemicEntry L 256 s a, phase10EpidemicEntry L 256 t b)
      else (a, b) := by
    unfold phaseEpidemicUpdate
    rw [hmaxFin]
    rfl
  rw [hepi]
  by_cases hc : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (a.phase.val = 10 ∨ b.phase.val = 10)
  · rw [if_pos hc, hma, hmb]
    exact ⟨ha, hb⟩
  · rw [if_neg hc]
    exact ⟨ha, hb⟩

theorem phase_one_shallow_pair_le (σ : Sign) (ell : ℕ)
    (s t : AgentState L 256) (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hlno : (Transition L 256 s t).1.phase.val ≠ 10)
    (hrno : (Transition L 256 s t).2.phase.val ≠ 10) :
    mixedShallowAgent σ ell (Transition L 256 s t).1 +
        mixedShallowAgent σ ell (Transition L 256 s t).2 ≤
      mixedShallowAgent σ ell s + mixedShallowAgent σ ell t := by
  have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1 s t hs ht
  have hel : (phaseEpidemicUpdate L 256 s t).1.phase.val < 2 := by
    simpa only [hepi] using (show s.phase.val < 2 by omega)
  have hlcap := Transition_left_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
    (L := L) (K := 256) s t hel hlno
  have hrcap := Transition_right_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
    (L := L) (K := 256) s t hel hrno
  have hsl : s.phase.val < 3 := by omega
  have htl : t.phase.val < 3 := by omega
  have hul : (Transition L 256 s t).1.phase.val < 3 := by omega
  have hur : (Transition L 256 s t).2.phase.val < 3 := by omega
  simp only [mixedShallowAgent, if_pos hsl, if_pos htl, if_pos hul, if_pos hur]
  by_cases hm : s.role = .main ∧ t.role = .main
  · have he := Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs ht hm.1 hm.2
    have hscaled := mul_le_mul_of_nonneg_left
      (avgFin7_majorityPart_le σ s.smallBias t.smallBias)
      (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ ell)
    simp only [mul_add] at hscaled
    simp only [he]
    linarith
  · have hpair := PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main s t hm
    have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs
    have hleft : (Transition L 256 s t).1.smallBias = s.smallBias := by
      unfold Transition
      rw [hepi]
      simp only [hsp]
      rw [finishPhase10Entry_smallBias, hpair, clockCounterStep_smallBias]
    have hright : (Transition L 256 s t).2.smallBias = t.smallBias := by
      unfold Transition
      rw [hepi]
      simp only [hsp]
      rw [finishPhase10Entry_smallBias, hpair, clockCounterStep_smallBias]
    rw [hleft, hright]

theorem transition_shallow_le_epidemic (σ : Sign) (ell : ℕ)
    (s t : AgentState L 256)
    (hel : (phaseEpidemicUpdate L 256 s t).1.phase.val = 3)
    (her : (phaseEpidemicUpdate L 256 s t).2.phase.val = 3) :
    mixedShallowAgent σ ell (Transition L 256 s t).1 +
        mixedShallowAgent σ ell (Transition L 256 s t).2 ≤
      mixedShallowAgent σ ell (phaseEpidemicUpdate L 256 s t).1 +
        mixedShallowAgent σ ell (phaseEpidemicUpdate L 256 s t).2 := by
  rcases he : phaseEpidemicUpdate L 256 s t with ⟨a, b⟩
  have ha : a.phase.val = 3 := by simpa only [he] using hel
  have hb : b.phase.val = 3 := by simpa only [he] using her
  have hpa : a.phase = ⟨3, by decide⟩ := Fin.ext ha
  have hactual : Transition L 256 s t =
      (finishPhase10Entry L 256 a (Phase3Transition L 256 a b).1,
       finishPhase10Entry L 256 b (Phase3Transition L 256 a b).2) := by
    unfold Transition
    rw [he]
    simp only [hpa]
  have hmono : a.phase.val ≤ (Phase3Transition L 256 a b).1.phase.val ∧
      b.phase.val ≤ (Phase3Transition L 256 a b).2.phase.val :=
    Phase3Transition_phase_nondec L 256 a b
  have hnl : ¬ (Phase3Transition L 256 a b).1.phase.val < 3 := by omega
  have hnr : ¬ (Phase3Transition L 256 a b).2.phase.val < 3 := by omega
  have hdispatch := Phase3Transition_shallow_pair_le σ ell a b ha hb
  rw [hactual]
  simpa only [mixedShallowAgent, ha, hb, show ¬ (3 : ℕ) < 3 by omega,
    if_false, finishPhase10Entry_phase_val, if_neg hnl, if_neg hnr,
    activeShallowAgent, finishPhase10Entry_role, finishPhase10Entry_bias] using hdispatch

/-- The complete actual dispatcher, including first-seed entry from Phase 2. -/
theorem transition_shallow_pair_le (σ : Sign) (ell : ℕ)
    (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hscarrier : s.role ≠ .main → s.smallBias.val = 3)
    (htcarrier : t.role ≠ .main → t.smallBias.val = 3)
    (hlcap : (Transition L 256 s t).1.phase.val ≤ 3)
    (hrcap : (Transition L 256 s t).2.phase.val ≤ 3) :
    mixedShallowAgent σ ell (Transition L 256 s t).1 +
        mixedShallowAgent σ ell (Transition L 256 s t).2 ≤
      mixedShallowAgent σ ell s + mixedShallowAgent σ ell t := by
  have hlno : (Transition L 256 s t).1.phase.val ≠ 10 := by omega
  have hrno : (Transition L 256 s t).2.phase.val ≠ 10 := by omega
  by_cases hones : s.phase.val = 1 ∧ t.phase.val = 1
  · exact phase_one_shallow_pair_le σ ell s t hones.1 hones.2 hlno hrno
  by_cases hmax : max s.phase.val t.phase.val ≤ 2
  · have hslo : s.phase.val ≤ 2 := (le_max_left _ _).trans hmax
    have htlo : t.phase.val ≤ 2 := (le_max_right _ _).trans hmax
    have hmaxeq : max s.phase.val t.phase.val = 2 := by omega
    have hge := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := 256) s t
    have hdispatch : 2 ≤ (phaseEpidemicUpdate L 256 s t).1.phase.val := by omega
    have hleft : (Transition L 256 s t).1.smallBias = s.smallBias :=
      (Transition_preserves_epidemic_smallBias_left_of_phase_ge_two
        (L := L) (K := 256) s t hdispatch).trans
          (phaseEpidemicUpdate_preserves_smallBias L 256 s t).1
    have hright : (Transition L 256 s t).2.smallBias = t.smallBias :=
      (Transition_preserves_epidemic_smallBias_right_of_dispatch_phase_ge_two
        (L := L) (K := 256) s t hdispatch).trans
          (phaseEpidemicUpdate_preserves_smallBias L 256 s t).2
    have hroles := PhaseTwoSeedProfile.mixed_transition_roles s t
      ⟨hs.1, hslo⟩ ⟨ht.1, htlo⟩ hlcap hrcap
    have hfreshLeft : (Transition L 256 s t).1.phase.val = 3 →
        Phase3Pre3.Phase3EntryAgent (Transition L 256 s t).1 := by
      intro hp
      exact (first_phase_three_pair s t hslo htlo hlno hrno (Or.inl (by omega))).1.1
    have hfreshRight : (Transition L 256 s t).2.phase.val = 3 →
        Phase3Pre3.Phase3EntryAgent (Transition L 256 s t).2 := by
      intro hp
      exact (first_phase_three_pair s t hslo htlo hlno hrno (Or.inr (by omega))).2.1
    rw [pending_shallow_eq σ ell s _ hslo hlcap hroles.1 hleft
        hssafe hscarrier hfreshLeft,
      pending_shallow_eq σ ell t _ htlo hrcap hroles.2 hright
        htsafe htcarrier hfreshRight]
  · have hmaxeq : max s.phase.val t.phase.val = 3 := by omega
    have hphase := epidemic_three_phases_of_success s t hs ht hmaxeq hlno hrno
    have heq := epidemic_three_shallow_eq σ ell s t hs ht hmaxeq
      hssafe htsafe hscarrier htcarrier
    rw [← heq.1, ← heq.2]
    exact transition_shallow_le_epidemic σ ell s t hphase.1 hphase.2

theorem mixedShallowPositive_add_pair (σ : Sign) (ell : ℕ)
    (c : Cfg L 256) (s t : AgentState L 256) :
    mixedShallowPositive σ ell (c + {s, t}) =
      mixedShallowPositive σ ell c +
        (mixedShallowAgent σ ell s + mixedShallowAgent σ ell t) := by
  simp [mixedShallowPositive, Config.sumOf, Multiset.map_add, Multiset.sum_add,
    add_assoc, add_left_comm]

theorem mixedShallowPositive_stepOrSelf (σ : Sign) (ell : ℕ)
    (c : Cfg L 256) (s t : AgentState L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3)
    (hcap : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      a.phase.val ≤ 3) :
    mixedShallowPositive σ ell (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) ≤
      mixedShallowPositive σ ell c := by
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
    have hpair := transition_shallow_pair_le σ ell s t
      (hrange s hs) (hrange t ht) (hsafe s hs) (hsafe t ht)
      (hcarrier s hs) (hcarrier t ht) (hcap _ hlmem) (hcap _ hrmem)
    have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L 256)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
    rw [hstep, mixedShallowPositive_add_pair]
    conv_rhs => rw [hsplit]
    rw [mixedShallowPositive_add_pair]
    exact add_le_add le_rfl hpair
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem mixedShallowPositive_draw (σ : Sign) (ell : ℕ)
    (c : Cfg L 256) (d : Draw L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3)
    (hcap : ∀ a ∈ applyDraw c d, a.phase.val ≤ 3) :
    mixedShallowPositive σ ell (applyDraw c d) ≤ mixedShallowPositive σ ell c := by
  cases d with
  | none => exact le_rfl
  | some p =>
      exact mixedShallowPositive_stepOrSelf σ ell c p.1.1 p.2.1
        hrange hsafe hcarrier hcap

theorem mixedShallowPositive_trace_le (σ : Sign) (ell : ℕ)
    (init : Cfg L 256) (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    mixedShallowPositive σ ell (trace init ω t) ≤
      mixedShallowPositive σ ell (trace init ω s) := by
  revert hrange hsafe hcarrier
  induction t, hst using Nat.le_induction with
  | base =>
      intro _ _ _
      exact le_rfl
  | succ t hst ih =>
      intro hrange hsafe hcarrier
      have hprev := ih
        (fun u hsu hut => hrange u hsu (by omega))
        (fun u hsu hut => hsafe u hsu (by omega))
        (fun u hsu hut => hcarrier u hsu (by omega))
      have hnext : mixedShallowPositive σ ell (trace init ω (t + 1)) ≤
          mixedShallowPositive σ ell (trace init ω t) := by
        rw [TimeTheorem.trace_succ]
        apply mixedShallowPositive_draw σ ell _ (ω (t + 1))
          (hrange t hst (by omega)) (hsafe t hst (by omega))
          (hcarrier t hst (by omega))
        intro a ha
        have ha' : a ∈ trace init ω (t + 1) := by
          simpa only [TimeTheorem.trace_succ] using ha
        exact (hrange (t + 1) (by omega) le_rfl a ha').2
      exact hnext.trans hprev


theorem mixedShallowPositive_step_split_drop
    (σ : Sign) (ell : ℕ) (c : Cfg L 256) (s t : AgentState L 256)
    (i : Fin (L + 1)) (happ : Protocol.Applicable c s t)
    (hsp : s.phase.val = 3) (htp : t.phase.val = 3)
    (hsm : s.role = .main) (htm : t.role = .main)
    (hs : s.bias = .dyadic σ i) (ht : t.bias = .zero)
    (hi : i.val = ell) (hhot : ell < t.hour.val) :
    mixedShallowPositive σ ell
        (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 =
      mixedShallowPositive σ ell c := by
  classical
  have hstep : Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
      c - {s, t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ] <;> rfl
  have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L 256)) := by
    rw [Multiset.sub_add_cancel
      (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
  have hpair := transition_shallow_pair_drop σ ell s t i
    hsp htp hsm htm hs ht hi hhot
  rw [hstep, mixedShallowPositive_add_pair]
  conv_rhs => rw [hsplit]
  rw [mixedShallowPositive_add_pair]
  linarith

theorem mixedShallowPositiveNat_step_split_drop
    (σ : Sign) (ell : ℕ) (c : Cfg L 256) (s t : AgentState L 256)
    (i : Fin (L + 1)) (happ : Protocol.Applicable c s t)
    (hsp : s.phase.val = 3) (htp : t.phase.val = 3)
    (hsm : s.role = .main) (htm : t.role = .main)
    (hs : s.bias = .dyadic σ i) (ht : t.bias = .zero)
    (hi : i.val = ell) (hhot : ell < t.hour.val)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hnextsafe : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    mixedShallowPositiveNat σ ell
        (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 =
      mixedShallowPositiveNat σ ell c := by
  have h := mixedShallowPositive_step_split_drop σ ell c s t i happ
    hsp htp hsm htm hs ht hi hhot
  rw [mixedShallowPositive_eq_nat σ ell _ hnextsafe,
    mixedShallowPositive_eq_nat σ ell _ hsafe] at h
  exact_mod_cast h

theorem mixedShallowPositive_step_split_drop_left
    (σ : Sign) (ell : ℕ) (c : Cfg L 256) (s t : AgentState L 256)
    (i : Fin (L + 1)) (happ : Protocol.Applicable c s t)
    (hsp : s.phase.val = 3) (htp : t.phase.val = 3)
    (hsm : s.role = .main) (htm : t.role = .main)
    (hs : s.bias = .zero) (ht : t.bias = .dyadic σ i)
    (hi : i.val = ell) (hhot : ell < s.hour.val) :
    mixedShallowPositive σ ell
        (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 =
      mixedShallowPositive σ ell c := by
  classical
  have hstep : Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
      c - {s, t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ] <;> rfl
  have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L 256)) := by
    rw [Multiset.sub_add_cancel
      (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
  have hpair := transition_shallow_pair_drop_left σ ell s t i
    hsp htp hsm htm hs ht hi hhot
  rw [hstep, mixedShallowPositive_add_pair]
  conv_rhs => rw [hsplit]
  rw [mixedShallowPositive_add_pair]
  linarith

theorem mixedShallowPositiveNat_step_split_drop_left
    (σ : Sign) (ell : ℕ) (c : Cfg L 256) (s t : AgentState L 256)
    (i : Fin (L + 1)) (happ : Protocol.Applicable c s t)
    (hsp : s.phase.val = 3) (htp : t.phase.val = 3)
    (hsm : s.role = .main) (htm : t.role = .main)
    (hs : s.bias = .zero) (ht : t.bias = .dyadic σ i)
    (hi : i.val = ell) (hhot : ell < s.hour.val)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hnextsafe : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    mixedShallowPositiveNat σ ell
        (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 =
      mixedShallowPositiveNat σ ell c := by
  have h := mixedShallowPositive_step_split_drop_left σ ell c s t i happ
    hsp htp hsm htm hs ht hi hhot
  rw [mixedShallowPositive_eq_nat σ ell _ hnextsafe,
    mixedShallowPositive_eq_nat σ ell _ hsafe] at h
  exact_mod_cast h

theorem mixedShallowPositiveNat_trace_le (σ : Sign) (ell : ℕ)
    (init : Cfg L 256) (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    mixedShallowPositiveNat σ ell (trace init ω t) ≤
      mixedShallowPositiveNat σ ell (trace init ω s) := by
  have h := mixedShallowPositive_trace_le σ ell init ω s t hst hrange hsafe hcarrier
  rw [mixedShallowPositive_eq_nat σ ell _ (hsafe t hst le_rfl),
    mixedShallowPositive_eq_nat σ ell _ (hsafe s le_rfl hst)] at h
  exact_mod_cast h

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end

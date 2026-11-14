-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingDebtAlgebra.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingPendingCredit
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingMixedPotentialTransitions

/-!
# Two-sided mass debt with a changing zero population

The nonnegative coefficients a,b pay for cancellation-created zeros when
a+b >= 2^h. This includes the changing-zero fuel, and both terminal X/Y
debts. No Main activation-completion premise is used.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingDebtAlgebra

open TimeTheorem P3DeterministicAlgebra AveragingMixedAlgebra AveragingMixedLedgers
open AveragingPendingCredit PhaseTwoSparse

variable {L K : ℕ}

def massBlend (a b x : ℚ) : ℚ :=
  a * max x 0 + b * max (-x) 0

def agentDebt (a b : ℚ) (h : ℕ) (s : AgentState L K) : ℚ :=
  (inactiveMainWeight s : ℚ) + (lowHourZeroWeight h s : ℚ) +
    massBlend a b (prePhase4Mass s)

def totalDebt (a b : ℚ) (h : ℕ) (c : Cfg L K) : ℚ :=
  Config.sumOf (agentDebt a b h) c

def activeDebt (a b : ℚ) (h : ℕ) (s : AgentState L K) : ℚ :=
  (if s.bias = .zero ∧ s.hour.val < h then 1 else 0) +
    massBlend a b (Bias.toRat s.bias)

theorem massBlend_nonneg (a b x : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ massBlend a b x := by
  exact add_nonneg (mul_nonneg ha (le_max_right _ _))
    (mul_nonneg hb (le_max_right _ _))

theorem massBlend_zero (a b : ℚ) : massBlend a b 0 = 0 := by
  simp [massBlend]

theorem massBlend_bias_zero (a b : ℚ) :
    massBlend a b (Bias.toRat (Bias.zero : Bias L)) = 0 :=
  massBlend_zero a b

theorem massBlend_pos (a b x : ℚ) (hx : 0 ≤ x) :
    massBlend a b x = a * x := by
  simp [massBlend, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]

theorem massBlend_neg (a b x : ℚ) (hx : 0 ≤ x) :
    massBlend a b (-x) = b * x := by
  simp [massBlend, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]

theorem massBlend_pair_le (a b x y u v : ℚ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : u + v = x + y)
    (habs : |u| + |v| ≤ |x| + |y|) :
    massBlend a b u + massBlend a b v ≤
      massBlend a b x + massBlend a b y := by
  have hp := minorityPart_pair_le .neg x y u v hsum habs
  have hn := minorityPart_pair_le .pos x y u v hsum habs
  have hpa := mul_le_mul_of_nonneg_left hp ha
  have hnb := mul_le_mul_of_nonneg_left hn hb
  simp only [minorityPart] at hpa hnb
  unfold massBlend
  nlinarith only [hpa, hnb]

theorem massBlend_dyadic_pos (a b : ℚ) (i : Fin (L + 1)) :
    massBlend a b (Bias.toRat (.dyadic .pos i)) = a * weightQ i := by
  simpa [Bias.toRat, weightQ] using massBlend_pos a b (weightQ i) (weightQ_nonneg i)

theorem massBlend_dyadic_neg (a b : ℚ) (i : Fin (L + 1)) :
    massBlend a b (Bias.toRat (.dyadic .neg i)) = b * weightQ i := by
  simpa [Bias.toRat, weightQ, neg_div] using
    massBlend_neg a b (weightQ i) (weightQ_nonneg i)

theorem massBlend_dyadic_split (a b : ℚ) (sgn : Sign)
    (i : Fin (L + 1)) (hi : i.val < L) :
    let j : Fin (L + 1) := ⟨i.val + 1, by omega⟩
    massBlend a b (Bias.toRat (.dyadic sgn i)) =
      massBlend a b (Bias.toRat (.dyadic sgn j)) +
        massBlend a b (Bias.toRat (.dyadic sgn j)) := by
  dsimp only
  cases sgn
  · rw [massBlend_dyadic_pos, massBlend_dyadic_pos]
    unfold weightQ
    field_simp [pow_succ, pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)] <;> ring
  · rw [massBlend_dyadic_neg, massBlend_dyadic_neg]
    unfold weightQ
    field_simp [pow_succ, pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)] <;> ring

theorem cancellation_pays_two (a b : ℚ) (h : ℕ)
    (hpay : (2 : ℚ) ^ h ≤ a + b)
    (i : Fin (L + 1)) (hi : i.val < h) :
    2 ≤ (a + b) * weightQ i := by
  have hpower : 2 * (2 : ℚ) ^ i.val ≤ (2 : ℚ) ^ h := by
    simpa [pow_succ, mul_comm] using
      (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
        (show i.val + 1 ≤ h by omega))
  have hdiv : (2 : ℚ) ≤ (a + b) / (2 : ℚ) ^ i.val :=
    (le_div_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ i.val)).2
      (hpower.trans hpay)
  simpa [weightQ, mul_div_assoc] using hdiv

theorem activeDebt_cancel_pair_le (a b : ℚ) (h : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hpay : (2 : ℚ) ^ h ≤ a + b)
    (s t : AgentState L K) (i : Fin (L + 1))
    (hs : s.bias = .dyadic .pos i) (ht : t.bias = .dyadic .neg i) :
    activeDebt a b h { s with bias := .zero, hour := i } +
        activeDebt a b h { t with bias := .zero, hour := i } ≤
      activeDebt a b h s + activeDebt a b h t := by
  have hweight := weightQ_nonneg i
  have hdebt : 0 ≤ (a + b) * weightQ i := mul_nonneg (add_nonneg ha hb) hweight
  by_cases hi : i.val < h
  · have hpaid := cancellation_pays_two a b h hpay i hi
    simpa [activeDebt, hs, ht, hi, massBlend_bias_zero,
      massBlend_dyadic_pos, massBlend_dyadic_neg, add_mul, one_add_one_eq_two] using hpaid
  · simpa [activeDebt, hs, ht, hi, massBlend_bias_zero,
      massBlend_dyadic_pos, massBlend_dyadic_neg, add_mul] using hdebt

theorem activeDebt_split_left (a b : ℚ) (h : ℕ)
    (s t : AgentState L K) (sgn : Sign) (i : Fin (L + 1))
    (hs : s.bias = .zero) (ht : t.bias = .dyadic sgn i)
    (hgt : i.val < s.hour.val) :
    activeDebt a b h (phase3CancelSplit L K s t).1 +
        activeDebt a b h (phase3CancelSplit L K s t).2 +
        (if s.hour.val < h then (1 : ℚ) else 0) =
      activeDebt a b h s + activeDebt a b h t := by
  have hi : i.val < L := by have := s.hour.isLt; omega
  have hsplit := massBlend_dyadic_split a b sgn i hi
  dsimp only at hsplit
  have he := congrArg
    (fun z : ℚ => z + (if s.hour.val < h then (1 : ℚ) else 0)) hsplit.symm
  simpa [phase3CancelSplit, hs, ht, hgt, activeDebt, massBlend_bias_zero,
    add_assoc, add_comm, add_left_comm] using he

theorem activeDebt_split_right (a b : ℚ) (h : ℕ)
    (s t : AgentState L K) (sgn : Sign) (i : Fin (L + 1))
    (hs : s.bias = .dyadic sgn i) (ht : t.bias = .zero)
    (hgt : i.val < t.hour.val) :
    activeDebt a b h (phase3CancelSplit L K s t).1 +
        activeDebt a b h (phase3CancelSplit L K s t).2 +
        (if t.hour.val < h then (1 : ℚ) else 0) =
      activeDebt a b h s + activeDebt a b h t := by
  have hi : i.val < L := by have := t.hour.isLt; omega
  have hsplit := massBlend_dyadic_split a b sgn i hi
  dsimp only at hsplit
  have he := congrArg
    (fun z : ℚ => z + (if t.hour.val < h then (1 : ℚ) else 0)) hsplit.symm
  simpa [phase3CancelSplit, hs, ht, hgt, activeDebt, massBlend_bias_zero,
    add_assoc, add_comm, add_left_comm] using he

theorem activeDebt_cancelSplit_pair_le (a b : ℚ) (h : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hpay : (2 : ℚ) ^ h ≤ a + b)
    (s t : AgentState L K) :
    activeDebt a b h (phase3CancelSplit L K s t).1 +
        activeDebt a b h (phase3CancelSplit L K s t).2 ≤
      activeDebt a b h s + activeDebt a b h t := by
  cases hs : s.bias with
  | zero =>
      cases ht : t.bias with
      | zero => simp [phase3CancelSplit, hs, ht]
      | dyadic sgn i =>
          by_cases hgt : i.val < s.hour.val
          · have he := activeDebt_split_left a b h s t sgn i hs ht hgt
            have hn : (0 : ℚ) ≤ if s.hour.val < h then 1 else 0 := by
              split_ifs <;> norm_num
            linarith
          · simp [phase3CancelSplit, hs, ht, hgt]
  | dyadic sgn i =>
      cases ht : t.bias with
      | zero =>
          by_cases hgt : i.val < t.hour.val
          · have he := activeDebt_split_right a b h s t sgn i hs ht hgt
            have hn : (0 : ℚ) ≤ if t.hour.val < h then 1 else 0 := by
              split_ifs <;> norm_num
            linarith
          · simp [phase3CancelSplit, hs, ht, hgt]
      | dyadic tau j =>
          cases sgn <;> cases tau
          · simp [phase3CancelSplit, hs, ht]
          · by_cases hij : i.val = j.val
            · have he : i = j := Fin.ext hij
              subst j
              simpa [phase3CancelSplit, hs, ht] using
                activeDebt_cancel_pair_le a b h ha hb hpay s t i hs ht
            · simp [phase3CancelSplit, hs, ht, hij]
          · by_cases hij : i.val = j.val
            · have he : i = j := Fin.ext hij
              subst j
              simpa [phase3CancelSplit, hs, ht, add_comm] using
                activeDebt_cancel_pair_le a b h ha hb hpay t s i ht hs
            · simp [phase3CancelSplit, hs, ht, hij]
          · simp [phase3CancelSplit, hs, ht]

theorem agentDebt_nonneg (a b : ℚ) (h : ℕ) (s : AgentState L K)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ agentDebt a b h s := by
  exact add_nonneg (by positivity) (massBlend_nonneg a b _ ha hb)

theorem agentDebt_eq_active (a b : ℚ) (h : ℕ) (s : AgentState L K)
    (hm : s.role = .main) (hp : 3 ≤ s.phase.val) :
    agentDebt a b h s = activeDebt a b h s := by
  have hnp : ¬ s.phase.val < 3 := by omega
  simp [agentDebt, activeDebt, inactiveMainWeight, lowHourZeroWeight,
    prePhase4Mass, hm, hnp]

theorem agentDebt_eq_pending (a b : ℚ) (h : ℕ) (s : AgentState L K)
    (hp : s.phase.val < 3) :
    agentDebt a b h s =
      (if s.role = .main then (1 : ℚ) else 0) +
        massBlend a b (smallValue s.smallBias) := by
  simp [agentDebt, inactiveMainWeight, lowHourZeroWeight, hp,
    prePhase4Mass, smallValue, AgentState.smallBiasInt]

theorem agentDebt_of_active_nonmain (a b : ℚ) (h : ℕ)
    (s : AgentState L K) (hm : s.role ≠ .main) (hp : 3 ≤ s.phase.val) :
    agentDebt a b h s = massBlend a b (Bias.toRat s.bias) := by
  simp [agentDebt, inactiveMainWeight, lowHourZeroWeight, hm,
    prePhase4Mass, show ¬ s.phase.val < 3 by omega]

theorem fresh_agentDebt_le_pending (a b : ℚ) (h : ℕ)
    (s : AgentState L K) (hfresh : Phase3Pre3.Phase3EntryAgent s)
    (hsafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : s.role ≠ .main → s.smallBias.val = 3) :
    agentDebt a b h s ≤
      (if s.role = .main then (1 : ℚ) else 0) +
        massBlend a b (smallValue s.smallBias) := by
  have hp := hfresh.1
  by_cases hm : s.role = .main
  · have hb := Phase3Pre3.main_bias_of_Phase3EntryAgent hfresh hm
    have hh := Phase3Pre3.main_hour_zero_of_Phase3EntryAgent hfresh hm
    have hd := agentDebt_eq_active a b h s hm (by omega : 3 ≤ s.phase.val)
    rw [hd]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
    rcases hsafe with hv | hv | hv <;>
      simp [activeDebt, hb, hh, Phase3Pre3.phase3BiasOfSmallBias,
        hm, hv, smallValue, Bias.toRat, massBlend] <;>
      first | (split_ifs <;> norm_num) | norm_num
  · have hb := Phase3Pre3.nonMain_bias_zero_of_Phase3EntryAgent hfresh hm
    have hd := agentDebt_of_active_nonmain a b h s hm (by omega : 3 ≤ s.phase.val)
    rw [hd]
    simp [hm, hb, hcarrier hm, smallValue, Bias.toRat, massBlend]

theorem totalDebt_eq_counts_and_masses (a b : ℚ) (h : ℕ) (c : Cfg L K) :
    totalDebt a b h c =
      (inactiveMainCount c : ℚ) + (lowHourZeroCount h c : ℚ) +
        a * mixedPositiveMass c + b * mixedNegativeMass c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [totalDebt, Config.sumOf, inactiveMainCount, lowHourZeroCount,
        mixedPositiveMass, mixedNegativeMass]
  | cons s c ih =>
      simp only [totalDebt, Config.sumOf, inactiveMainCount, lowHourZeroCount,
        mixedPositiveMass, mixedNegativeMass, Multiset.map_cons,
        Multiset.sum_cons, Nat.cast_add] at ih ⊢
      simp only [agentDebt, massBlend] at ih ⊢
      linarith

theorem totalDebt_eq_changingZeroFuel (h : ℕ) (c : Cfg L K)
    (hcarrier : ∀ s ∈ c, s.role ≠ .main → prePhase4Mass s = 0) :
    totalDebt ((2 : ℚ) ^ h) ((2 : ℚ) ^ h) h c = changingZeroFuel h c := by
  rw [totalDebt_eq_counts_and_masses, changingZeroFuel_eq h c hcarrier]
  have he := (mixedMassIdentities c).2
  rw [← he]
  ring

end Ripple.PopulationProtocol.ExactMajority.AveragingDebtAlgebra

end

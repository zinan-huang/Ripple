import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCreditTransitions
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingFirstExit

/-!
# Configuration capacity of protected credit

This file connects the existing actual-transition credit to the literal
`StageEventSpec.bandCount`. It also transports that bound to the first
Phase-4 seed. It does not produce the terminal credit margin or assert a
probability estimate.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingTerminalReadout

open TimeTheorem StageEventSpec AveragingCreditTransitions

variable {L K n : ℕ}

def InBand (σ : Sign) (ell width : ℕ) (a : AgentState L K) : Prop :=
  a.role = .main ∧
    ∃ j, a.bias = Bias.dyadic σ j ∧ ell ≤ j.val ∧ j.val ≤ ell + width

noncomputable def mainIndicator (a : AgentState L K) : ℚ := by
  classical
  exact if a.role = .main then 1 else 0

noncomputable def bandIndicator (σ : Sign) (ell width : ℕ)
    (a : AgentState L K) : ℚ := by
  classical
  exact if InBand σ ell width a then 1 else 0

theorem scaledWeight_le_half_of_lt {k j : ℕ} (hkj : k < j) :
    scaledWeight k j ≤ (1 / 2 : ℚ) := by
  have hpow : (2 : ℚ) ^ (k + 1) ≤ (2 : ℚ) ^ j :=
    pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega)
  rw [pow_succ] at hpow
  unfold scaledWeight
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ j)).2
  linarith

/-- Every Main outside the protected band has credit at most one half;
inside the band its credit is exactly one. Minority debt only helps this
upper bound. -/
theorem agentCredit_capacity (σ : Sign) (ell width : ℕ)
    (a : AgentState L K) :
    2 * agentCredit σ ell (ell + width) a ≤
      mainIndicator a + bandIndicator σ ell width a := by
  classical
  by_cases hm : a.role = .main
  · by_cases hband : InBand σ ell width a
    · obtain ⟨_, j, hb, hlo, hhi⟩ := hband
      have hband' : InBand σ ell width a := ⟨hm, j, hb, hlo, hhi⟩
      have hw := protectedWeight_eq_one_of_mem_band ell (ell + width) j.val hlo hhi
      have hc : agentCredit σ ell (ell + width) a = 1 := by
        simp [agentCredit, hm, biasCredit, hb, signedCredit, hw]
      norm_num [mainIndicator, hm, bandIndicator, hband', hc]
    · have hhalf : agentCredit σ ell (ell + width) a ≤ (1 / 2 : ℚ) := by
        cases hb : a.bias with
        | zero =>
            norm_num [agentCredit, hm, biasCredit, hb]
        | dyadic τ j =>
            by_cases hsign : τ = σ
            · subst τ
              by_cases hlo : j.val < ell
              · norm_num [agentCredit, hm, biasCredit, hb, signedCredit,
                  protectedWeight, hlo]
              · have hhi : ell + width < j.val := by
                  by_contra h
                  exact hband ⟨hm, j, hb, by omega, by omega⟩
                have hw : protectedWeight ell (ell + width) j.val ≤ (1 / 2 : ℚ) :=
                  (protectedWeight_le_scaled ell (ell + width) j.val).trans
                    (scaledWeight_le_half_of_lt hhi)
                simpa [agentCredit, hm, biasCredit, hb, signedCredit] using hw
            · have hw := scaledWeight_nonneg (ell + width) j.val
              simp only [agentCredit, if_pos hm, hb, biasCredit, signedCredit,
                if_neg hsign]
              linarith
      simp only [mainIndicator, if_pos hm, bandIndicator, if_neg hband]
      linarith
  · have hband : ¬ InBand σ ell width a := fun h => hm h.1
    simp [agentCredit, hm, mainIndicator, bandIndicator, hband]

theorem sumOf_indicator_eq_countP {α : Type*} (P : α → Prop)
    [DecidablePred P] (c : Multiset α) :
    Config.sumOf (fun a => if P a then (1 : ℚ) else 0) c =
      (c.countP P : ℚ) := by
  induction c using Multiset.induction_on with
  | empty => simp [Config.sumOf]
  | cons a c ih =>
      by_cases ha : P a <;>
        simp [Config.sumOf, Multiset.countP_cons, ha] at ih ⊢ <;>
        linarith

theorem sum_mainIndicator (c : InputCfg n) :
    Config.sumOf mainIndicator c = (timeMainCount c : ℚ) := by
  classical
  simpa only [mainIndicator, timeMainCount,
    AveragingEventInterface.countP_classical] using
    sumOf_indicator_eq_countP (fun a => a.role = Role.main) c

theorem sum_bandIndicator (σ : Sign) (ell width : ℕ) (c : InputCfg n) :
    Config.sumOf (bandIndicator σ ell width) c =
      (bandCount σ ell width c : ℚ) := by
  classical
  simpa only [bandIndicator, InBand, bandCount,
    AveragingEventInterface.countP_classical] using
    sumOf_indicator_eq_countP (InBand σ ell width) c

/-- The capacity bound is about the actual configuration, not supplied
scalar values for the Main and band counts. -/
theorem totalCredit_capacity (σ : Sign) (ell width : ℕ) (c : InputCfg n) :
    2 * totalCredit σ ell (ell + width) c ≤
      (timeMainCount c : ℚ) + (bandCount σ ell width c : ℚ) := by
  have hraw :
      2 * totalCredit σ ell (ell + width) c ≤
        Config.sumOf mainIndicator c +
          Config.sumOf (bandIndicator σ ell width) c := by
    induction c using Multiset.induction_on with
    | empty => simp [totalCredit, Config.sumOf]
    | cons a c ih =>
        have ha := agentCredit_capacity σ ell width a
        simp only [totalCredit, Config.sumOf, Multiset.map_cons,
          Multiset.sum_cons] at ih ⊢
        linarith
  simpa only [sum_mainIndicator, sum_bandIndicator] using hraw

theorem protected_band_of_credit (σ : Sign) (ell M : ℕ) (c : InputCfg n)
    (hcount : timeMainCount c = M)
    (hcredit : (601 / 625 : ℚ) * (M : ℚ) ≤ totalCredit σ ell (ell + 2) c) :
    9232 * M ≤ 10000 * bandCount σ ell 2 c := by
  have hcap := totalCredit_capacity σ ell 2 c
  rw [hcount] at hcap
  have hq : (9232 : ℚ) * (M : ℚ) ≤
      10000 * (bandCount σ ell 2 c : ℚ) := by linarith
  exact_mod_cast hq

theorem required_band_of_credit (σ : Sign) (ell M : ℕ) (c : InputCfg n)
    (hcount : timeMainCount c = M)
    (hcredit : (601 / 625 : ℚ) * (M : ℚ) ≤ totalCredit σ ell (ell + 2) c) :
    92 * M ≤ 100 * bandCount σ ell 2 c := by
  have h := protected_band_of_credit σ ell M c hcount hcredit
  omega

/-- The clock-history count fields stop strictly before rho. This lemma
justifies the additional final interaction. -/
theorem mainCount_at_first_exit {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init}
    (h : ClockHistory init ω S T ρ w) :
    timeMainCount (trace init ω ρ) = timeMainCount (trace init ω S) := by
  have hST := AveragingEventInterface.clockHistory_seed_lt_exit h
  calc
    timeMainCount (trace init ω ρ) =
        timeMainCount (trace init ω (ρ - 1)) :=
      AveragingFirstExit.mainCount_first_exit_step h
    _ = timeMainCount (trace init ω S) :=
      h.main_count (ρ - 1) (by omega) (by omega)

/-- A produced credit margin at any initialized checkpoint persists to the
first exit and gives the stronger .9232 band there. -/
theorem protected_band_at_first_exit {init : InputCfg n} {ω : InputLog n}
    {S T ρ u ell : ℕ} {w : ClockTimes init} (σ : Sign)
    (h : ClockHistory init ω S T ρ w) (hTu : T ≤ u) (huρ : u ≤ ρ)
    (hcredit : (601 / 625 : ℚ) * (timeMainCount (trace init ω S) : ℚ) ≤
      totalCredit σ ell (ell + 2) (trace init ω u)) :
    9232 * timeMainCount (trace init ω S) ≤
      10000 * bandCount σ ell 2 (trace init ω ρ) := by
  have hmono := totalCredit_trace_mono σ ell (ell + 2) init ω huρ
    (by
      intro v huv hvρ a ha
      exact Or.inl (h.all_three v (by omega) hvρ a ha))
  exact protected_band_of_credit σ ell _ _ (mainCount_at_first_exit h)
    (hcredit.trans hmono)

theorem required_band_at_first_exit {init : InputCfg n} {ω : InputLog n}
    {S T ρ u ell : ℕ} {w : ClockTimes init} (σ : Sign)
    (h : ClockHistory init ω S T ρ w) (hTu : T ≤ u) (huρ : u ≤ ρ)
    (hcredit : (601 / 625 : ℚ) * (timeMainCount (trace init ω S) : ℚ) ≤
      totalCredit σ ell (ell + 2) (trace init ω u)) :
    92 * timeMainCount (trace init ω S) ≤
      100 * bandCount σ ell 2 (trace init ω ρ) := by
  have hb := protected_band_at_first_exit σ h hTu huρ hcredit
  omega

end Ripple.PopulationProtocol.ExactMajority.AveragingTerminalReadout

end

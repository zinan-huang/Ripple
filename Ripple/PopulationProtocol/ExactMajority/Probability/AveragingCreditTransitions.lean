import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5To6FuelProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.TimeTheorem
import Mathlib.Tactic

/-!
# Protected-credit transport in the actual Phase-3/4 window

The majority weight is zero below ell and min(1, 2^k / 2^j) elsewhere.
Minority weight is -2^k / 2^j. Equal-index cancellation cannot decrease
credit, majority splitting cannot decrease it, and minority splitting
preserves it. The initialized Phase-3 premises are retained when passing
from the helper to the real dispatcher.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingCreditTransitions

open TimeTheorem

variable {L K : ℕ}

def scaledWeight (k j : ℕ) : ℚ :=
  (2 : ℚ) ^ k / (2 : ℚ) ^ j

def protectedWeight (ell k j : ℕ) : ℚ :=
  if j < ell then 0 else min 1 (scaledWeight k j)

theorem scaledWeight_nonneg (k j : ℕ) : 0 ≤ scaledWeight k j := by
  unfold scaledWeight
  positivity

theorem scaledWeight_split (k j : ℕ) :
    scaledWeight k j = scaledWeight k (j + 1) + scaledWeight k (j + 1) := by
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  unfold scaledWeight
  field_simp [pow_succ, pow_ne_zero j htwo] <;> ring

theorem protectedWeight_nonneg (ell k j : ℕ) :
    0 ≤ protectedWeight ell k j := by
  unfold protectedWeight
  split_ifs
  · exact le_rfl
  · exact le_min (by norm_num) (scaledWeight_nonneg k j)

theorem protectedWeight_le_scaled (ell k j : ℕ) :
    protectedWeight ell k j ≤ scaledWeight k j := by
  unfold protectedWeight
  split_ifs
  · exact scaledWeight_nonneg k j
  · exact min_le_right _ _

theorem protectedWeight_le_one (ell k j : ℕ) :
    protectedWeight ell k j ≤ 1 := by
  unfold protectedWeight
  split_ifs
  · norm_num
  · exact min_le_left _ _

theorem protectedWeight_eq_zero_of_lt (ell k j : ℕ) (hj : j < ell) :
    protectedWeight ell k j = 0 := by
  simp only [protectedWeight, if_pos hj]

theorem protectedWeight_eq_one_of_mem_band (ell k j : ℕ)
    (hlo : ell ≤ j) (hhi : j ≤ k) :
    protectedWeight ell k j = 1 := by
  unfold protectedWeight
  rw [if_neg (Nat.not_lt.mpr hlo)]
  apply min_eq_left
  unfold scaledWeight
  apply (one_le_div (by positivity : (0 : ℚ) < (2 : ℚ) ^ j)).2
  exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hhi

/-- This split inequality needs no relation between ell and k. -/
theorem protectedWeight_split (ell k j : ℕ) :
    protectedWeight ell k j ≤
      protectedWeight ell k (j + 1) + protectedWeight ell k (j + 1) := by
  by_cases hj : j < ell
  · rw [protectedWeight_eq_zero_of_lt ell k j hj]
    exact add_nonneg (protectedWeight_nonneg ell k (j + 1))
      (protectedWeight_nonneg ell k (j + 1))
  · have hj' : ¬ j + 1 < ell := by omega
    simp only [protectedWeight, if_neg hj, if_neg hj']
    by_cases hw : scaledWeight k (j + 1) ≤ 1
    · simp only [min_eq_right hw]
      exact (min_le_right 1 (scaledWeight k j)).trans
        (le_of_eq (scaledWeight_split k j))
    · have hw' : 1 ≤ scaledWeight k (j + 1) := (lt_of_not_ge hw).le
      simp only [min_eq_left hw']
      exact (min_le_left 1 (scaledWeight k j)).trans (by norm_num)

def signedCredit (σ τ : Sign) (ell k j : ℕ) : ℚ :=
  if τ = σ then protectedWeight ell k j else -scaledWeight k j

def biasCredit (σ : Sign) (ell k : ℕ) : Bias L → ℚ
  | .zero => 0
  | .dyadic τ i => signedCredit σ τ ell k i.val

def agentCredit (σ : Sign) (ell k : ℕ) (a : AgentState L K) : ℚ :=
  if a.role = .main then biasCredit σ ell k a.bias else 0

def totalCredit (σ : Sign) (ell k : ℕ) (c : Cfg L K) : ℚ :=
  Config.sumOf (agentCredit σ ell k) c

theorem signedCredit_split (σ τ : Sign) (ell k j : ℕ) :
    signedCredit σ τ ell k j ≤
      signedCredit σ τ ell k (j + 1) + signedCredit σ τ ell k (j + 1) := by
  unfold signedCredit
  by_cases hsign : τ = σ
  · simp only [if_pos hsign]
    exact protectedWeight_split ell k j
  · simp only [if_neg hsign]
    have hsplit := scaledWeight_split k j
    linarith

theorem signedCredit_cancel (σ : Sign) (ell k j : ℕ) :
    signedCredit σ .pos ell k j + signedCredit σ .neg ell k j ≤ 0 := by
  have hweight := protectedWeight_le_scaled ell k j
  cases σ <;> simp [signedCredit] <;> linarith

/-- The actual cancel/split helper has nondecreasing bias credit. -/
theorem phase3CancelSplit_credit_pair_mono
    (σ : Sign) (ell k : ℕ) (s t : AgentState L K) :
    biasCredit σ ell k s.bias + biasCredit σ ell k t.bias ≤
      biasCredit σ ell k (phase3CancelSplit L K s t).1.bias +
        biasCredit σ ell k (phase3CancelSplit L K s t).2.bias := by
  cases hs : s.bias with
  | zero =>
      cases ht : t.bias with
      | zero => simp [phase3CancelSplit, hs, ht, biasCredit]
      | dyadic τ i =>
          by_cases hgt : s.hour.val > i.val
          · simpa [phase3CancelSplit, hs, ht, hgt, biasCredit] using
              signedCredit_split σ τ ell k i.val
          · simp [phase3CancelSplit, hs, ht, hgt, biasCredit]
  | dyadic τ i =>
      cases ht : t.bias with
      | zero =>
          by_cases hgt : t.hour.val > i.val
          · simpa [phase3CancelSplit, hs, ht, hgt, biasCredit] using
              signedCredit_split σ τ ell k i.val
          · simp [phase3CancelSplit, hs, ht, hgt, biasCredit]
      | dyadic υ j =>
          cases τ <;> cases υ
          · simp [phase3CancelSplit, hs, ht, biasCredit]
          · by_cases hij : i.val = j.val
            · simpa [phase3CancelSplit, hs, ht, hij, biasCredit] using
                signedCredit_cancel σ ell k i.val
            · simp [phase3CancelSplit, hs, ht, hij, biasCredit]
          · by_cases hij : i.val = j.val
            · simpa [phase3CancelSplit, hs, ht, hij, biasCredit, add_comm] using
                signedCredit_cancel σ ell k i.val
            · simp [phase3CancelSplit, hs, ht, hij, biasCredit]
          · simp [phase3CancelSplit, hs, ht, biasCredit]

/-- A Phase-3 pair must be initialized before the complete Phase-3 rule can
be replaced by its cancel/split and bias-preserving branches. -/
theorem Phase3Transition_credit_pair_mono
    (σ : Sign) (ell k : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    agentCredit σ ell k s + agentCredit σ ell k t ≤
      agentCredit σ ell k (Phase3Transition L K s t).1 +
        agentCredit σ ell k (Phase3Transition L K s t).2 := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · have hroles := Phase5To6FuelProducer.phase3CancelSplit_roles s t
    have hhelper :
        agentCredit σ ell k s + agentCredit σ ell k t ≤
          agentCredit σ ell k (phase3CancelSplit L K s t).1 +
            agentCredit σ ell k (phase3CancelSplit L K s t).2 := by
      simpa [agentCredit, hroles.1, hroles.2, hmain.1, hmain.2] using
        phase3CancelSplit_credit_pair_mono σ ell k s t
    simpa [Phase3Transition, hmain.1, hmain.2] using hhelper
  · have hroles := Phase5To6FuelProducer.Phase3Transition_roles s t hs ht
    have hbias := Phase5To6FuelProducer.Phase3Transition_biases_of_not_both_main
      s t hs ht hmain
    simp only [agentCredit, hroles.1, hroles.2, hbias.1, hbias.2, le_refl]

theorem Transition_credit_pair_mono_of_three_three
    (σ : Sign) (ell k : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    agentCredit σ ell k s + agentCredit σ ell k t ≤
      agentCredit σ ell k (Transition L K s t).1 +
        agentCredit σ ell k (Transition L K s t).2 := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hp := Phase3Transition_credit_pair_mono σ ell k s t hs ht
  unfold Transition
  rw [hepi]
  simpa only [hsp, agentCredit, finishPhase10Entry_role, finishPhase10Entry_bias] using hp

/-- Protected credit is nondecreasing through every real Phase-3/4 pair
interaction, including mixed epidemic entry into Phase 4. -/
theorem Transition_credit_pair_mono_of_phase_three_or_four
    (σ : Sign) (ell k : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 3 ∨ s.phase.val = 4)
    (ht : t.phase.val = 3 ∨ t.phase.val = 4) :
    agentCredit σ ell k s + agentCredit σ ell k t ≤
      agentCredit σ ell k (Transition L K s t).1 +
        agentCredit σ ell k (Transition L K s t).2 := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact Transition_credit_pair_mono_of_three_three σ ell k s t hs ht
  · have hfields := Phase5To6FuelProducer.Transition_role_bias_of_three_four s t hs ht
    simp only [agentCredit, hfields.1, hfields.2.1, hfields.2.2.1,
      hfields.2.2.2, le_refl]
  · have hfields := Phase5To6FuelProducer.Transition_role_bias_of_four_three s t hs ht
    simp only [agentCredit, hfields.1, hfields.2.1, hfields.2.2.1,
      hfields.2.2.2, le_refl]
  · have hfields := Phase5To6FuelProducer.Transition_role_bias_of_four_four s t hs ht
    simp only [agentCredit, hfields.1, hfields.2.1, hfields.2.2.1,
      hfields.2.2.2, le_refl]

theorem phase34Protocol_credit_pair_mono
    (σ : Sign) (ell k : ℕ) (s t : AgentState L K) :
    let p := (Phase5To6FuelProducer.Phase34Protocol L K).δ s t
    agentCredit σ ell k s + agentCredit σ ell k t ≤
      agentCredit σ ell k p.1 + agentCredit σ ell k p.2 := by
  by_cases hphase :
      Phase5To6FuelProducer.InPhase34 s ∧ Phase5To6FuelProducer.InPhase34 t
  · simpa [Phase5To6FuelProducer.Phase34Protocol, hphase] using
      Transition_credit_pair_mono_of_phase_three_or_four σ ell k s t
        hphase.1 hphase.2
  · simp [Phase5To6FuelProducer.Phase34Protocol, hphase]

/-- Configuration-level transport; the source is in the Phase-3/4 window,
while the final step is allowed to reach Phase 5. -/
theorem totalCredit_step_mono (σ : Sign) (ell k : ℕ)
    {c d : Cfg L K} (hc : Phase5To6FuelProducer.AllPhase34 c)
    (hstep : (NonuniformMajority L K).StepRel c d) :
    totalCredit σ ell k c ≤ totalCredit σ ell k d := by
  exact Phase5To6FuelProducer.stepRel_sumOf_le_of_pair
    (M := OrderDual ℚ)
    (f := fun a => (agentCredit σ ell k a : OrderDual ℚ))
    (phase34Protocol_credit_pair_mono σ ell k)
    (Phase5To6FuelProducer.phase34Protocol_stepRel_of_real_step hc hstep)

/-- This holds for every recorded draw, including an inapplicable draw. -/
theorem totalCredit_applyDraw_mono (σ : Sign) (ell k : ℕ)
    (c : Cfg L K) (hc : Phase5To6FuelProducer.AllPhase34 c) (d : Draw L K) :
    totalCredit σ ell k c ≤ totalCredit σ ell k (applyDraw c d) := by
  cases d with
  | none => exact le_rfl
  | some p =>
      change totalCredit σ ell k c ≤
        totalCredit σ ell k
          (Protocol.stepOrSelf (NonuniformMajority L K) c p.1.1 p.2.1)
      by_cases happ : Protocol.Applicable c p.1.1 p.2.1
      · exact totalCredit_step_mono σ ell k hc
          (Protocol.stepRel_stepOrSelf_of_applicable happ)
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- Pathwise persistence on the actual pair-log trace. No probability is
conditioned on a future clock-success event. -/
theorem totalCredit_trace_mono (σ : Sign) (ell k : ℕ)
    (init : Cfg L K) (ω : Ω L K) {s t : ℕ} (hst : s ≤ t)
    (hwindow : ∀ u, s ≤ u → u < t →
      Phase5To6FuelProducer.AllPhase34 (trace init ω u)) :
    totalCredit σ ell k (trace init ω s) ≤
      totalCredit σ ell k (trace init ω t) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hst
  have haux : ∀ r : ℕ,
      (∀ u, s ≤ u → u < s + r →
        Phase5To6FuelProducer.AllPhase34 (trace init ω u)) →
      totalCredit σ ell k (trace init ω s) ≤
        totalCredit σ ell k (trace init ω (s + r)) := by
    intro r
    induction r with
    | zero =>
        intro _
        simp only [Nat.add_zero, le_refl]
    | succ r ih =>
        intro hwin
        have hprevious := ih (fun u hu hut => hwin u hu (by omega))
        have hsource := hwin (s + r) (by omega) (by omega)
        have hnext :
            totalCredit σ ell k (trace init ω (s + r)) ≤
              totalCredit σ ell k (trace init ω (s + (r + 1))) := by
          rw [show s + (r + 1) = (s + r) + 1 by omega, TimeTheorem.trace_succ]
          exact totalCredit_applyDraw_mono σ ell k _ hsource _
        exact hprevious.trans hnext
  exact haux q hwindow

end Ripple.PopulationProtocol.ExactMajority.AveragingCreditTransitions

end

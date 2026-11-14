-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingSeedReceipt.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReadout
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6OriginalLaw

/-!
# Retained credits for the Phase-5 sampling consumer

`LateSeedReadout` intentionally records literal count inequalities at the
first Phase-4 seed.  The sampling proof needs the weighted credits from which
those inequalities were obtained, because raw two- and three-level counts are
not monotone during the remaining Phase-3 interactions.

This file introduces the corrected consumer receipt and proves that both
credits persist along the genuine mixed Phase-3/4/5 prefix.  No probability
statement is made here.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingSeedReceipt

open TimeTheorem StageEventSpec PairLog
open AveragingCreditTransitions AveragingTerminalReadout
open LateStrengthening LateF6Acceptance LateF6OriginalLaw

variable {L K n : ℕ}

/-- The N16 data actually consumed by adaptive Phase-5 sampling. -/
structure LateSamplingSeedReceipt
    (init : InputCfg n) (M ell : ℕ) (σ : Sign)
    (c : InputCfg n) : Prop extends SmallReadout init M ell σ c where
  main_count : timeMainCount c = M
  protected_credit :
    (601 / 625 : ℚ) * (M : ℚ) ≤ totalCredit σ ell (ell + 2) c
  near_credit :
    10000 * scaledShallowPositive σ ell c ≤ 111 * (M : ℚ) ∨
      (1939 / 2000 : ℚ) * (M : ℚ) ≤ totalCredit σ ell (ell + 1) c
  old_index_cutoff : noIndexBelow (ell - terminalCutoff n) c

/-- Forgetting the retained witnesses recovers exactly the public N16 readout. -/
theorem LateSamplingSeedReceipt.toLateSeedReadout
    {init : InputCfg n} {M ell : ℕ} {σ : Sign} {c : InputCfg n}
    (h : LateSamplingSeedReceipt init M ell σ c) :
    LateSeedReadout init M ell σ c := by
  refine
    { toSmallReadout := h.toSmallReadout
      protectedBand := protected_band_of_credit σ ell M c
        h.main_count h.protected_credit
      nearTwoLevels := ?_
      oldIndexCutoff := h.old_index_cutoff }
  rcases h.near_credit with hsmall | hcredit
  · exact Or.inl hsmall
  · exact Or.inr
      (two_level_band_of_credit σ ell M c h.main_count hcredit)

/-- When one input is already in Phase 5, the left participant's Main credit
is unchanged by the real dispatcher. -/
theorem agentCredit_left_eq_of_max_five
    (σ : Sign) (ell k : ℕ) (s t : AgentState L K)
    (hs : Window s) (ht : Window t)
    (hmax : max s.phase.val t.phase.val = 5) :
    agentCredit σ ell k (Transition L K s t).1 =
      agentCredit σ ell k s := by
  have hroles := transition_roles s t hs ht
  have hge :=
    (phaseEpidemicUpdate_left_phase_ge_max L K s t).trans
      (phaseEpidemicUpdate_phase_le_Transition_phase L K s t).1
  have hfour : 4 ≤ (Transition L K s t).1.phase.val := by
    omega
  by_cases hm : s.role = .main
  · have hb := transition_main_freeze_left s t hs ht hm hfour
    simp only [agentCredit, hroles.1, hm, if_true, hb]
  · have hout : (Transition L K s t).1.role ≠ .main := by
      rw [hroles.1]
      exact hm
    simp only [agentCredit, hm, hout, if_false]

/-- Right-output version of `agentCredit_left_eq_of_max_five`. -/
theorem agentCredit_right_eq_of_max_five
    (σ : Sign) (ell k : ℕ) (s t : AgentState L K)
    (hs : Window s) (ht : Window t)
    (hmax : max s.phase.val t.phase.val = 5) :
    agentCredit σ ell k (Transition L K s t).2 =
      agentCredit σ ell k t := by
  have hroles := transition_roles s t hs ht
  have hge :=
    (phaseEpidemicUpdate_right_phase_ge_max L K s t).trans
      (phaseEpidemicUpdate_phase_le_Transition_phase L K s t).2
  have hfour : 4 ≤ (Transition L K s t).2.phase.val := by
    omega
  by_cases hm : t.role = .main
  · have hb := transition_main_freeze_right s t hs ht hm hfour
    simp only [agentCredit, hroles.2, hm, if_true, hb]
  · have hout : (Transition L K s t).2.role ≠ .main := by
      rw [hroles.2]
      exact hm
    simp only [agentCredit, hm, hout, if_false]

/-- Weighted credit is nondecreasing on every actual pair in the complete
Phase-3/4/5 window.  The Phase-3/4 case uses the compiled credit proof; a
pair containing Phase 5 preserves both participants' role/bias fields. -/
theorem transition_credit_pair_mono_of_window
    (σ : Sign) (ell k : ℕ) (s t : AgentState L K)
    (hs : Window s) (ht : Window t) :
    agentCredit σ ell k s + agentCredit σ ell k t ≤
      agentCredit σ ell k (Transition L K s t).1 +
        agentCredit σ ell k (Transition L K s t).2 := by
  by_cases hfive : s.phase.val = 5 ∨ t.phase.val = 5
  · have hs2 : s.phase.val ≤ 5 := hs.2
    have ht2 : t.phase.val ≤ 5 := ht.2
    have hmax : max s.phase.val t.phase.val = 5 := by
      rcases hfive with hfive | hfive <;> omega
    rw [agentCredit_left_eq_of_max_five σ ell k s t hs ht hmax,
      agentCredit_right_eq_of_max_five σ ell k s t hs ht hmax]
  · have hs' : s.phase.val = 3 ∨ s.phase.val = 4 := by
      rcases hs with ⟨hlo, hhi⟩
      omega
    have ht' : t.phase.val = 3 ∨ t.phase.val = 4 := by
      rcases ht with ⟨hlo, hhi⟩
      omega
    exact Transition_credit_pair_mono_of_phase_three_or_four
      σ ell k s t hs' ht'

open Classical in
/-- Guarded protocol equal to the real dispatcher exactly on the window. -/
noncomputable def phaseThreeFiveProtocol (L K : ℕ) :
    Protocol (AgentState L K) where
  δ := fun s t =>
    if Window s ∧ Window t then Transition L K s t else (s, t)

def allPhaseThreeFive (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, Window a

theorem phaseThreeFiveProtocol_credit_pair_mono
    (σ : Sign) (ell k : ℕ) (s t : AgentState L K) :
    let p := (phaseThreeFiveProtocol L K).δ s t
    agentCredit σ ell k s + agentCredit σ ell k t ≤
      agentCredit σ ell k p.1 + agentCredit σ ell k p.2 := by
  by_cases hwindow : Window s ∧ Window t
  · simpa [phaseThreeFiveProtocol, hwindow] using
      transition_credit_pair_mono_of_window σ ell k s t
        hwindow.1 hwindow.2
  · simp [phaseThreeFiveProtocol, hwindow]

theorem phaseThreeFiveProtocol_stepRel_of_real_step
    {c d : Config (AgentState L K)}
    (hc : allPhaseThreeFive c)
    (hstep : (NonuniformMajority L K).StepRel c d) :
    (phaseThreeFiveProtocol L K).StepRel c d := by
  rcases hstep with ⟨r₁, r₂, happ, hd⟩
  have hr₁ : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂ : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  refine ⟨r₁, r₂, happ, ?_⟩
  simpa [phaseThreeFiveProtocol, hc r₁ hr₁, hc r₂ hr₂,
    NonuniformMajority] using hd

theorem totalCredit_step_mono_of_three_five
    (σ : Sign) (ell k : ℕ) {c d : Cfg L K}
    (hc : allPhaseThreeFive c)
    (hstep : (NonuniformMajority L K).StepRel c d) :
    totalCredit σ ell k c ≤ totalCredit σ ell k d := by
  exact Phase5To6FuelProducer.stepRel_sumOf_le_of_pair
    (M := OrderDual ℚ)
    (f := fun a => (agentCredit σ ell k a : OrderDual ℚ))
    (phaseThreeFiveProtocol_credit_pair_mono σ ell k)
    (phaseThreeFiveProtocol_stepRel_of_real_step hc hstep)

theorem totalCredit_applyDraw_mono_of_three_five
    (σ : Sign) (ell k : ℕ) (c : Cfg L K)
    (hc : allPhaseThreeFive c) (d : Draw L K) :
    totalCredit σ ell k c ≤ totalCredit σ ell k (applyDraw c d) := by
  cases d with
  | none => exact le_rfl
  | some p =>
      change totalCredit σ ell k c ≤
        totalCredit σ ell k
          (Protocol.stepOrSelf (NonuniformMajority L K) c p.1.1 p.2.1)
      by_cases happ : Protocol.Applicable c p.1.1 p.2.1
      · exact totalCredit_step_mono_of_three_five σ ell k hc
          (Protocol.stepRel_stepOrSelf_of_applicable happ)
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem totalCredit_trace_mono_of_three_five
    (σ : Sign) (ell k : ℕ) (init : Cfg L K) (ω : Ω L K)
    {s t : ℕ} (hst : s ≤ t)
    (hwindow : ∀ u, s ≤ u → u < t →
      allPhaseThreeFive (trace init ω u)) :
    totalCredit σ ell k (trace init ω s) ≤
      totalCredit σ ell k (trace init ω t) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hst
  have haux : ∀ r : ℕ,
      (∀ u, s ≤ u → u < s + r →
        allPhaseThreeFive (trace init ω u)) →
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
          rw [show s + (r + 1) = (s + r) + 1 by omega,
            TimeTheorem.trace_succ]
          exact totalCredit_applyDraw_mono_of_three_five
            σ ell k _ hsource _
        exact hprevious.trans hnext
  exact haux q hwindow

/-- Specialization to the genuine first-4-to-before-first-6 prefix. -/
theorem totalCredit_prefix_mono
    {init : InputCfg n} {ω : InputLog n} {a s t u v ell k : ℕ}
    (h : Prefix init ω a s t)
    (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t)
    (σ : Sign) :
    totalCredit σ ell k (trace init ω u) ≤
      totalCredit σ ell k (trace init ω v) := by
  apply totalCredit_trace_mono_of_three_five σ ell k init ω huv
  intro r hur hrv x hx
  have hw := h.window r
    (h.start_order.trans (hsu.trans hur)) (by omega)
  exact hw x hx

/-- The protected width-three floor is available at every later observed
snapshot once the retained credit has been exported. -/
theorem LateSamplingSeedReceipt.protectedBand_at
    {init : InputCfg n} {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hseed : LateSamplingSeedReceipt init M ell σ (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t)
    (hcount : timeMainCount (trace init ω v) = M) :
    9232 * M ≤ 10000 * bandCount σ ell 2 (trace init ω v) := by
  have hcredit := hseed.protected_credit.trans
    (totalCredit_prefix_mono hpath le_rfl hsv hvt σ)
  exact protected_band_of_credit σ ell M (trace init ω v)
    hcount hcredit

/-- In the second near-two-level branch, the `.939` class floor likewise
holds at every later observed snapshot.  The first branch remains the literal
small-shallow-mass alternative and is transported by its own mass ledger. -/
theorem LateSamplingSeedReceipt.nearAlternative_at
    {init : InputCfg n} {ω : InputLog n}
    {a s t v M ell : ℕ} {σ : Sign}
    (hpath : Prefix init ω a s t)
    (hseed : LateSamplingSeedReceipt init M ell σ (trace init ω s))
    (hsv : s ≤ v) (hvt : v ≤ t)
    (hcount : timeMainCount (trace init ω v) = M) :
    10000 * scaledShallowPositive σ ell (trace init ω s) ≤ 111 * (M : ℚ) ∨
      939 * M ≤ 1000 * bandCount σ ell 1 (trace init ω v) := by
  rcases hseed.near_credit with hsmall | hcredit
  · exact Or.inl hsmall
  · right
    have hpersist := hcredit.trans
      (totalCredit_prefix_mono hpath le_rfl hsv hvt σ)
    exact two_level_band_of_credit σ ell M (trace init ω v)
      hcount hpersist

end Ripple.PopulationProtocol.ExactMajority.LateSamplingSeedReceipt

end

-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockEmbeddingBridge.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEmbedding
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingMixedLedgers

/-!
# Closing the deterministic guards in the virtual clock embedding

The clock carrier invariant propagates from the seed without an entry-failure
probability allowance. On an AsyncEntry path, the actual and virtual paths agree
through the all-Phase-3 entry time; the homogeneous Phase-3 virtual region is
then invariant. Consequently the phase-range, no-backup, and fixed-role guards
of the embedding hold for the entire virtual continuation from the seed.

These are pathwise statements. They do not condition the scheduler on AsyncEntry.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEmbeddingBridge

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbedding

variable {L K m : ℕ}

/-! ## Roles across the epidemic wrapper -/

private theorem foldl_initializers_role (l : List ℕ)
    (hmem : ∀ k ∈ l, 2 ≤ k) (a : AgentState L K) :
    (l.foldl (fun acc k =>
      if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a).role = a.role := by
  induction l generalizing a with
  | nil => rfl
  | cons k l ih =>
      simp only [List.foldl_cons]
      rw [ih (fun k' hk' => hmem k' (List.mem_cons_of_mem k hk'))]
      have hkmin : 2 ≤ k := hmem k List.mem_cons_self
      by_cases hk : k < 11
      · rw [dif_pos hk, phaseInit_role]
        change (if k = 1 ∧ a.role = .cr then .reserve else a.role) = a.role
        rw [if_neg (by omega)]
      · rw [dif_neg hk]

theorem runInitsBetween_role_of_one_le (oldP newP : ℕ)
    (hold : 1 ≤ oldP) (a : AgentState L K) :
    (runInitsBetween L K oldP newP a).role = a.role := by
  unfold runInitsBetween
  apply foldl_initializers_role
  intro k hk
  rw [List.mem_filter] at hk
  simp only [decide_eq_true_eq] at hk
  omega

theorem phaseEpidemicUpdate_roles_of_one_le (s t : AgentState L K)
    (hs : 1 ≤ s.phase.val) (ht : 1 ≤ t.phase.val) :
    (phaseEpidemicUpdate L K s t).1.role = s.role ∧
      (phaseEpidemicUpdate L K s t).2.role = t.role := by
  have hsl := runInitsBetween_role_of_one_le
    s.phase.val (max s.phase t.phase).val hs
    ({ s with phase := max s.phase t.phase } : AgentState L K)
  have htr := runInitsBetween_role_of_one_le
    t.phase.val (max s.phase t.phase).val ht
    ({ t with phase := max s.phase t.phase } : AgentState L K)
  unfold phaseEpidemicUpdate
  dsimp only
  split_ifs <;> simpa only [phase10EpidemicEntry_role] using And.intro hsl htr

/-- A post-step phase cap rules out either epidemic backup output, including at
a virtual cap pair. This implication does not assume a safe-small-bias history. -/
theorem virtualRule_no_backup_of_phase_le_three (s t : AgentState L K)
    (hsout : (virtualRule s t).1.phase.val ≤ 3)
    (htout : (virtualRule s t).2.phase.val ≤ 3) :
    (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10 := by
  by_cases hc : CapCounterPair s t
  · exact ⟨by rw [hc.1]; decide, by rw [hc.2.1]; decide⟩
  · rw [virtualRule_eq_transition_of_not_cap s t hc] at hsout htout
    have hmono := phaseEpidemicUpdate_phase_le_Transition_phase
      (L := L) (K := K) s t
    have hsle : (phaseEpidemicUpdate L K s t).1.phase.val ≤ 3 :=
      hmono.1.trans hsout
    have htle : (phaseEpidemicUpdate L K s t).2.phase.val ≤ 3 :=
      hmono.2.trans htout
    constructor <;> omega

theorem virtualRule_roles_of_phase_range (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hsout : (virtualRule s t).1.phase.val ≤ 3)
    (htout : (virtualRule s t).2.phase.val ≤ 3) :
    (virtualRule s t).1.role = s.role ∧
      (virtualRule s t).2.role = t.role := by
  by_cases hc : CapCounterPair s t
  · simpa only [virtualRule, if_pos hc, saturatedCounterStep_role] using
      phaseEpidemicUpdate_roles_of_one_le s t hs.1 ht.1
  · rw [virtualRule_eq_transition_of_not_cap s t hc] at hsout htout ⊢
    exact AveragingMixedLedgers.transition_roles_before_exit s t hs ht hsout htout

/-! ## Carrier discipline and homogeneous Phase 3 -/

theorem virtualRule_preserves_carrier (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (virtualRule s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (virtualRule s t).2 := by
  by_cases hc : CapCounterPair s t
  · simpa only [virtualRule, if_pos hc, nonMainCarrierSmallBiasZeroAgent,
      saturatedCounterStep] using
      phaseEpidemicUpdate_preserves_nonMainCarrierSmallBiasZero s t hs ht
  · rw [virtualRule_eq_transition_of_not_cap s t hc]
    exact Transition_preserves_nonMainCarrierSmallBiasZero s t hs ht

/-- Saturating the cap counters makes the all-Phase-3 region genuinely invariant.
The remaining Phase-3 rules only change hours, minutes, biases, or counters. -/
theorem virtualRule_phase_three (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    (virtualRule s t).1.phase.val = 3 ∧
      (virtualRule s t).2.phase.val = 3 := by
  by_cases hcc : s.role = .clock ∧ t.role = .clock
  · have h := virtualRule_active_clock_pair s t hs ht hcc.1 hcc.2
    exact ⟨h.2.2.1, h.2.2.2.1⟩
  · have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
    have hnc : ¬ CapCounterPair s t := by
      intro hc
      apply hcc
      simpa only [hepi] using And.intro hc.2.2.1 hc.2.2.2.1
    have hleft : (Phase3Transition L K s t).1.phase = s.phase :=
      (Phase3Transition_left_output_eq_rule1 L K s t s
        (by rw [if_neg hcc])).2
    have hright : (Phase3Transition L K s t).2.phase = t.phase :=
      (Phase3Transition_right_output_eq_rule1 L K s t t
        (by rw [if_neg hcc])).2
    rw [virtualRule_eq_transition_of_not_cap s t hnc,
      transition_eq_phase3_of_dispatch s t (by rw [hepi]; exact hs), hepi]
    simpa only [finishPhase10Entry_phase_val, hleft, hright] using And.intro hs ht

private theorem ruleUpdate_property (F : PairRule L K) (P : AgentState L K → Prop)
    (f : Fin m → AgentState L K) (i j : Fin m)
    (hf : ∀ k, P (f k)) (hout : P (F (f i) (f j)).1 ∧ P (F (f i) (f j)).2) :
    ∀ k, P (ruleUpdate F f i j k) := by
  intro k
  by_cases hkj : k = j
  · subst k
    simpa only [ruleUpdate, Function.update_self] using hout.2
  · by_cases hki : k = i
    · subst k
      simpa only [ruleUpdate, Function.update_of_ne hkj, Function.update_self] using hout.1
    · simpa only [ruleUpdate, Function.update_of_ne hkj, Function.update_of_ne hki] using hf k

private theorem ruleUpdate_roles (F : PairRule L K) (f : Fin m → AgentState L K)
    (i j : Fin m)
    (hout : (F (f i) (f j)).1.role = (f i).role ∧
      (F (f i) (f j)).2.role = (f j).role) :
    ∀ k, (ruleUpdate F f i j k).role = (f k).role := by
  intro k
  by_cases hkj : k = j
  · subst k
    simpa only [ruleUpdate, Function.update_self] using hout.2
  · by_cases hki : k = i
    · subst k
      simpa only [ruleUpdate, Function.update_of_ne hkj, Function.update_self] using hout.1
    · simp only [ruleUpdate, Function.update_of_ne hkj, Function.update_of_ne hki]

theorem virtualLabels_carrier_of_time (init : Cfg L K) (ω : Ω L K) (S : ℕ)
    (hS : ∀ i, nonMainCarrierSmallBiasZeroAgent (virtualLabels init ω S i)) :
    ∀ t, S ≤ t → ∀ i, nonMainCarrierSmallBiasZeroAgent (virtualLabels init ω t i) := by
  intro t hSt
  induction t, hSt using Nat.le_induction with
  | base => exact hS
  | succ t hSt ih =>
      rw [virtualLabels_succ]
      cases hd : drawLabels init ω (t + 1) with
      | none => exact ih
      | some p =>
          rcases p with ⟨i, j⟩
          exact ruleUpdate_property virtualRule nonMainCarrierSmallBiasZeroAgent
            (virtualLabels init ω t) i j ih
            (virtualRule_preserves_carrier _ _ (ih i) (ih j))

theorem virtualLabels_phase_three_of_time (init : Cfg L K) (ω : Ω L K) (T : ℕ)
    (hT : ∀ i, (virtualLabels init ω T i).phase.val = 3) :
    ∀ t, T ≤ t → ∀ i, (virtualLabels init ω t i).phase.val = 3 := by
  intro t hTt
  induction t, hTt using Nat.le_induction with
  | base => exact hT
  | succ t hTt ih =>
      rw [virtualLabels_succ]
      cases hd : drawLabels init ω (t + 1) with
      | none => exact ih
      | some p =>
          rcases p with ⟨i, j⟩
          exact ruleUpdate_property virtualRule (fun a => a.phase.val = 3)
            (virtualLabels init ω t) i j ih
            (virtualRule_phase_three _ _ (ih i) (ih j))

/-! ## A usable prefix guard for the front-count step law -/

theorem virtualLabels_roles_step_of_phase_range
    (init : Cfg L 256) (ω : Ω L 256) (t : ℕ)
    (hpre : ∀ k, 1 ≤ (virtualLabels init ω t k).phase.val ∧
      (virtualLabels init ω t k).phase.val ≤ 3)
    (hpost : ∀ k, (virtualLabels init ω (t + 1) k).phase.val ≤ 3) :
    ∀ k, (virtualLabels init ω (t + 1) k).role =
      (virtualLabels init ω t k).role := by
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      rw [virtualLabels_succ, hd]
      intro k
      rfl
  | some p =>
      rcases p with ⟨i, j⟩
      have hij := (labelsAt_selected_transition init ω t i j hd).1
      have hleft : (virtualRule (virtualLabels init ω t i)
          (virtualLabels init ω t j)).1.phase.val ≤ 3 := by
        have h := hpost i
        rw [virtualLabels_succ, hd] at h
        simpa only [auxStep, ruleUpdate, Function.update_of_ne hij,
          Function.update_self] using h
      have hright : (virtualRule (virtualLabels init ω t i)
          (virtualLabels init ω t j)).2.phase.val ≤ 3 := by
        have h := hpost j
        rw [virtualLabels_succ, hd] at h
        simpa only [auxStep, ruleUpdate, Function.update_self] using h
      rw [virtualLabels_succ, hd]
      exact ruleUpdate_roles virtualRule (virtualLabels init ω t) i j
        (virtualRule_roles_of_phase_range _ _ (hpre i) (hpre j) hleft hright)

/-- This version has only the current phase/carrier guard and the next-state phase
cap. In particular it has no independent no-backup or roles-fixed assumption. -/
theorem frontCount_virtualLabels_succ_of_phase_range
    (init : Cfg L 256) (ω : Ω L 256) (t : ℕ)
    (i j : Fin init.card) (hd : drawLabels init ω (t + 1) = some (i, j))
    (hpre : ∀ k, 1 ≤ (virtualLabels init ω t k).phase.val ∧
      (virtualLabels init ω t k).phase.val ≤ 3)
    (hclk : ∀ k, (virtualLabels init ω t k).role = .clock →
      (virtualLabels init ω t k).smallBias.val = 3)
    (hpost : ∀ k, (virtualLabels init ω (t + 1) k).phase.val ≤ 3)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1)) :
    frontCount (virtualLabels init ω (t + 1)) ℓ =
      frontCount (virtualLabels init ω t) ℓ +
        if GatedTick ℓ (virtualLabels init ω t) i j then 1 else 0 := by
  have hij := (labelsAt_selected_transition init ω t i j hd).1
  have hleft : (virtualRule (virtualLabels init ω t i)
      (virtualLabels init ω t j)).1.phase.val ≤ 3 := by
    have h := hpost i
    rw [virtualLabels_succ, hd] at h
    simpa only [auxStep, ruleUpdate, Function.update_of_ne hij,
      Function.update_self] using h
  have hright : (virtualRule (virtualLabels init ω t i)
      (virtualLabels init ω t j)).2.phase.val ≤ 3 := by
    have h := hpost j
    rw [virtualLabels_succ, hd] at h
    simpa only [auxStep, ruleUpdate, Function.update_self] using h
  exact frontCount_virtualLabels_succ_regime init (by decide) ω t i j hd hpre hclk
    (virtualRule_no_backup_of_phase_le_three _ _ hleft hright)
    (virtualLabels_roles_step_of_phase_range init ω t hpre hpost) ℓ hℓ hcap

/-! ## Discharging the guards on the existing AsyncEntry intersection -/

structure ClockEnvironment (f : Fin m → AgentState L K) : Prop where
  phase_range : ∀ i, 1 ≤ (f i).phase.val ∧ (f i).phase.val ≤ 3
  carrier : ∀ i, nonMainCarrierSmallBiasZeroAgent (f i)

theorem ClockEnvironment.clock_regime {f : Fin m → AgentState L K}
    (h : ClockEnvironment f) (i : Fin m) (hc : (f i).role = .clock) :
    ClockRegime (f i) :=
  ⟨hc, (h.phase_range i).1, (h.phase_range i).2,
    h.carrier i (Or.inr (Or.inr hc))⟩

theorem seedProfile_clockEnvironment {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S : ℕ)
    (hseed : StageEventSpec.SeedProfile n init (trace init ω S)) :
    ClockEnvironment (labelsAt init ω S) := by
  constructor
  · intro i
    exact hseed.phase_range _ (labelsAt_mem_trace init ω S i)
  · intro i hc
    apply hseed.nonmain_zero _ (labelsAt_mem_trace init ω S i)
    rcases hc with hc | hc | hc <;> simp [hc]

theorem virtualLabels_eq_labelsAt_through_asyncEntry {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (S T : ℕ)
    (hentry : StageEventSpec.AsyncEntry init ω S T) :
    ∀ u, u ≤ T → virtualLabels init ω u = labelsAt init ω u := by
  apply virtualLabels_eq_labelsAt_of_phases_lt_four init ω T
  intro u hu i
  by_cases hbefore : u < S
  · have hlt := hentry.first_phase_seed.2 u hbefore _
      (labelsAt_mem_trace init ω u i)
    omega
  · have hSu : S ≤ u := by omega
    have hcap := (hentry.phases u hSu hu _
      (labelsAt_mem_trace init ω u i)).2
    omega

theorem virtualLabels_clockEnvironment_of_asyncEntry {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (S T : ℕ)
    (hentry : StageEventSpec.AsyncEntry init ω S T) :
    ∀ u, S ≤ u → ClockEnvironment (virtualLabels init ω u) := by
  have heq := virtualLabels_eq_labelsAt_through_asyncEntry init ω S T hentry
  have hseed : ClockEnvironment (virtualLabels init ω S) := by
    rw [heq S hentry.order]
    exact seedProfile_clockEnvironment init ω S hentry.seed_profile
  have hT : ∀ i, (virtualLabels init ω T i).phase.val = 3 := by
    intro i
    rw [heq T le_rfl]
    exact hentry.advanced_profile.all_three _ (labelsAt_mem_trace init ω T i)
  intro u hSu
  refine ⟨?_, virtualLabels_carrier_of_time init ω S hseed.carrier u hSu⟩
  intro i
  by_cases huT : u ≤ T
  · rw [heq u huT]
    exact hentry.phases u hSu huT _ (labelsAt_mem_trace init ω u i)
  · have hthree := virtualLabels_phase_three_of_time init ω T hT u (by omega) i
    constructor <;> omega

theorem virtualLabels_roles_fixed_of_asyncEntry {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (S T : ℕ)
    (hentry : StageEventSpec.AsyncEntry init ω S T) :
    ∀ u, S ≤ u → ∀ i, (virtualLabels init ω u i).role =
      (labelsAt init ω S i).role := by
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry
  intro u hSu
  induction u, hSu using Nat.le_induction with
  | base =>
      intro i
      rw [virtualLabels_eq_labelsAt_through_asyncEntry init ω S T hentry S hentry.order]
  | succ u hSu ih =>
      intro i
      exact (virtualLabels_roles_step_of_phase_range init ω u
        (henv u hSu).phase_range
        (fun k => ((henv (u + 1) (by omega)).phase_range k).2) i).trans (ih i)

theorem frontCount_virtualLabels_succ_of_asyncEntry {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (S T : ℕ)
    (hentry : StageEventSpec.AsyncEntry init ω S T)
    (t : ℕ) (hSt : S ≤ t) (i j : Fin init.card)
    (hd : drawLabels init ω (t + 1) = some (i, j))
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    frontCount (virtualLabels init ω (t + 1)) ℓ =
      frontCount (virtualLabels init ω t) ℓ +
        if GatedTick ℓ (virtualLabels init ω t) i j then 1 else 0 := by
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry
  exact frontCount_virtualLabels_succ_of_phase_range init ω t i j hd
    (henv t hSt).phase_range
    (fun k hc => (henv t hSt).carrier k (Or.inr (Or.inr hc)))
    (fun k => ((henv (t + 1) (by omega)).phase_range k).2) ℓ hℓ hcap

theorem clockSet_virtualLabels_eq_seed {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (S T : ℕ)
    (hentry : StageEventSpec.AsyncEntry init ω S T)
    (u : ℕ) (hSu : S ≤ u) :
    clockSet (virtualLabels init ω u) = clockSet (labelsAt init ω S) := by
  classical
  ext i
  simp only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and,
    virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry u hSu]

/-- The reviewed front uses the physical Clock labels frozen at S. Before the
genuine first exit, this is exactly the current virtual front. -/
theorem stageEvent_frontCount_eq_virtual_of_asyncEntry {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (S T : ℕ)
    (hentry : StageEventSpec.AsyncEntry init ω S T)
    {ρ : ℕ} (hρ : firstPhaseSeed init 4 ρ ω)
    (v ℓ : ℕ) (hSv : S ≤ v) (hvρ : v < ρ) :
    StageEventSpec.frontCount init ω S v ℓ =
      frontCount (virtualLabels init ω v) ℓ := by
  have heq := virtualLabels_eq_labelsAt_before_seed init ω hρ v hvρ
  have hroles : ∀ i, (labelsAt init ω v i).role = (labelsAt init ω S i).role := by
    intro i
    rw [← heq]
    exact virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry v hSv i
  rw [stageEvent_frontCount_eq init ω S v ℓ hroles, ← heq]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEmbeddingBridge

end

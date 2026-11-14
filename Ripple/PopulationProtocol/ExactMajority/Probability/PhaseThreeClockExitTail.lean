import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockBudget
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCounterLedger
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockStoppedPassage
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinning

/-!
# The exit-deadline tail (N12, step 6, probabilistic half of P15 (65))

PHASE3 P15 (65): once every Clock is at the cap and all agents are in Phase 3, a tagged
Clock meets another capped Clock with probability `2 (C - 1) / (n (n - 1))` at every raw
step, and `50 H + 1` such contacts force a counter exit. This file proves the tail

`law {∃ s, seedTime 3 = s ∧ VirtualGoodAt s ∧ ¬ ExitDeadlineAt s} ≤ 1 / n ^ 12`,

the input `hexit` of `PhaseThreeClockBudget.asynchronous_clock_estimate_of_tails`.

* `CapState init ω S t`: the all-cap state on the actual path (roles as at `S`, every
  agent in Phase 3, every Clock at the cap); it is preserved by every interaction that
  is not a counter exit (`capState_succ`), and a counter exit produces an agent in phase
  exactly four (`transition_phase_eq_four_of_exit`).
* `capPrefix init S z`: the prefix event (genuine first Phase-3 seed at `S`, Clock
  density at `S`, `z` the first all-cap time at or after `S`), measurable at `z`; the
  prefixes are pairwise disjoint over `(S, z)`.
* `exitStop`: the first offset after `z` at which some agent has phase at least four,
  a stopping time of the `z`-shifted pair-log filtration, killed outside the prefix.
* `tagIndicator`: the indicator that the next drawn pair is an eligible contact of the
  least Clock; its conditional probability given the past is at least `exitRate n` on
  the all-cap state (`tagIndicator_condExp_floor`), and on the prefix with no exit
  through `z + N` its count is the eligible-contact count of the counter ledger
  (`bernoulliCount_tag_eq`), hence at most `50 H`.
* `exit_prefix_tail`: `PhaseThreeClockStoppedPassage.prefix_success_hitting_tail` with
  `N = logWindow n 400`, `k = 50 H + 1`; `exit_budget`: the exponent is at most `n^{-12}`.
* `exit_deadline_tail`: the headline, by the inclusion `exit_bad_subset` and the sum over
  the disjoint prefixes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockExitTail

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec PhaseThreeClockVirtual
  PhaseThreeClockEmbedding PhaseThreeClockEmbeddingBridge PhaseThreeClockCore
  PhaseThreeClockTransfer PhaseThreeClockProducer PhaseThreeClockAssembly
  PhaseThreeClockExit PhaseThreeClockCounterLedger PhaseThreeClockStoppedPassage
  PhaseThreeClockPrefixTails PhaseThreeClockThinning PhaseThreeScalar

/-! ## Agent-level facts: exit exactness and cap-minute preservation -/

section Agent

variable {L K : ℕ}

theorem phaseInit_phase_of_four (p : Fin 11) (hp : p.val = 4) (a : AgentState L K) :
    (phaseInit L K p a).phase = a.phase := by
  unfold phaseInit
  simp [hp]

/-- At a counter exit from Phase 3 the exiting endpoint enters phase exactly four. -/
theorem stdCounterSubroutine_phase_eq_four (a : AgentState L K)
    (h3 : a.phase.val = 3) (h0 : a.counter.val = 0) :
    (stdCounterSubroutine L K a).phase.val = 4 := by
  unfold stdCounterSubroutine
  rw [dif_pos h0]
  change (phaseInit L K (advancePhase L K a).phase (advancePhase L K a)).phase.val = 4
  have hadv : (advancePhase L K a).phase.val = 4 := by
    unfold advancePhase
    rw [dif_pos (by omega)]
    change a.phase.val.succ = 4
    omega
  rw [phaseInit_phase_of_four _ hadv]
  exact hadv

/-- An actual counter exit puts one endpoint in phase exactly four. -/
theorem transition_phase_eq_four_of_exit (s t : AgentState L K) (h : CounterExitPair s t) :
    (Transition L K s t).1.phase.val = 4 ∨ (Transition L K s t).2.phase.val = 4 := by
  obtain ⟨hcap, hz⟩ := h
  rw [transition_of_capCounterPair s t hcap]
  simp only [finishPhase10Entry_phase_val]
  rcases hz with h0 | h0
  · exact Or.inl (stdCounterSubroutine_phase_eq_four _ hcap.1 h0)
  · exact Or.inr (stdCounterSubroutine_phase_eq_four _ hcap.2.1 h0)

/-- A capped Phase-3 Clock as initiator keeps the cap minute under the virtual rule
with any Phase-3 partner. -/
theorem virtualRule_cap_minute_left (s x : AgentState L K) (hs3 : s.phase.val = 3)
    (hx3 : x.phase.val = 3) (hsr : s.role = .clock) (hsm : s.minute.val = K * (L + 1)) :
    (virtualRule s x).1.minute.val = K * (L + 1) := by
  by_cases hxr : x.role = .clock
  · have h := PhaseThreeClockGatedLaw.virtualRule_active_clock_pair s x hs3 hx3 hsr hxr
    rw [h.2.2.2.2.1]
    have hxm := x.minute.isLt
    split_ifs with h1 h2
    · omega
    · omega
    · exact hsm
  · have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s x hs3 hx3
    have hnc : ¬ CapCounterPair s x := by
      intro hc
      apply hxr
      have := hc.2.2.2.1
      rw [hepi] at this
      exact this
    rw [virtualRule_eq_transition_of_not_cap s x hnc,
      PhaseThreeClockGatedLaw.transition_eq_phase3_of_dispatch s x (by rw [hepi]; exact hs3),
      hepi]
    simp only []
    rw [phase3Transition_clock_left s x hsr hxr,
      finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by show s.phase.val ≠ 10; omega)]
    exact hsm

/-- A capped Phase-3 Clock as responder keeps the cap minute under the virtual rule
with any Phase-3 partner. -/
theorem virtualRule_cap_minute_right (x s : AgentState L K) (hx3 : x.phase.val = 3)
    (hs3 : s.phase.val = 3) (hsr : s.role = .clock) (hsm : s.minute.val = K * (L + 1)) :
    (virtualRule x s).2.minute.val = K * (L + 1) := by
  by_cases hxr : x.role = .clock
  · have h := PhaseThreeClockGatedLaw.virtualRule_active_clock_pair x s hx3 hs3 hxr hsr
    rw [h.2.2.2.2.2]
    have hxm := x.minute.isLt
    split_ifs with h1
    · omega
    · exact hsm
  · have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 x s hx3 hs3
    have hnc : ¬ CapCounterPair x s := by
      intro hc
      apply hxr
      have := hc.2.2.1
      rw [hepi] at this
      exact this
    rw [virtualRule_eq_transition_of_not_cap x s hnc,
      PhaseThreeClockGatedLaw.transition_eq_phase3_of_dispatch x s (by rw [hepi]; exact hx3),
      hepi]
    simp only []
    rw [phase3Transition_clock_right x s hxr hsr,
      finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by show s.phase.val ≠ 10; omega)]
    exact hsm

end Agent

/-! ## The all-cap state on the actual path -/

variable {n : ℕ} (init : InputCfg n)

/-- A capped Clock: role Clock, Phase 3, minute at the cap. -/
def CapClock (f : Lab init) (j : Fin init.card) : Prop :=
  (f j).role = .clock ∧ (f j).phase.val = 3 ∧ (f j).minute.val = clockTop n

/-- The least Clock label of a labelling: the tagged Clock of P15. -/
def IsLeastClock (f : Lab init) (i : Fin init.card) : Prop :=
  (f i).role = .clock ∧ ∀ i', (f i').role = .clock → i ≤ i'

/-- A drawn pair is a tagged eligible contact: both endpoints are capped Clocks and one
of them is the least Clock. -/
def TagContact (f : Lab init) (j l : Fin init.card) : Prop :=
  (IsLeastClock init f j ∨ IsLeastClock init f l) ∧ CapClock init f j ∧ CapClock init f l

/-- The all-cap labelling relative to a role map: roles as prescribed, every agent in
Phase 3, every Clock at the cap. -/
def CapLab (r : Fin init.card → Role) (f : Lab init) : Prop :=
  (∀ i, (f i).role = r i) ∧ (∀ i, (f i).phase.val = 3) ∧
    (∀ i, r i = .clock → (f i).minute.val = clockTop n)

theorem isLeastClock_unique {f : Lab init} {i i' : Fin init.card}
    (h : IsLeastClock init f i) (h' : IsLeastClock init f i') : i = i' :=
  le_antisymm (h.2 i' h'.1) (h'.2 i h.1)

theorem isLeastClock_congr {f g : Lab init} (hr : ∀ i, (f i).role = (g i).role)
    (i : Fin init.card) : IsLeastClock init f i ↔ IsLeastClock init g i := by
  unfold IsLeastClock
  simp only [hr]

theorem clockCount_labelCfg_eq (f : Lab init) :
    clockCount (labelCfg f) = (Finset.univ.filter (fun i => (f i).role = .clock)).card := by
  unfold clockCount labelCfg
  exact Multiset.countP_map f (Finset.univ : Finset (Fin init.card)).val
    (fun a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 => a.role = .clock)

theorem clockSet_card_eq (f : Lab init) :
    (PhaseThreeClockGatedLaw.clockSet f).card = clockCount (labelCfg f) := by
  rw [clockCount_labelCfg_eq]
  rfl

theorem labelCount_fixedRole_eq (fS : Lab init) :
    labelCount init (fixedRoleL init fS .clock) = clockCount (labelCfg fS) := by
  classical
  rw [clockCount_labelCfg_eq]
  unfold labelCount
  rw [Finset.card_filter, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (fS i).role = .clock
  · rw [if_pos h, if_pos (show fixedRoleL init fS .clock i from h)]
  · rw [if_neg h, if_neg (show ¬ fixedRoleL init fS .clock i from h)]

/-- A filter containing a filter of no smaller cardinality contains every element of
it; stated for arbitrary decidability instances. -/
theorem filter_all_of_card_le {α : Type*} {s : Finset α} {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] (hcard : (s.filter q).card ≤ (s.filter p).card)
    (hpq : ∀ a, p a → q a) : ∀ a ∈ s, q a → p a := by
  intro a ha hq
  have hsub : s.filter p ⊆ s.filter q := fun x hx => by
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hpq x hx.2⟩
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : a ∈ s.filter q := Finset.mem_filter.mpr ⟨ha, hq⟩
  rw [← heq] at hmem
  exact (Finset.mem_filter.mp hmem).2

/-- From the cap-count equality at the cap time: every Clock of `fS` is active at the
cap minute in `fv`. -/
theorem capClocks_of_frontCount_eq (fS fv : Lab init)
    (h : frontCountL init fS fv (clockTop n) = clockCount (labelCfg fS)) :
    ∀ i, (fS i).role = .clock → 3 ≤ (fv i).phase.val ∧ (fv i).minute.val = clockTop n := by
  intro i hi
  rw [← labelCount_fixedRole_eq] at h
  unfold frontCountL labelCount at h
  rw [Finset.card_filter, Finset.card_filter] at h
  have key := (Finset.sum_eq_sum_iff_of_le (fun j _ => ?_)).mp h i (Finset.mem_univ i)
  swap
  · split_ifs with h1 h2
    · exact le_rfl
    · exact absurd h1.1 h2
    · exact Nat.zero_le _
    · exact le_rfl
  rw [if_pos (show fixedRoleL init fS .clock i from hi)] at key
  by_cases hP : fixedRoleL init fS .clock i ∧ clockTop n ≤ effectiveMinuteL init fv i
  · obtain ⟨-, hmin⟩ := hP
    unfold effectiveMinuteL at hmin
    split_ifs at hmin with hact
    · refine ⟨hact, ?_⟩
      have := (fv i).minute.isLt
      unfold clockTop at hmin ⊢
      omega
    · exfalso
      unfold clockTop at hmin
      omega
  · rw [if_neg hP] at key
    exact absurd key (by norm_num)

/-- On an all-cap labelling the cap count equals the Clock count. -/
theorem frontCount_eq_of_capLab (r : Fin init.card → Role) (fS fv : Lab init)
    (hS : ∀ i, (fS i).role = r i) (hv : CapLab init r fv) :
    frontCountL init fS fv (clockTop n) = clockCount (labelCfg fS) := by
  classical
  rw [← labelCount_fixedRole_eq]
  unfold frontCountL labelCount
  rw [Finset.card_filter, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : fixedRoleL init fS .clock i
  · have hr : r i = .clock := by rw [← hS i]; exact h
    have hact : activeL init fv i := by
      unfold activeL
      have := hv.2.1 i
      omega
    have hmin : clockTop n ≤ effectiveMinuteL init fv i := by
      unfold effectiveMinuteL
      rw [if_pos hact, hv.2.2 i hr]
    rw [if_pos (And.intro h hmin), if_pos h]
  · rw [if_neg (fun hc => h hc.1), if_neg h]

open Classical in
/-- The tagged-contact pairs on an all-cap labelling number at least `2 (C - 1)`. -/
theorem goodPairs_tagContact_card (r : Fin init.card → Role) (f : Lab init)
    (hf : CapLab init r f) (hne : (PhaseThreeClockGatedLaw.clockSet f).Nonempty) :
    2 * ((PhaseThreeClockGatedLaw.clockSet f).card - 1) ≤
      (goodPairs (TagContact init) f).card := by
  set C := PhaseThreeClockGatedLaw.clockSet f with hC
  have hmemC : ∀ j, j ∈ C ↔ (f j).role = .clock := by
    intro j
    simp only [hC, PhaseThreeClockGatedLaw.clockSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
  set i₀ := C.min' hne with hi₀
  have hi₀C : i₀ ∈ C := Finset.min'_mem C hne
  have hleast : IsLeastClock init f i₀ :=
    ⟨(hmemC i₀).mp hi₀C, fun i' hi' => Finset.min'_le C i' ((hmemC i').mpr hi')⟩
  have hcapClock : ∀ j ∈ C, CapClock init f j := by
    intro j hj
    have hjr : (f j).role = .clock := (hmemC j).mp hj
    exact ⟨hjr, hf.2.1 j, hf.2.2 j (by rw [← hf.1 j]; exact hjr)⟩
  let S₁ : Finset (Fin init.card × Fin init.card) := (C.erase i₀).image (fun l => (i₀, l))
  let S₂ : Finset (Fin init.card × Fin init.card) := (C.erase i₀).image (fun l => (l, i₀))
  have hS₁ : S₁ ⊆ goodPairs (TagContact init) f := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    have hl' := Finset.mem_erase.mp hl
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hl'.1 h.symm, Or.inl hleast, hcapClock i₀ hi₀C, hcapClock l hl'.2⟩
  have hS₂ : S₂ ⊆ goodPairs (TagContact init) f := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    have hl' := Finset.mem_erase.mp hl
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hl'.1, Or.inr hleast, hcapClock l hl'.2, hcapClock i₀ hi₀C⟩
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp1
    obtain ⟨l', hl', hEq⟩ := Finset.mem_image.mp hp2
    exact (Finset.mem_erase.mp hl).1 (Prod.mk.inj hEq).2.symm
  have hc1 : S₁.card = C.card - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2),
      Finset.card_erase_of_mem hi₀C]
  have hc2 : S₂.card = C.card - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
      Finset.card_erase_of_mem hi₀C]
  calc 2 * (C.card - 1) = S₁.card + S₂.card := by rw [hc1, hc2, two_mul]
    _ = (S₁ ∪ S₂).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (goodPairs (TagContact init) f).card :=
        Finset.card_le_card (Finset.union_subset hS₁ hS₂)

/-! ## The all-cap state along the actual path -/

variable (ω : InputLog n)

/-- The all-cap state at time `t` with the roles of time `S`, on the actual path. -/
def CapState (S t : ℕ) : Prop :=
  CapLab init (fun i => (labelsAt init ω S i).role) (labelsAt init ω t)

theorem capState_capLab {S t : ℕ} (h : CapState init ω S t) :
    CapLab init (fun i => (labelsAt init ω S i).role) (labelsAt init ω t) := h

theorem capState_allCapAt {S t : ℕ} (h : CapState init ω S t) : AllCapAt init ω S t :=
  ⟨h.1, fun k hk => ⟨h.2.1 k, h.2.2 k ((h.1 k).symm.trans hk)⟩, fun k => (h.2.1 k).le⟩

/-- One interaction that is not a counter exit preserves the all-cap state. -/
theorem capState_succ {S t : ℕ} (h : CapState init ω S t)
    (hlt4 : ∀ k, (labelsAt init ω (t + 1) k).phase.val < 4) : CapState init ω S (t + 1) := by
  obtain ⟨hroles, hphase, hcap⟩ := h
  have hTrans : (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).δ =
      Transition (PhaseThreeModel.Numeric.hourIndex n) 256 := rfl
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      have hstep := labelsAt_succ_eq_auxStep init ω t
      rw [hd] at hstep
      simp only [auxStep] at hstep
      unfold CapState
      rw [hstep]
      exact ⟨hroles, hphase, hcap⟩
  | some ij =>
      obtain ⟨i, j⟩ := ij
      obtain ⟨hij, hi, hj, hother⟩ := labelsAt_selected_transition init ω t i j hd
      rw [hTrans] at hi hj
      have hne : ¬ CounterExitPair (labelsAt init ω t i) (labelsAt init ω t j) := by
        intro hex
        rcases transition_phase_eq_four_of_exit _ _ hex with h4 | h4
        · have := hlt4 i
          rw [hi] at this
          omega
        · have := hlt4 j
          rw [hj] at this
          omega
      have hv := virtualRule_eq_transition _ _ hne
      rw [← hv] at hi hj
      have hi3 := hphase i
      have hj3 := hphase j
      have hp := virtualRule_phase_three _ _ hi3 hj3
      have hr := virtualRule_roles_of_phase_range (labelsAt init ω t i) (labelsAt init ω t j)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hp.1.le hp.2.le
      refine ⟨?_, ?_, ?_⟩
      · intro k
        by_cases hki : k = i
        · subst hki
          rw [hi, hr.1]
          exact hroles k
        by_cases hkj : k = j
        · subst hkj
          rw [hj, hr.2]
          exact hroles k
        rw [hother k hki hkj]
        exact hroles k
      · intro k
        by_cases hki : k = i
        · subst hki
          rw [hi]
          exact hp.1
        by_cases hkj : k = j
        · subst hkj
          rw [hj]
          exact hp.2
        rw [hother k hki hkj]
        exact hphase k
      · intro k hk
        by_cases hki : k = i
        · subst hki
          rw [hi]
          exact virtualRule_cap_minute_left _ _ hi3 hj3 ((hroles k).trans hk) (hcap k hk)
        by_cases hkj : k = j
        · subst hkj
          rw [hj]
          exact virtualRule_cap_minute_right _ _ hi3 hj3 ((hroles k).trans hk) (hcap k hk)
        rw [hother k hki hkj]
        exact hcap k hk

/-- The all-cap state persists while every phase stays below four. -/
theorem capState_persist {S z v : ℕ} (hz : CapState init ω S z)
    (hlt4 : ∀ u, z < u → u ≤ v → ∀ k, (labelsAt init ω u k).phase.val < 4) :
    ∀ u, z ≤ u → u ≤ v → CapState init ω S u := by
  intro u hzu huv
  induction u, hzu using Nat.le_induction with
  | base => exact hz
  | succ u hzu ih =>
      exact capState_succ init ω (ih (by omega)) (hlt4 (u + 1) (by omega) huv)

/-- Tagged contacts at an all-cap time are the eligible contacts of the least Clock. -/
theorem tagContact_iff_eligible (S t : ℕ) (hcs : CapState init ω S t) (i₀ : Fin init.card)
    (hi₀ : IsLeastClock init (labelsAt init ω S) i₀) :
    (∃ j l, drawLabels init ω (t + 1) = some (j, l) ∧
        TagContact init (labelsAt init ω t) j l) ↔
      eligibleContact init ω S i₀ (t + 1) := by
  have hr : ∀ i, (labelsAt init ω t i).role = (labelsAt init ω S i).role := hcs.1
  have hleast : ∀ j, IsLeastClock init (labelsAt init ω t) j ↔ j = i₀ := by
    intro j
    rw [isLeastClock_congr init hr]
    exact ⟨fun h => isLeastClock_unique init h hi₀, fun h => h ▸ hi₀⟩
  constructor
  · rintro ⟨j, l, hjl, hl, ⟨hjr, hj3, hjm⟩, ⟨hlr, hl3, hlm⟩⟩
    refine ⟨Nat.succ_pos t, j, l, hjl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hl with h | h
      · exact Or.inl ((hleast j).mp h).symm
      · exact Or.inr ((hleast l).mp h).symm
    · show (labelsAt init ω S j).role = .clock
      rw [← hr j]
      exact hjr
    · show (labelsAt init ω S l).role = .clock
      rw [← hr l]
      exact hlr
    · simpa using hj3
    · simpa using hl3
    · simpa using hjm
    · simpa using hlm
  · rintro ⟨-, j, l, hjl, hmem, hjr, hlr, hj3, hl3, hjm, hlm⟩
    refine ⟨j, l, hjl, ?_, ⟨?_, by simpa using hj3, by simpa using hjm⟩,
      ⟨?_, by simpa using hl3, by simpa using hlm⟩⟩
    · rcases hmem with h | h
      · exact Or.inl ((hleast j).mpr h.symm)
      · exact Or.inr ((hleast l).mpr h.symm)
    · rw [hr j]
      exact hjr
    · rw [hr l]
      exact hlr

/-! ## The prefix event, the stopping time and the indicator -/

theorem measurable_labelsAt (t : ℕ) :
    Measurable[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      (fun ω => labelsAt init ω t) := by
  have h := measurable_auxLabels init (NonuniformMajority _ _).δ t
  have hfun : (fun ω : InputLog n => labelsAt init ω t) =
      fun ω => auxLabels init (NonuniformMajority _ _).δ ω t := by
    funext ω
    exact labelsAt_eq_auxLabels_delta init ω t
  rw [hfun]
  exact h

theorem capState_measurableSet {S t : ℕ} (hSt : S ≤ t) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | CapState init ω S t} := by
  have hset : {ω | CapState init ω S t} = ⋃ f : Lab init,
      ({ω | labelsAt init ω S = f} ∩
        {ω | CapLab init (fun i => (f i).role) (labelsAt init ω t)}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨labelsAt init ω S, rfl, h⟩
    · rintro ⟨f, hf, h⟩
      unfold CapState
      rw [hf]
      exact h
  rw [hset]
  refine MeasurableSet.iUnion fun f => MeasurableSet.inter ?_ ?_
  · exact ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono hSt) _
      ((show MeasurableSet {g : Lab init | g = f} from
        (Set.to_countable _).measurableSet).preimage (measurable_labelsAt init S))
  · exact (show MeasurableSet {g : Lab init | CapLab init (fun i => (f i).role) g} from
      (Set.to_countable _).measurableSet).preimage (measurable_labelsAt init t)

theorem highPhase_measurableSet (t : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | ∃ k, 4 ≤ (labelsAt init ω t k).phase.val} :=
  (show MeasurableSet {f : Lab init | ∃ k, 4 ≤ (f k).phase.val} from
    (Set.to_countable _).measurableSet).preimage (measurable_labelsAt init t)

theorem density_measurableSet (S : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 S]
      {ω | 6 * n ≤ 25 * clockCount (trace init ω S)} :=
  (show MeasurableSet {c : InputCfg n | 6 * n ≤ 25 * clockCount c} from
    (Set.to_countable _).measurableSet).preimage (measurable_trace_at init S)

/-- The P15 prefix: the genuine first Phase-3 seed at `S`, the Clock density at `S`, and
`z` the first all-cap time at or after `S`. -/
def capPrefix (S z : ℕ) : Set (InputLog n) :=
  {ω | firstPhaseSeed init 3 S ω ∧ S ≤ z ∧ 6 * n ≤ 25 * clockCount (trace init ω S) ∧
    CapState init ω S z ∧ ∀ u, S ≤ u → u < z → ¬ CapState init ω S u}

theorem capPrefix_measurableSet (S z : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 z]
      (capPrefix init S z) := by
  by_cases hSz : S ≤ z
  · have hmono := (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono hSz
    have h1 := hmono _ (firstPhaseSeed_measurableSet init 3 S)
    have h2 : MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 z]
        {ω : InputLog n | S ≤ z} := by
      simp only [hSz, Set.setOf_true]
      exact @MeasurableSet.univ _ (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 z)
    have h3 := hmono _ (density_measurableSet init S)
    have h4 := capState_measurableSet init hSz
    have h5 : MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 z]
        {ω | ∀ u, S ≤ u → u < z → ¬ CapState init ω S u} := by
      have hset : {ω : InputLog n | ∀ u, S ≤ u → u < z → ¬ CapState init ω S u} =
          ⋂ u, {ω | S ≤ u → u < z → ¬ CapState init ω S u} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [hset]
      refine MeasurableSet.iInter fun u => ?_
      by_cases hu : S ≤ u ∧ u < z
      · have hm := ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono hu.2.le) _
          (capState_measurableSet init hu.1).compl
        have hset' : {ω : InputLog n | S ≤ u → u < z → ¬ CapState init ω S u} =
            {ω | ¬ CapState init ω S u} := by
          ext ω
          simp only [Set.mem_setOf_eq, hu.1, hu.2, true_implies]
        rw [hset']
        exact hm
      · have hset' : {ω : InputLog n | S ≤ u → u < z → ¬ CapState init ω S u} = Set.univ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          intro h1 h2
          exact absurd ⟨h1, h2⟩ hu
        rw [hset']
        exact @MeasurableSet.univ _ (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 z)
    exact h1.inter (h2.inter (h3.inter (h4.inter h5)))
  · have hempty : capPrefix init S z = ∅ := by
      ext ω
      simp only [capPrefix, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hSz h.2.1
    rw [hempty]
    exact @MeasurableSet.empty _ (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 z)

theorem capPrefix_disjoint {a b : ℕ × ℕ} (hab : a ≠ b) :
    Disjoint (capPrefix init a.1 a.2) (capPrefix init b.1 b.2) := by
  rw [Set.disjoint_left]
  rintro ω ⟨ha1, ha2, -, ha4, ha5⟩ ⟨hb1, hb2, -, hb4, hb5⟩
  have hs : a.1 = b.1 := firstPhaseSeed_unique init 3 ω ha1 hb1
  have hz : a.2 ≠ b.2 := fun h => hab (Prod.ext hs h)
  rw [hs] at ha2 ha4 ha5
  rcases Nat.lt_or_gt_of_ne hz with hlt | hlt
  · exact hb5 a.2 ha2 hlt ha4
  · exact ha5 b.2 hb2 hlt hb4

open Classical in
/-- The first offset `t` after `z` at which some agent has phase at least four, as a
`WithTop ℕ`; killed at `0` outside the prefix `E`. -/
def exitStop (E : Set (InputLog n)) (z : ℕ) (ω : InputLog n) : WithTop ℕ :=
  if ω ∈ E then
    (if h : ∃ t, ∃ k, 4 ≤ (labelsAt init ω (z + t) k).phase.val then
      ((Nat.find h : ℕ) : WithTop ℕ) else ⊤)
  else 0

theorem exitStop_le_iff (E : Set (InputLog n)) (z t : ℕ) (ω : InputLog n) :
    exitStop init E z ω ≤ (t : WithTop ℕ) ↔
      ω ∉ E ∨ ∃ u ≤ t, ∃ k, 4 ≤ (labelsAt init ω (z + u) k).phase.val := by
  classical
  unfold exitStop
  by_cases hE : ω ∈ E
  · rw [if_pos hE]
    simp only [hE, not_true_eq_false, false_or]
    split_ifs with h
    · constructor
      · intro hle
        exact ⟨Nat.find h, WithTop.coe_le_coe.mp hle, Nat.find_spec h⟩
      · rintro ⟨u, hu, hk⟩
        exact WithTop.coe_le_coe.mpr ((Nat.find_min' h hk).trans hu)
    · constructor
      · intro hle
        exact absurd hle (not_le.mpr (WithTop.coe_lt_top t))
      · rintro ⟨u, -, hk⟩
        exact absurd ⟨u, hk⟩ h
  · rw [if_neg hE]
    simp only [hE, not_false_eq_true, true_or, iff_true]
    simp

theorem lt_exitStop_iff (E : Set (InputLog n)) (z t : ℕ) (ω : InputLog n) :
    (t : WithTop ℕ) < exitStop init E z ω ↔
      ω ∈ E ∧ ∀ u ≤ t, ∀ k, (labelsAt init ω (z + u) k).phase.val < 4 := by
  rw [← not_le, exitStop_le_iff]
  simp only [not_or, not_not, not_exists, not_and, not_le]

theorem exitStop_isStoppingTime (E : Set (InputLog n)) (z : ℕ)
    (hE : MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 z] E) :
    IsStoppingTime
      (shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) z)
      (exitStop init E z) := by
  intro t
  have hm : MeasurableSet[shiftedFiltration
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) z t]
      (Eᶜ ∪ ⋃ u, {ω | u ≤ t ∧ ∃ k, 4 ≤ (labelsAt init ω (z + u) k).phase.val}) := by
    refine MeasurableSet.union ?_ (MeasurableSet.iUnion fun u => ?_)
    · exact ((shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
        z).mono (Nat.zero_le t)) _ hE.compl
    · by_cases hu : u ≤ t
      · have hw : MeasurableSet[shiftedFiltration
            (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) z t]
            {ω | ∃ k, 4 ≤ (labelsAt init ω (z + u) k).phase.val} :=
          ((shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
            z).mono hu) _ (highPhase_measurableSet init (z + u))
        simpa only [hu, true_and] using hw
      · simp only [hu, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion]
  exact exitStop_le_iff init E z t ω

open Classical in
/-- The indicator that the pair drawn at `z + t + 1` is a tagged contact of the labelling
at `z + t`. -/
def tagIndicator (z t : ℕ) (ω : InputLog n) : ℝ :=
  if ∃ i j, drawLabels init ω (z + t + 1) = some (i, j) ∧
      TagContact init (auxLabels init (NonuniformMajority _ _).δ ω (z + t)) i j
  then (1 : ℝ) else 0

theorem tagIndicator_stronglyMeasurable (z t : ℕ) :
    StronglyMeasurable[shiftedFiltration
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) z (t + 1)]
      (tagIndicator init z t) := by
  have h := PhaseThreeClockProbabilityFloors.stronglyMeasurable_aux_pair_indicator init
    (NonuniformMajority _ _).δ (TagContact init) (z + t)
  simpa only [shiftedFiltration_apply, Nat.add_assoc, tagIndicator] using h

theorem tagIndicator_zero_one (z t : ℕ) (ω : InputLog n) :
    tagIndicator init z t ω = 0 ∨ tagIndicator init z t ω = 1 := by
  unfold tagIndicator
  split_ifs <;> simp

/-- The P15 contact floor `2 (6n - 25) / (25 n (n - 1)) ≤ 2 (C - 1) / (n (n - 1))`. -/
def exitRate (n : ℕ) : ℝ := 2 * (6 * (n : ℝ) - 25) / (25 * (n : ℝ) * ((n : ℝ) - 1))

theorem exitRate_le_one (hn : 2 ≤ n) : exitRate n ≤ 1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < 25 * (n : ℝ) * ((n : ℝ) - 1) := by
    apply mul_pos (by linarith) (by linarith)
  unfold exitRate
  rw [div_le_one hpos]
  nlinarith

theorem exitRate_le_ratio (hn : 40 ≤ n) (hcard : init.card = n) (r : Fin init.card → Role)
    (f : Lab init) (hf : CapLab init r f)
    (hdens : 6 * n ≤ 25 * (PhaseThreeClockGatedLaw.clockSet f).card) :
    exitRate n ≤ ((goodPairs (TagContact init) f).card : ℝ) /
      ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  have hC : 1 ≤ (PhaseThreeClockGatedLaw.clockSet f).card := by omega
  have hne : (PhaseThreeClockGatedLaw.clockSet f).Nonempty := Finset.card_pos.mp hC
  have hgp := goodPairs_tagContact_card init r f hf hne
  have hcardR : (init.card : ℝ) = n := by exact_mod_cast hcard
  rw [hcardR]
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := mul_pos (by linarith) (by linarith)
  have h25 : 0 < 25 * (n : ℝ) * ((n : ℝ) - 1) := by
    apply mul_pos (by linarith) (by linarith)
  have hgpR : (2 : ℝ) * (((PhaseThreeClockGatedLaw.clockSet f).card : ℝ) - 1) ≤
      (goodPairs (TagContact init) f).card := by
    have hcast : ((2 * ((PhaseThreeClockGatedLaw.clockSet f).card - 1) : ℕ) : ℝ) =
        2 * (((PhaseThreeClockGatedLaw.clockSet f).card : ℝ) - 1) := by
      push_cast [Nat.cast_sub hC]
      ring
    rw [← hcast]
    exact_mod_cast hgp
  have hdensR : (6 : ℝ) * n ≤ 25 * ((PhaseThreeClockGatedLaw.clockSet f).card : ℝ) := by
    exact_mod_cast hdens
  unfold exitRate
  rw [div_le_div_iff₀ h25 hpos]
  have hkey : 2 * (6 * (n : ℝ) - 25) ≤ 25 * ((goodPairs (TagContact init) f).card : ℝ) := by
    linarith
  have := mul_le_mul_of_nonneg_right hkey hpos.le
  nlinarith [this]

/-- The conditional contact floor given the past, on the stopped set. -/
theorem tagIndicator_condExp_floor (hn : 40 ≤ n) (hcard : init.card = n) (S z t : ℕ) :
    ∀ᵐ ω ∂law init, (t : WithTop ℕ) < exitStop init (capPrefix init S z) z ω →
      exitRate n ≤ ((law init)[tagIndicator init z t |
        shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) z t]) ω := by
  have hc : 2 ≤ init.card := by omega
  have h := aux_pair_conditional_probability init hc (NonuniformMajority _ _).δ (TagContact init)
    (z + t)
  filter_upwards [h] with ω hω
  intro hlt
  rw [lt_exitStop_iff] at hlt
  obtain ⟨hE, hlt4⟩ := hlt
  obtain ⟨-, -, hdens, hcapz, -⟩ := hE
  have hcap : CapState init ω S (z + t) :=
    capState_persist init ω hcapz
      (fun u hzu hut k => by
        have := hlt4 (u - z) (by omega) k
        rwa [show z + (u - z) = u by omega] at this) (z + t) (Nat.le_add_right z t) le_rfl
  have hfun : ((law init)[tagIndicator init z t |
      shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) z t]) ω =
      ((goodPairs (TagContact init)
        (auxLabels init (NonuniformMajority _ _).δ ω (z + t))).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := hω
  rw [hfun, ← labelsAt_eq_auxLabels_delta]
  have hroles : PhaseThreeClockGatedLaw.clockSet (labelsAt init ω (z + t)) =
      PhaseThreeClockGatedLaw.clockSet (labelsAt init ω S) := by
    ext i
    simp only [PhaseThreeClockGatedLaw.clockSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hr := hcap.1 i
    simp only [] at hr
    rw [hr]
  have hdens' : 6 * n ≤ 25 * (PhaseThreeClockGatedLaw.clockSet (labelsAt init ω (z + t))).card := by
    rw [hroles, clockSet_card_eq,
      show labelCfg (labelsAt init ω S) = trace init ω S from labelsAt_config init ω S]
    exact hdens
  exact exitRate_le_ratio init hn hcard _ _ (capState_capLab init ω hcap) hdens'

open Classical in
/-- On an all-cap stretch the tagged-contact count is the eligible-contact count of the
least Clock. -/
theorem bernoulliCount_tag_eq (S z N : ℕ)
    (hcap : ∀ u, z ≤ u → u ≤ z + N → CapState init ω S u)
    (i₀ : Fin init.card) (hi₀ : IsLeastClock init (labelsAt init ω S) i₀) :
    bernoulliCount (tagIndicator init z) N ω =
      (eligibleContacts init ω S i₀ z (z + N) : ℝ) := by
  induction N with
  | zero =>
      simp [bernoulliCount, eligibleContacts]
  | succ N ih =>
      have ih' := ih (fun u h1 h2 => hcap u h1 (by omega))
      have hsum : eligibleContacts init ω S i₀ z (z + (N + 1)) =
          eligibleContacts init ω S i₀ z (z + N) +
            (if eligibleContact init ω S i₀ (z + N + 1) then 1 else 0) := by
        unfold eligibleContacts
        rw [Finset.card_filter, Finset.card_filter, ← Nat.add_assoc,
          Finset.sum_Ioc_succ_top (Nat.le_add_right z N)]
      have hind : tagIndicator init z N ω =
          if eligibleContact init ω S i₀ (z + N + 1) then (1 : ℝ) else 0 := by
        have hiff := tagContact_iff_eligible init ω S (z + N)
          (hcap (z + N) (Nat.le_add_right z N) (by omega)) i₀ hi₀
        unfold tagIndicator
        rw [← labelsAt_eq_auxLabels_delta]
        by_cases hP : ∃ j l, drawLabels init ω (z + N + 1) = some (j, l) ∧
            TagContact init (labelsAt init ω (z + N)) j l
        · rw [if_pos hP, if_pos (hiff.mp hP)]
        · rw [if_neg hP, if_neg (fun hQ => hP (hiff.mpr hQ))]
      unfold bernoulliCount at ih' ⊢
      rw [Finset.sum_range_succ, ih', hsum, hind]
      try (by_cases hP : eligibleContact init ω S i₀ (z + N + 1) <;> simp [hP])

/-- The exponent of the P15 tail. -/
def exitBudget (n : ℕ) : ℝ :=
  Real.exp ((((50 * (PhaseThreeModel.Numeric.hourIndex n + 1) : ℕ) : ℝ) + 1) * Real.log 2 -
    exitRate n * (logWindow n 400 : ℝ) / 2)

/-- The P15 prefix tail: no exit through `z + logWindow n 400` on the prefix. -/
theorem exit_prefix_tail (hinput : ThresholdEpidemic.GoodInput n init) (S z : ℕ) :
    law init (capPrefix init S z ∩
        {ω | ((logWindow n 400 : ℕ) : WithTop ℕ) < exitStop init (capPrefix init S z) z ω}) ≤
      ENNReal.ofReal (exitBudget n) * law init (capPrefix init S z) := by
  have h40 : 40 ≤ n := (time_population_bounds hinput.1).2
  have hcard : init.card = n := hinput.2.2
  apply measure_le_of_real_weighted_bound (law init) _ _ _ (Real.exp_nonneg _)
  let ℱ := shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) z
  let E := capPrefix init S z
  have hE : MeasurableSet[ℱ 0] E := by
    simpa only [ℱ, shiftedFiltration_apply, Nat.add_zero] using capPrefix_measurableSet init S z
  have hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (tagIndicator init z t) :=
    fun t => tagIndicator_stronglyMeasurable init z t
  have hzeroOne : ∀ t, ∀ᵐ ω ∂law init,
      tagIndicator init z t ω = 0 ∨ tagIndicator init z t ω = 1 :=
    fun t => ae_of_all _ (tagIndicator_zero_one init z t)
  have hτ : IsStoppingTime ℱ (exitStop init E z) :=
    exitStop_isStoppingTime init E z (capPrefix_measurableSet init S z)
  have hp : exitRate n ≤ 1 := exitRate_le_one (by omega)
  have hcond : ∀ t : ℕ, ∀ᵐ ω ∂law init, (t : WithTop ℕ) < exitStop init E z ω →
      exitRate n ≤ ((law init)[tagIndicator init z t | ℱ t]) ω :=
    fun t => tagIndicator_condExp_floor init h40 hcard S z t
  have hfail : ∀ ω ∈ E, ((logWindow n 400 : ℕ) : WithTop ℕ) < exitStop init E z ω →
      bernoulliCount (tagIndicator init z) (logWindow n 400) ω <
        (((50 * (PhaseThreeModel.Numeric.hourIndex n + 1) : ℕ) : ℝ) + 1) := by
    intro ω hω hlt
    rw [lt_exitStop_iff] at hlt
    obtain ⟨-, hlt4⟩ := hlt
    obtain ⟨-, -, hdens, hcapz, -⟩ := hω
    have hcap : ∀ u, z ≤ u → u ≤ z + logWindow n 400 → CapState init ω S u :=
      capState_persist init ω hcapz (fun u hzu hut k => by
        have := hlt4 (u - z) (by omega) k
        rwa [show z + (u - z) = u by omega] at this)
    have hC : 1 ≤ (PhaseThreeClockGatedLaw.clockSet (labelsAt init ω S)).card := by
      rw [clockSet_card_eq,
        show labelCfg (labelsAt init ω S) = trace init ω S from labelsAt_config init ω S]
      omega
    have hne := Finset.card_pos.mp hC
    have hmemC : ∀ j, j ∈ PhaseThreeClockGatedLaw.clockSet (labelsAt init ω S) ↔
        (labelsAt init ω S j).role = .clock := by
      intro j
      simp only [PhaseThreeClockGatedLaw.clockSet, Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, IsLeastClock init (labelsAt init ω S) i₀ :=
      ⟨_, (hmemC _).mp (Finset.min'_mem _ hne),
        fun i' hi' => Finset.min'_le _ i' ((hmemC i').mpr hi')⟩
    rw [bernoulliCount_tag_eq init ω S z (logWindow n 400) hcap i₀ hi₀]
    have hle := eligibleContacts_le_of_no_exit init ω S z (logWindow n 400) i₀ hi₀.1
      (fun t h1 h2 => capState_allCapAt init ω (hcap t h1 h2))
      (fun t h1 h2 k => by
        have := (hcap t h1.le h2).2.1 k
        omega)
    have hleR : (eligibleContacts init ω S i₀ z (z + logWindow n 400) : ℝ) ≤
        ((50 * (PhaseThreeModel.Numeric.hourIndex n + 1) : ℕ) : ℝ) := by
      exact_mod_cast hle
    linarith
  exact prefix_success_hitting_tail hI hzeroOne hτ hp hcond E hE (logWindow n 400) _ hfail

/-- The P15 exponent is at most `n^{-12}` for `n ≥ 40`. -/
theorem exit_budget (hn : 40 ≤ n) : exitBudget n ≤ 1 / (n : ℝ) ^ 12 := by
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hlog3 : (3 : ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hpos]
    exact le_trans PhaseThreeClockBudget.exp_three_le (by linarith)
  have hlog2 := PhaseThreeModel.Numeric.log_two_bounds
  have hH : (PhaseThreeModel.Numeric.hourIndex n : ℝ) ≤ 3 / 2 * Real.log n + 1 := by
    rw [PhaseThreeModel.Numeric.hourIndex_eq_real_ceiling]
    have h1 : Real.log n / Real.log 2 ≤ 3 / 2 * Real.log n := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hlog2.1, hlog3]
    have h2 := Nat.ceil_lt_add_one (show 0 ≤ Real.log n / Real.log 2 by
      apply div_nonneg (by linarith) (by linarith))
    linarith
  have hN : (400 : ℝ) * n * Real.log n ≤ (logWindow n 400 : ℝ) :=
    PhaseThreeClockExit.logWindow_ge_real 400
  have hx : (n : ℝ) ≠ 0 := by linarith
  have hx1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hrate : 88 * Real.log n ≤ exitRate n * (logWindow n 400 : ℝ) / 2 := by
    have hden : 0 < 25 * (n : ℝ) * ((n : ℝ) - 1) := by
      apply mul_pos (by linarith) (by linarith)
    have h1 : (6 * (n : ℝ) - 25) * (400 * n * Real.log n) ≤
        (6 * (n : ℝ) - 25) * (logWindow n 400 : ℝ) :=
      mul_le_mul_of_nonneg_left hN (by linarith)
    have hkey : 88 * Real.log n * (25 * (n : ℝ) * ((n : ℝ) - 1)) ≤
        (6 * (n : ℝ) - 25) * (logWindow n 400 : ℝ) := by
      nlinarith [h1, mul_nonneg (mul_nonneg hpos.le (by linarith : (0 : ℝ) ≤ Real.log n))
        (by linarith : (0 : ℝ) ≤ 200 * (n : ℝ) - 7800)]
    calc 88 * Real.log n
        = 88 * Real.log n * (25 * (n : ℝ) * ((n : ℝ) - 1)) /
            (25 * (n : ℝ) * ((n : ℝ) - 1)) := by
          field_simp
      _ ≤ (6 * (n : ℝ) - 25) * (logWindow n 400 : ℝ) / (25 * (n : ℝ) * ((n : ℝ) - 1)) :=
          div_le_div_of_nonneg_right hkey hden.le
      _ = exitRate n * (logWindow n 400 : ℝ) / 2 := by
          unfold exitRate
          field_simp
          try ring
  have hk : (((50 * (PhaseThreeModel.Numeric.hourIndex n + 1) : ℕ) : ℝ) + 1) ≤
      75 * Real.log n + 101 := by
    push_cast
    linarith
  have hklog : (((50 * (PhaseThreeModel.Numeric.hourIndex n + 1) : ℕ) : ℝ) + 1) * Real.log 2 ≤
      (75 * Real.log n + 101) * (25 / 36) :=
    mul_le_mul hk hlog2.2 (by linarith [hlog2.1]) (by linarith)
  have hexp : (((50 * (PhaseThreeModel.Numeric.hourIndex n + 1) : ℕ) : ℝ) + 1) * Real.log 2 -
      exitRate n * (logWindow n 400 : ℝ) / 2 ≤ -(12 * Real.log n) := by
    linarith
  unfold exitBudget
  calc Real.exp _ ≤ Real.exp (-(12 * Real.log n)) := Real.exp_le_exp.mpr hexp
    _ = 1 / (n : ℝ) ^ 12 := by
        rw [Real.exp_neg, one_div]
        congr 1
        rw [show (12 : ℝ) * Real.log n = ((12 : ℕ) : ℝ) * Real.log n by norm_num,
          Real.exp_nat_mul, Real.exp_log hpos]

/-! ## The headline inclusion and the tail -/

theorem firstAfter_unique {P : ℕ → Prop} {S t t' : ℕ} (h : firstAfter P S t)
    (h' : firstAfter P S t') : t = t' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.2.2 t h.1 hlt h.2.1
  · exact h.2.2 t' h'.1 hlt h'.2.1

/-- On a virtual core with no genuine Phase-4 seed through `M ≤ cap + logWindow n 400`,
every actual phase stays below four through `M`. -/
theorem phases_lt_four_of_no_seed {S T : ℕ} {w : ClockTimes init}
    (hentry : AsyncEntry init ω S T) (hcore : VirtualClockCore init ω S T w)
    (M : ℕ) (hM : M ≤ w.cap + logWindow n 400)
    (hno : ∀ ρ ≤ M, ¬ firstPhaseSeed init 4 ρ ω) :
    ∀ u ≤ M, ∀ i, (labelsAt init ω u i).phase.val < 4 := by
  have hseed := hentry.first_phase_seed
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro huM i
  rcases Nat.lt_or_ge u S with huS | huS
  · have := hseed.2 u huS _ (labelsAt_mem_trace init ω u i)
    omega
  · have hprev : ∀ u' < u, ∀ k, (labelsAt init ω u' k).phase.val < 4 :=
      fun u' hu' k => ih u' hu' (by omega) k
    rcases Nat.eq_zero_or_pos u with hu0 | hupos
    · subst hu0
      have hmem : virtualLabels init ω 0 i ∈ virtualCfg init ω 0 :=
        Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩
      have := (hcore.phase_range 0 (by omega) (by omega) _ hmem).2
      rw [virtualLabels_zero] at this
      omega
    · obtain ⟨r, rfl⟩ : ∃ r, u = r + 1 := ⟨u - 1, by omega⟩
      have hagree : ∀ t ≤ r, virtualLabels init ω t = labelsAt init ω t :=
        virtualLabels_eq_labelsAt_of_phases_lt_four init ω r
          (fun u' hu' k => hprev u' (by omega) k)
      cases hd : drawLabels init ω (r + 1) with
      | none =>
          have hstep := labelsAt_succ_eq_auxStep init ω r
          rw [hd] at hstep
          simp only [auxStep] at hstep
          rw [hstep]
          exact hprev r (by omega) i
      | some ab =>
          obtain ⟨a, b⟩ := ab
          obtain ⟨hab, ha, hb, hother⟩ := labelsAt_selected_transition init ω r a b hd
          by_cases hce : CounterExitPair (labelsAt init ω r a) (labelsAt init ω r b)
          · exfalso
            apply hno (r + 1) huM
            refine ⟨?_, fun u' hu' x hx => ?_⟩
            · rcases transition_phase_eq_four_of_exit _ _ hce with h4 | h4
              · exact ⟨labelsAt init ω (r + 1) a, labelsAt_mem_trace init ω (r + 1) a,
                  by rw [ha]; exact h4⟩
              · exact ⟨labelsAt init ω (r + 1) b, labelsAt_mem_trace init ω (r + 1) b,
                  by rw [hb]; exact h4⟩
            · rw [← labelsAt_config] at hx
              obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp hx
              rw [← hk]
              exact hprev u' hu' k
          · have hrule : virtualRule (labelsAt init ω r a) (labelsAt init ω r b) =
                (NonuniformMajority _ _).δ (labelsAt init ω r a) (labelsAt init ω r b) :=
              virtualRule_eq_transition _ _ hce
            have hv : labelsAt init ω (r + 1) = virtualLabels init ω (r + 1) := by
              rw [virtualLabels_succ, hd, labelsAt_succ_eq_auxStep, hd, hagree r le_rfl]
              simp only [auxStep, ruleUpdate, hrule]
            have hmem : virtualLabels init ω (r + 1) i ∈ virtualCfg init ω (r + 1) :=
              Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩
            have := (hcore.phase_range (r + 1) (by omega) (by omega) _ hmem).2
            rw [← hv] at this
            omega

/-- The exit-deadline failure is covered by the prefixes with no exit through
`z + logWindow n 400`. -/
theorem exit_bad_subset :
    {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
        VirtualGoodAt init s ω ∧ ¬ ExitDeadlineAt init s ω} ⊆
      ⋃ sz : ℕ × ℕ, capPrefix init sz.1 sz.2 ∩
        {ω | ((logWindow n 400 : ℕ) : WithTop ℕ) <
          exitStop init (capPrefix init sz.1 sz.2) sz.2 ω} := by
  rintro ω ⟨s, hs, hv, hnd⟩
  obtain ⟨T, w, hT, hentry, hcore⟩ := hv
  have hseed : firstPhaseSeed init 3 s ω := (seedTime_eq_iff init 3 ω s).mp hs
  have hno : ∀ ρ ≤ w.cap + logWindow n 400, ¬ firstPhaseSeed init 4 ρ ω := by
    intro ρ hρ hexit
    apply hnd
    refine ⟨ρ, hexit, fun T' w' _ _ hcore' => ?_⟩
    have hcap' : w'.cap = w.cap := firstAfter_unique hcore'.cap_first hcore.cap_first
    rw [hcap']
    exact hρ
  have hlt4 := phases_lt_four_of_no_seed init ω hentry hcore (w.cap + logWindow n 400) le_rfl hno
  have hagree : ∀ t ≤ w.cap + logWindow n 400, virtualLabels init ω t = labelsAt init ω t :=
    virtualLabels_eq_labelsAt_of_phases_lt_four init ω (w.cap + logWindow n 400) hlt4
  have hScap : s ≤ w.cap := seed_le_cap init ω hcore
  have hTcap : T ≤ w.cap := hcore.all_before_cap
  have hvcfg : virtualCfg init ω s = trace init ω s := by
    change labelCfg (virtualLabels init ω s) = trace init ω s
    rw [hagree s (by omega)]
    exact labelsAt_config init ω s
  have hdens : 6 * n ≤ 25 * clockCount (trace init ω s) := by
    have := (hcore.density s le_rfl (by omega)).2.2.1
    rwa [hvcfg] at this
  have hcapz : CapState init ω s w.cap := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have := hcore.roles_fixed w.cap hScap (by omega) i
      rwa [hagree w.cap (by omega), hagree s (by omega)] at this
    · intro i
      have hmem : virtualLabels init ω w.cap i ∈ virtualCfg init ω w.cap :=
        Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩
      have := hcore.all_three w.cap hTcap (by omega) _ hmem
      rwa [hagree w.cap (by omega)] at this
    · intro i hi
      have hfc : frontCountL init (virtualLabels init ω s) (virtualLabels init ω w.cap)
          (clockTop n) = clockCount (labelCfg (virtualLabels init ω s)) :=
        hcore.cap_first.2.1
      have hcc := capClocks_of_frontCount_eq init _ _ hfc i
        (by rw [hagree s (by omega)]; exact hi)
      rw [hagree w.cap (by omega)] at hcc
      exact hcc.2
  have hmin : ∀ u, s ≤ u → u < w.cap → ¬ CapState init ω s u := by
    intro u hsu huz hcs
    apply hcore.cap_first.2.2 u hsu huz
    show frontCountL init (virtualLabels init ω s) (virtualLabels init ω u) (clockTop n) =
      clockCount (labelCfg (virtualLabels init ω s))
    rw [hagree u (by omega), hagree s (by omega)]
    exact frontCount_eq_of_capLab init _ _ _ (fun i => rfl) hcs
  refine Set.mem_iUnion.mpr ⟨(s, w.cap), ⟨hseed, hScap, hdens, hcapz, hmin⟩, ?_⟩
  show ((logWindow n 400 : ℕ) : WithTop ℕ) < exitStop init (capPrefix init s w.cap) w.cap ω
  rw [lt_exitStop_iff]
  refine ⟨⟨hseed, hScap, hdens, hcapz, hmin⟩, fun u hu k => hlt4 (w.cap + u) (by omega) k⟩

/-- The exit-deadline tail: the input `hexit` of
`PhaseThreeClockBudget.asynchronous_clock_estimate_of_tails`. -/
theorem exit_deadline_tail (hinput : ThresholdEpidemic.GoodInput n init) :
    law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      VirtualGoodAt init s ω ∧ ¬ ExitDeadlineAt init s ω} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 12) := by
  have h40 : 40 ≤ n := (time_population_bounds hinput.1).2
  have hdisj : Pairwise (Function.onFun Disjoint fun sz : ℕ × ℕ => capPrefix init sz.1 sz.2) :=
    fun a b hab => capPrefix_disjoint init hab
  have hmeas : ∀ sz : ℕ × ℕ, MeasurableSet (capPrefix init sz.1 sz.2) :=
    fun sz => (pairLogFiltration _ _).le _ _ (capPrefix_measurableSet init sz.1 sz.2)
  have hsum : ∑' sz : ℕ × ℕ, law init (capPrefix init sz.1 sz.2) ≤ 1 := by
    rw [← measure_iUnion hdisj hmeas]
    exact prob_le_one
  calc law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
        VirtualGoodAt init s ω ∧ ¬ ExitDeadlineAt init s ω}
      ≤ law init (⋃ sz : ℕ × ℕ, capPrefix init sz.1 sz.2 ∩
          {ω | ((logWindow n 400 : ℕ) : WithTop ℕ) <
            exitStop init (capPrefix init sz.1 sz.2) sz.2 ω}) :=
        measure_mono (exit_bad_subset init)
    _ ≤ ∑' sz : ℕ × ℕ, law init (capPrefix init sz.1 sz.2 ∩
          {ω | ((logWindow n 400 : ℕ) : WithTop ℕ) <
            exitStop init (capPrefix init sz.1 sz.2) sz.2 ω}) := measure_iUnion_le _
    _ ≤ ∑' sz : ℕ × ℕ, ENNReal.ofReal (exitBudget n) * law init (capPrefix init sz.1 sz.2) :=
        ENNReal.tsum_le_tsum (fun sz => exit_prefix_tail init hinput sz.1 sz.2)
    _ = ENNReal.ofReal (exitBudget n) * ∑' sz : ℕ × ℕ, law init (capPrefix init sz.1 sz.2) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (exitBudget n) * 1 := mul_le_mul_right hsum _
    _ = ENNReal.ofReal (exitBudget n) := mul_one _
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 12) := ENNReal.ofReal_le_ofReal (exit_budget h40)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockExitTail

end

import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRows
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEmbeddingBridge

/-!
# The counter reserve from the contact budget (N12, step 4, P14 transfer part)

On the virtual continuation a Phase-3 Clock's counter changes only at a cap counter
pair, where it decreases by exactly one (saturated at zero), and a cap counter pair
drawn for the tagged Clock is an eligible contact (`StageEventSpec.eligibleContact`
in its path-generic form). Hence from its genuine initialization, with counter
`50 (H + 1)`, through any time with fewer than `40 (H + 1)` eligible contacts the
counter stays at least `10 (H + 1) + 1`. This discharges the row
`PhaseThreeClockRows.RowReserve` from `RowActivation` (counter reset, initialization)
and `RowContact` (contact budget); `virtual_core_tail_of_row_tails` is `hcore` from the
six probabilistic row tails and the regime row.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockReserve

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge PhaseThreeClockCore PhaseThreeClockTransfer
  PhaseThreeClockProducer PhaseThreeClockRows

/-! ## One interaction of a Phase-3 Clock -/

section Agent

variable {L K : ℕ}

/-- Without backup the epidemic leaves the higher Phase-3 endpoint unchanged and puts the
other endpoint in Phase 3. -/
theorem epidemic_left_of_phase_three (s x : AgentState L K) (hs3 : s.phase.val = 3)
    (hx3 : x.phase.val ≤ 3)
    (hnb : (phaseEpidemicUpdate L K s x).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K s x).2.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s x).1 = s ∧ (phaseEpidemicUpdate L K s x).2.phase.val = 3 := by
  have hepi := phaseEpidemicUpdate_eq_of_no_backup s x (by omega) (by omega) hnb
  have hmax : max s.phase x.phase = s.phase :=
    max_eq_left (Fin.le_iff_val_le_val.mpr (by omega))
  rw [hmax, runInitsBetween_self] at hepi
  refine ⟨by rw [hepi], ?_⟩
  rcases runInitsBetween_phase_eq_or_ten x.phase.val s.phase.val { x with phase := s.phase }
      with h | h
  · rw [hepi]
    simp only []
    rw [h]
    exact hs3
  · exfalso
    apply hnb.2
    rw [hepi]
    exact h

theorem epidemic_right_of_phase_three (x s : AgentState L K) (hs3 : s.phase.val = 3)
    (hx3 : x.phase.val ≤ 3)
    (hnb : (phaseEpidemicUpdate L K x s).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K x s).2.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K x s).2 = s ∧ (phaseEpidemicUpdate L K x s).1.phase.val = 3 := by
  have hepi := phaseEpidemicUpdate_eq_of_no_backup x s (by omega) (by omega) hnb
  have hmax : max x.phase s.phase = s.phase :=
    max_eq_right (Fin.le_iff_val_le_val.mpr (by omega))
  rw [hmax, runInitsBetween_self] at hepi
  refine ⟨by rw [hepi], ?_⟩
  rcases runInitsBetween_phase_eq_or_ten x.phase.val s.phase.val { x with phase := s.phase }
      with h | h
  · rw [hepi]
    simp only []
    rw [h]
    exact hs3
  · exfalso
    apply hnb.1
    rw [hepi]
    exact h

/-- A Phase-3 Clock as initiator: phase stays three, the counter drops by at most one and
only at a cap counter pair. -/
theorem virtualRule_clock_counter_left (s x : AgentState L K) (hs3 : s.phase.val = 3)
    (hsr : s.role = .clock) (hx3 : x.phase.val ≤ 3)
    (hnb : (phaseEpidemicUpdate L K s x).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K s x).2.phase.val ≠ 10) :
    (virtualRule s x).1.phase.val = 3 ∧
    s.counter.val ≤ (virtualRule s x).1.counter.val +
      (if CapCounterPair s x then 1 else 0) := by
  obtain ⟨hpe1, hpe2⟩ := epidemic_left_of_phase_three s x hs3 hx3 hnb
  by_cases hcap : CapCounterPair s x
  · rw [if_pos hcap]
    unfold virtualRule
    rw [if_pos hcap]
    simp only [saturatedCounterStep_phase, saturatedCounterStep_counter, hpe1]
    exact ⟨hs3, by omega⟩
  · rw [if_neg hcap, add_zero, virtualRule_eq_transition_of_not_cap s x hcap,
      transition_eq_phase3_of_dispatch s x (by rw [hpe1]; exact hs3), hpe1]
    simp only []
    set x' := (phaseEpidemicUpdate L K s x).2 with hx'
    by_cases hxr : x'.role = .clock
    · by_cases hne : s.minute = x'.minute
      · by_cases hlt : s.minute.val < K * (L + 1)
        · rw [phase3Transition_drip s x' hsr hxr hne hlt,
            finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by simp [hs3])]
          simp [hs3]
        · exfalso
          apply hcap
          refine ⟨by rw [hpe1]; exact hs3, hpe2, by rw [hpe1]; exact hsr, hxr, ?_, ?_⟩
          · rw [hpe1]; exact hne
          · rw [hpe1]
            have := s.minute.isLt
            omega
      · rw [phase3Transition_copy s x' hsr hxr hne,
          finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by simp [hs3])]
        simp [hs3]
    · rw [phase3Transition_clock_left s x' hsr hxr,
        finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by show s.phase.val ≠ 10; omega)]
      exact ⟨hs3, le_rfl⟩

/-- A Phase-3 Clock as responder. -/
theorem virtualRule_clock_counter_right (x s : AgentState L K) (hs3 : s.phase.val = 3)
    (hsr : s.role = .clock) (hx3 : x.phase.val ≤ 3)
    (hnb : (phaseEpidemicUpdate L K x s).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K x s).2.phase.val ≠ 10) :
    (virtualRule x s).2.phase.val = 3 ∧
    s.counter.val ≤ (virtualRule x s).2.counter.val +
      (if CapCounterPair x s then 1 else 0) := by
  obtain ⟨hpe2, hpe1⟩ := epidemic_right_of_phase_three x s hs3 hx3 hnb
  by_cases hcap : CapCounterPair x s
  · rw [if_pos hcap]
    unfold virtualRule
    rw [if_pos hcap]
    simp only [saturatedCounterStep_phase, saturatedCounterStep_counter, hpe2]
    exact ⟨hs3, by omega⟩
  · rw [if_neg hcap, add_zero, virtualRule_eq_transition_of_not_cap x s hcap,
      transition_eq_phase3_of_dispatch x s hpe1, hpe2]
    simp only []
    set x' := (phaseEpidemicUpdate L K x s).1 with hx'
    by_cases hxr : x'.role = .clock
    · by_cases hne : x'.minute = s.minute
      · by_cases hlt : x'.minute.val < K * (L + 1)
        · rw [phase3Transition_drip x' s hxr hsr hne hlt,
            finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by show s.phase.val ≠ 10; omega)]
          exact ⟨hs3, le_rfl⟩
        · exfalso
          apply hcap
          refine ⟨hpe1, by rw [hpe2]; exact hs3, hxr, by rw [hpe2]; exact hsr, ?_, ?_⟩
          · rw [hpe2]; exact hne
          · rw [← hx']
            have := x'.minute.isLt
            omega
      · rw [phase3Transition_copy x' s hxr hsr hne,
          finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by simp [hs3])]
        simp [hs3]
    · rw [phase3Transition_clock_right x' s hxr hsr,
        finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by show s.phase.val ≠ 10; omega)]
      exact ⟨hs3, le_rfl⟩

/-- A cap counter pair at a Phase-3 Clock with a partner in the Clock regime (if a Clock)
is an eligible contact: both endpoints are Phase-3 Clocks at the cap before the
interaction. -/
theorem capCounterPair_eligible (hK : 0 < K) (s x : AgentState L K) (hs3 : s.phase.val = 3)
    (hx1 : 1 ≤ x.phase.val) (hx3 : x.phase.val ≤ 3) (hxsb : x.role = .clock → x.smallBias.val = 3)
    (hcap : CapCounterPair s x) :
    x.role = .clock ∧ x.phase.val = 3 ∧ s.minute.val = K * (L + 1) ∧
      x.minute.val = K * (L + 1) := by
  obtain ⟨h3, h3', hsr, hxr, hmin, hm⟩ := hcap
  have hnb : (phaseEpidemicUpdate L K s x).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K s x).2.phase.val ≠ 10 := ⟨by omega, by omega⟩
  have hepi := phaseEpidemicUpdate_eq_of_no_backup s x (by omega) (by omega) hnb
  have hmaxp : max s.phase x.phase = s.phase :=
    max_eq_left (Fin.le_iff_val_le_val.mpr (by omega))
  rw [hmaxp, runInitsBetween_self] at hepi
  rw [hepi] at hxr hmin hm
  simp only [] at hxr hmin hm
  have hxr' : x.role = .clock := by
    have h := runInitsBetween_role_clock_of_output _ _ _ hxr
    exact h
  rcases Nat.lt_or_ge x.phase.val 3 with hlt | hge
  · exfalso
    have hup := runInitsBetween_clock_up x.phase.val s.phase.val hx1 (by omega) (by omega)
      { x with phase := s.phase } hxr' (hxsb hxr')
    have hmin0 := hup.2.2.2.1
    rw [if_pos hs3] at hmin0
    have hxm : (runInitsBetween L K x.phase.val s.phase.val { x with phase := s.phase }).minute.val =
        s.minute.val := by rw [← hmin]
    rw [hmin0] at hxm
    rw [← hxm] at hm
    exact absurd hm.symm (Nat.pos_iff_ne_zero.mp (Nat.mul_pos hK (Nat.succ_pos L)))
  · have hx3' : x.phase.val = 3 := by omega
    have hxp : x.phase = s.phase := Fin.ext (by omega)
    rw [← hxp, runInitsBetween_self] at hmin
    refine ⟨hxr', hx3', hm, ?_⟩
    rw [← hmin]
    exact hm

/-- The responder version of `capCounterPair_eligible`. -/
theorem capCounterPair_eligible_right (hK : 0 < K) (x s : AgentState L K) (hs3 : s.phase.val = 3)
    (hx1 : 1 ≤ x.phase.val) (hx3 : x.phase.val ≤ 3) (hxsb : x.role = .clock → x.smallBias.val = 3)
    (hcap : CapCounterPair x s) :
    x.role = .clock ∧ x.phase.val = 3 ∧ s.minute.val = K * (L + 1) ∧
      x.minute.val = K * (L + 1) := by
  obtain ⟨h3, h3', hxr, hsr, hmin, hm⟩ := hcap
  have hnb : (phaseEpidemicUpdate L K x s).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K x s).2.phase.val ≠ 10 := ⟨by omega, by omega⟩
  have hepi := phaseEpidemicUpdate_eq_of_no_backup x s (by omega) (by omega) hnb
  have hmaxp : max x.phase s.phase = s.phase :=
    max_eq_right (Fin.le_iff_val_le_val.mpr (by omega))
  rw [hmaxp, runInitsBetween_self] at hepi
  rw [hepi] at hxr hmin hm
  simp only [] at hxr hmin hm
  have hxr' : x.role = .clock := by
    have h := runInitsBetween_role_clock_of_output _ _ _ hxr
    exact h
  rcases Nat.lt_or_ge x.phase.val 3 with hlt | hge
  · exfalso
    have hup := runInitsBetween_clock_up x.phase.val s.phase.val hx1 (by omega) (by omega)
      { x with phase := s.phase } hxr' (hxsb hxr')
    have hmin0 := hup.2.2.2.1
    rw [if_pos hs3] at hmin0
    rw [hmin0] at hm
    exact absurd hm.symm (Nat.pos_iff_ne_zero.mp (Nat.mul_pos hK (Nat.succ_pos L)))
  · have hx3' : x.phase.val = 3 := by omega
    have hxp : x.phase = s.phase := Fin.ext (by omega)
    rw [← hxp, runInitsBetween_self] at hmin hm
    exact ⟨hxr', hx3', by rw [← hmin]; exact hm, hm⟩

end Agent

/-! ## The ledger along the virtual path -/

variable {n : ℕ} (init : InputCfg n) (ω : InputLog n)

theorem virtualLabels_succ_left {t : ℕ} {j l : Fin init.card}
    (hd : drawLabels init ω (t + 1) = some (j, l)) (hjl : j ≠ l) :
    virtualLabels init ω (t + 1) j =
      (virtualRule (virtualLabels init ω t j) (virtualLabels init ω t l)).1 := by
  rw [virtualLabels_succ, hd]
  simp only [auxStep, ruleUpdate, Function.update_of_ne hjl, Function.update_self]

theorem virtualLabels_succ_right {t : ℕ} {j l : Fin init.card}
    (hd : drawLabels init ω (t + 1) = some (j, l)) :
    virtualLabels init ω (t + 1) l =
      (virtualRule (virtualLabels init ω t j) (virtualLabels init ω t l)).2 := by
  rw [virtualLabels_succ, hd]
  simp only [auxStep, ruleUpdate, Function.update_self]

theorem virtualLabels_succ_other {t : ℕ} {j l k : Fin init.card}
    (hd : drawLabels init ω (t + 1) = some (j, l)) (hkj : k ≠ j) (hkl : k ≠ l) :
    virtualLabels init ω (t + 1) k = virtualLabels init ω t k := by
  rw [virtualLabels_succ, hd]
  simp only [auxStep, ruleUpdate, Function.update_of_ne hkj, Function.update_of_ne hkl]

theorem virtualLabels_succ_none {t : ℕ} (hd : drawLabels init ω (t + 1) = none) :
    virtualLabels init ω (t + 1) = virtualLabels init ω t := by
  rw [virtualLabels_succ, hd]
  rfl

open Classical in
theorem eligibleContactsL_succ (S : ℕ) (i : Fin init.card) {u v : ℕ} (huv : u ≤ v) :
    eligibleContactsL init (virtualLabels init ω) (drawLabels init ω) S i u (v + 1) =
      eligibleContactsL init (virtualLabels init ω) (drawLabels init ω) S i u v +
        (if eligibleContactL init (virtualLabels init ω) (drawLabels init ω) S i (v + 1)
          then 1 else 0) := by
  unfold eligibleContactsL
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_Ioc_succ_top huv]

theorem eligibleContactsL_mono (S : ℕ) (i : Fin init.card) {u v v' : ℕ} (hvv : v ≤ v') :
    eligibleContactsL init (virtualLabels init ω) (drawLabels init ω) S i u v ≤
      eligibleContactsL init (virtualLabels init ω) (drawLabels init ω) S i u v' := by
  classical
  unfold eligibleContactsL
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hvv))

/-- The virtual counter ledger from a time `τ ≥ S` at which the tagged Clock is in
Phase 3: the counter plus the eligible contacts never decreases, and the phase stays
three. -/
theorem virtual_counter_ledger {S T : ℕ} (hentry : AsyncEntry init ω S T) (i : Fin init.card)
    (hi : (virtualLabels init ω S i).role = .clock) (τ : ℕ) (hSτ : S ≤ τ)
    (hτ3 : (virtualLabels init ω τ i).phase.val = 3) (v : ℕ) (hτv : τ ≤ v) :
    (virtualLabels init ω v i).phase.val = 3 ∧
    (virtualLabels init ω τ i).counter.val ≤ (virtualLabels init ω v i).counter.val +
      eligibleContactsL init (virtualLabels init ω) (drawLabels init ω) S i τ v := by
  classical
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry
  have hroles := virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry
  have hrv : ∀ u, S ≤ u → ∀ k, (virtualLabels init ω u k).role = (virtualLabels init ω S k).role :=
    fun u hu k => (hroles u hu k).trans (hroles S le_rfl k).symm
  induction v, hτv using Nat.le_induction with
  | base =>
      refine ⟨hτ3, ?_⟩
      unfold eligibleContactsL
      rw [Finset.Ioc_self, Finset.filter_empty, Finset.card_empty, add_zero]
  | succ v hτv ih =>
      obtain ⟨ih3, ihc⟩ := ih
      rw [eligibleContactsL_succ init ω S i hτv]
      have hphase3 := fun k => ((henv (v + 1) (by omega)).phase_range k).2
      have hvrange := fun k => (henv v (by omega)).phase_range k
      have hSv : S ≤ v := by omega
      cases hd : drawLabels init ω (v + 1) with
      | none =>
          rw [virtualLabels_succ_none init ω hd]
          exact ⟨ih3, by omega⟩
      | some jl =>
          obtain ⟨j, l⟩ := jl
          have hjl : j ≠ l := (labelsAt_selected_transition init ω v j l hd).1
          have hj := virtualLabels_succ_left init ω hd hjl
          have hl := virtualLabels_succ_right init ω hd
          have hnb : (phaseEpidemicUpdate _ _ (virtualLabels init ω v j)
                (virtualLabels init ω v l)).1.phase.val ≠ 10 ∧
              (phaseEpidemicUpdate _ _ (virtualLabels init ω v j)
                (virtualLabels init ω v l)).2.phase.val ≠ 10 :=
            virtualRule_no_backup_of_phase_le_three _ _
              (by rw [← hj]; exact hphase3 j) (by rw [← hl]; exact hphase3 l)
          by_cases hij : i = j
          · subst hij
            have hir : (virtualLabels init ω v i).role = .clock := by rw [hrv v hSv]; exact hi
            have hc := virtualRule_clock_counter_left (virtualLabels init ω v i)
              (virtualLabels init ω v l) ih3 hir (hvrange l).2 hnb
            rw [hj]
            refine ⟨hc.1, ?_⟩
            have hcapelig : CapCounterPair (virtualLabels init ω v i) (virtualLabels init ω v l) →
                eligibleContactL init (virtualLabels init ω) (drawLabels init ω) S i (v + 1) := by
              intro hcap
              have hlreg : (virtualLabels init ω v l).role = .clock →
                  (virtualLabels init ω v l).smallBias.val = 3 :=
                fun hc => ((henv v hSv).clock_regime l hc).small
              obtain ⟨hlr, hl3, him, hlm⟩ := capCounterPair_eligible (by norm_num) _ _ ih3
                (hvrange l).1 (hvrange l).2 hlreg hcap
              refine ⟨by omega, i, l, hd, Or.inl rfl, hi, ?_, ?_, ?_, ?_, ?_⟩
              · show (virtualLabels init ω S l).role = .clock
                rw [← hrv v hSv]
                exact hlr
              · simpa using ih3
              · simpa using hl3
              · simpa using him
              · simpa using hlm
            have hc2 := hc.2
            by_cases hcap : CapCounterPair (virtualLabels init ω v i) (virtualLabels init ω v l)
            · rw [if_pos hcap] at hc2
              rw [if_pos (hcapelig hcap)]
              omega
            · rw [if_neg hcap, add_zero] at hc2
              split_ifs <;> omega
          by_cases hil : i = l
          · subst hil
            have hir : (virtualLabels init ω v i).role = .clock := by rw [hrv v hSv]; exact hi
            have hc := virtualRule_clock_counter_right (virtualLabels init ω v j)
              (virtualLabels init ω v i) ih3 hir (hvrange j).2 hnb
            rw [hl]
            refine ⟨hc.1, ?_⟩
            have hcapelig : CapCounterPair (virtualLabels init ω v j) (virtualLabels init ω v i) →
                eligibleContactL init (virtualLabels init ω) (drawLabels init ω) S i (v + 1) := by
              intro hcap
              have hjreg : (virtualLabels init ω v j).role = .clock →
                  (virtualLabels init ω v j).smallBias.val = 3 :=
                fun hc => ((henv v hSv).clock_regime j hc).small
              obtain ⟨hjr, hj3, him, hjm⟩ := capCounterPair_eligible_right (by norm_num) _ _ ih3
                (hvrange j).1 (hvrange j).2 hjreg hcap
              refine ⟨by omega, j, i, hd, Or.inr rfl, ?_, hi, ?_, ?_, ?_, ?_⟩
              · show (virtualLabels init ω S j).role = .clock
                rw [← hrv v hSv]
                exact hjr
              · simpa using hj3
              · simpa using ih3
              · simpa using hjm
              · simpa using him
            have hc2 := hc.2
            by_cases hcap : CapCounterPair (virtualLabels init ω v j) (virtualLabels init ω v i)
            · rw [if_pos hcap] at hc2
              rw [if_pos (hcapelig hcap)]
              omega
            · rw [if_neg hcap, add_zero] at hc2
              split_ifs <;> omega
          · rw [virtualLabels_succ_other init ω hd hij hil]
            exact ⟨ih3, by omega⟩

/-! ## The reserve row -/

theorem reserve_arith {c₀ cv e₁ e₂ H : ℕ} (hA : c₀ ≤ cv + e₁) (hB : e₁ ≤ e₂)
    (hC : e₂ < 40 * (H + 1)) (hD : c₀ = 50 * (H + 1)) : 10 * (H + 1) + 1 ≤ cv := by
  omega

/-- `RowReserve` from the counter reset, the genuine initialization and the contact
budget, on the virtual path from an entry. -/
theorem rowReserve_of_rows {S T : ℕ} (hentry : AsyncEntry init ω S T)
    (hact : activationRow init ω S T) (hcontact : contactRow init ω S T) :
    reserveRow init ω S T := by
  constructor
  intro i hi v hiv hvcap
  have hclock : (virtualLabels init ω S i).role = .clock := hi
  have hfirst := hact.initialized_first i hi
  have h3 : 3 ≤ (virtualLabels init ω ((virtualTimes init ω S).initialized i) i).phase.val :=
    hfirst.1
  have hinitS : S ≤ (virtualTimes init ω S).initialized i := by
    by_contra hlt
    have hlt' : (virtualTimes init ω S).initialized i < S := Nat.lt_of_not_le hlt
    have hagree := virtualLabels_eq_labelsAt_through_asyncEntry init ω S T hentry
    have hST := hentry.order
    rw [hagree ((virtualTimes init ω S).initialized i) (by omega)] at h3
    have hlow := hentry.first_phase_seed.2 ((virtualTimes init ω S).initialized i) hlt' _
      (labelsAt_mem_trace init ω ((virtualTimes init ω S).initialized i) i)
    omega
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry
  have hτ3 : (virtualLabels init ω ((virtualTimes init ω S).initialized i) i).phase.val = 3 := by
    have h2 := ((henv _ hinitS).phase_range i).2
    omega
  have hledger := (virtual_counter_ledger init ω hentry i hclock _ hinitS hτ3 v hiv).2
  have hreset := hact.counter_reset i hi
  have hbudget := hcontact.eligible_budget i hi
  have hmono := eligibleContactsL_mono init ω S i (u := (virtualTimes init ω S).initialized i) hvcap
  exact reserve_arith hledger hmono hbudget hreset

/-- `hcore` from the six probabilistic row tails and the regime row. -/
theorem virtual_core_tail_of_row_tails {n : ℕ} (init : InputCfg n) (hn : 2 ≤ n)
    (hreg : ∀ ω S T, AsyncEntry init ω S T → regimeRow init ω S T) (h : RowTails init) :
    law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧
      ¬ PhaseThreeClockAssembly.VirtualGoodAt init s ω} ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 5) :=
  virtual_core_tail_of_rows init hn hreg
    (fun ω S T hentry hact hcontact => rowReserve_of_rows init ω hentry hact hcontact) h

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockReserve

end

import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockExit

/-!
# The tagged-Clock counter ledger after all-cap (N12, step 6, deterministic half of P15)

PHASE3 P15 (65): once every Clock is in Phase 3 at the cap and before the first Phase-4
seed, a tagged Clock's counter decreases by exactly one at each of its eligible contacts
(`StageEventSpec.eligibleContact`) and is unchanged by every other interaction. Hence
if no exit has occurred by `ζ + N`, the tagged Clock had at most `counter(ζ) ≤ 50 H`
eligible contacts in `(ζ, ζ + N]`.

* `AllCapAt init ω S t`: roles as at `S`, every Clock in Phase 3 at the cap, all phases
  at most 3.
* `counter_pair_left`, `counter_pair_right`: the one-interaction ledger for the tagged
  Clock as initiator or responder.
* `counter_step`, `counter_ledger`: the ledger along the actual trace.
* `eligibleContacts_le_of_no_exit`: the contact budget forced by a late exit.

The probabilistic half (conditional floor `2 (C - 1) / (n (n - 1))` on the eligible
contact indicator and the adapted Bernoulli hitting tail from the all-cap stopping time)
is not here.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCounterLedger

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockEmbedding

variable {L K : ℕ}

/-! ## One interaction of the tagged Clock -/

/-- The tagged Clock `s` as initiator: a capped Clock partner decrements its counter, a
non-Clock partner leaves it unchanged; in both cases no backup and no exit occur. -/
theorem counter_pair_left (s x : AgentState L K) (hs3 : s.phase.val = 3)
    (hsr : s.role = .clock) (hsm : s.minute.val = K * (L + 1)) (hx3 : x.phase.val ≤ 3)
    (hout : (Transition L K s x).1.phase.val < 4)
    (hout' : (Transition L K s x).2.phase.val < 4) :
    (x.role = .clock → x.phase.val = 3 → x.minute.val = K * (L + 1) →
      (Transition L K s x).1.counter.val + 1 = s.counter.val) ∧
    (x.role ≠ .clock → (Transition L K s x).1.counter.val = s.counter.val) := by
  constructor
  · intro hxr hx3' hxm
    have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s x hs3 hx3'
    have hc : CapCounterPair s x := by
      unfold CapCounterPair
      rw [hepi]
      exact ⟨hs3, hx3', hsr, hxr, Fin.ext (show s.minute.val = x.minute.val by omega), hsm⟩
    rw [transition_of_capCounterPair s x hc, hepi] at hout ⊢
    try simp only [] at hout ⊢
    simp only [finishPhase10Entry_phase_val] at hout
    by_cases h0 : s.counter.val = 0
    · exact absurd hout (by have := stdCounterSubroutine_phase_ge_four s hs3 h0; omega)
    · rw [stdCounterSubroutine_of_ne_zero s h0,
        finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by rw [saturatedCounterStep_phase]; omega)]
      simp only [saturatedCounterStep_counter]
      omega
  · intro hxr
    have hle := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s x
    have hnb : (phaseEpidemicUpdate L K s x).1.phase.val ≠ 10 ∧
        (phaseEpidemicUpdate L K s x).2.phase.val ≠ 10 := ⟨by omega, by omega⟩
    have hepi := phaseEpidemicUpdate_eq_of_no_backup s x (by omega) (by omega) hnb
    have hmax : max s.phase x.phase = s.phase :=
      max_eq_left (Fin.le_iff_val_le_val.mpr (by omega))
    rw [hmax, runInitsBetween_self] at hepi
    have h3 : (phaseEpidemicUpdate L K s x).1.phase.val = 3 := by
      rw [hepi]
      exact hs3
    rw [transition_eq_phase3_of_dispatch s x h3, hepi]
    simp only []
    rw [phase3Transition_clock_left _ _ hsr
      (runInitsBetween_role_ne_clock _ _ _ (by simpa using hxr)),
      finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by show s.phase.val ≠ 10; omega)]

/-- The tagged Clock `s` as responder. -/
theorem counter_pair_right (x s : AgentState L K) (hs3 : s.phase.val = 3)
    (hsr : s.role = .clock) (hsm : s.minute.val = K * (L + 1)) (hx3 : x.phase.val ≤ 3)
    (hout : (Transition L K x s).1.phase.val < 4)
    (hout' : (Transition L K x s).2.phase.val < 4) :
    (x.role = .clock → x.phase.val = 3 → x.minute.val = K * (L + 1) →
      (Transition L K x s).2.counter.val + 1 = s.counter.val) ∧
    (x.role ≠ .clock → (Transition L K x s).2.counter.val = s.counter.val) := by
  constructor
  · intro hxr hx3' hxm
    have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 x s hx3' hs3
    have hc : CapCounterPair x s := by
      unfold CapCounterPair
      rw [hepi]
      exact ⟨hx3', hs3, hxr, hsr, Fin.ext (show x.minute.val = s.minute.val by omega), hxm⟩
    rw [transition_of_capCounterPair x s hc, hepi] at hout' ⊢
    try simp only [] at hout' ⊢
    simp only [finishPhase10Entry_phase_val] at hout'
    by_cases h0 : s.counter.val = 0
    · exact absurd hout' (by have := stdCounterSubroutine_phase_ge_four s hs3 h0; omega)
    · rw [stdCounterSubroutine_of_ne_zero s h0,
        finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by rw [saturatedCounterStep_phase]; omega)]
      simp only [saturatedCounterStep_counter]
      omega
  · intro hxr
    have hle := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) x s
    have hnb : (phaseEpidemicUpdate L K x s).1.phase.val ≠ 10 ∧
        (phaseEpidemicUpdate L K x s).2.phase.val ≠ 10 := ⟨by omega, by omega⟩
    have hepi := phaseEpidemicUpdate_eq_of_no_backup x s (by omega) (by omega) hnb
    have hmax : max x.phase s.phase = s.phase :=
      max_eq_right (Fin.le_iff_val_le_val.mpr (by omega))
    rw [hmax, runInitsBetween_self] at hepi
    have hx' : (phaseEpidemicUpdate L K x s).1.phase.val = 3 := by
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
    rw [transition_eq_phase3_of_dispatch x s hx', hepi]
    simp only []
    rw [phase3Transition_clock_right _ _
      (runInitsBetween_role_ne_clock _ _ _ (by simpa using hxr)) hsr,
      finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by show s.phase.val ≠ 10; omega)]

/-! ## Along the actual trace -/

variable {n : ℕ} (init : InputCfg n) (ω : InputLog n)

/-- The all-cap regime at time `t` with the roles of time `S`. -/
def AllCapAt (S t : ℕ) : Prop :=
  (∀ k, (labelsAt init ω t k).role = (labelsAt init ω S k).role) ∧
  (∀ k, (labelsAt init ω t k).role = .clock →
    (labelsAt init ω t k).phase.val = 3 ∧ (labelsAt init ω t k).minute.val = clockTop n) ∧
  (∀ k, (labelsAt init ω t k).phase.val ≤ 3)

open Classical in
/-- One step of the ledger. -/
theorem counter_step (S t : ℕ) (i : Fin init.card) (hreg : AllCapAt init ω S t)
    (hi : fixedRole init ω S .clock i)
    (hlt4 : ∀ k, (labelsAt init ω (t + 1) k).phase.val < 4) :
    (labelsAt init ω (t + 1) i).counter.val +
        (if eligibleContact init ω S i (t + 1) then 1 else 0) =
      (labelsAt init ω t i).counter.val := by
  obtain ⟨hroles, hcap, hle3⟩ := hreg
  have hir : (labelsAt init ω t i).role = .clock := by rw [hroles]; exact hi
  obtain ⟨hi3, him⟩ := hcap i hir
  have hTrans : (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).δ =
      Transition (PhaseThreeModel.Numeric.hourIndex n) 256 := rfl
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      have hstep := labelsAt_succ_eq_auxStep init ω t
      rw [hd] at hstep
      simp only [auxStep] at hstep
      have hne : ¬ eligibleContact init ω S i (t + 1) := by
        rintro ⟨-, j, l, hjl, -⟩
        rw [hd] at hjl
        cases hjl
      rw [hstep, if_neg hne, add_zero]
  | some jl =>
      obtain ⟨j, l⟩ := jl
      obtain ⟨hjl, hj, hl, hother⟩ := labelsAt_selected_transition init ω t j l hd
      rw [hTrans] at hj hl
      have hj4 := hlt4 j
      have hl4 := hlt4 l
      rw [hj] at hj4
      rw [hl] at hl4
      by_cases hij : i = j
      · subst hij
        have hpair := counter_pair_left (labelsAt init ω t i) (labelsAt init ω t l) hi3 hir
          (by unfold clockTop at him; exact him) (hle3 l) hj4 hl4
        by_cases hlr : (labelsAt init ω t l).role = .clock
        · obtain ⟨hl3, hlm⟩ := hcap l hlr
          have helig : eligibleContact init ω S i (t + 1) :=
            ⟨by omega, i, l, hd, Or.inl rfl, hi, by unfold fixedRole; rw [← hroles]; exact hlr,
              by simpa using hi3, by simpa using hl3, by simpa using him, by simpa using hlm⟩
          rw [if_pos helig, hj]
          exact hpair.1 hlr hl3 (by unfold clockTop at hlm; exact hlm)
        · have hne : ¬ eligibleContact init ω S i (t + 1) := by
            rintro ⟨-, j', l', hjl', hmem, hj'r, hl'r, -⟩
            rw [hd] at hjl'
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hjl')
            apply hlr
            unfold fixedRole at hl'r
            rw [hroles]
            exact hl'r
          rw [if_neg hne, add_zero, hj]
          exact hpair.2 hlr
      by_cases hil : i = l
      · subst hil
        have hpair := counter_pair_right (labelsAt init ω t j) (labelsAt init ω t i) hi3 hir
          (by unfold clockTop at him; exact him) (hle3 j) hj4 hl4
        by_cases hjr : (labelsAt init ω t j).role = .clock
        · obtain ⟨hj3, hjm⟩ := hcap j hjr
          have helig : eligibleContact init ω S i (t + 1) :=
            ⟨by omega, j, i, hd, Or.inr rfl, by unfold fixedRole; rw [← hroles]; exact hjr, hi,
              by simpa using hj3, by simpa using hi3, by simpa using hjm, by simpa using him⟩
          rw [if_pos helig, hl]
          exact hpair.1 hjr hj3 (by unfold clockTop at hjm; exact hjm)
        · have hne : ¬ eligibleContact init ω S i (t + 1) := by
            rintro ⟨-, j', l', hjl', hmem, hj'r, hl'r, -⟩
            rw [hd] at hjl'
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hjl')
            apply hjr
            unfold fixedRole at hj'r
            rw [hroles]
            exact hj'r
          rw [if_neg hne, add_zero, hl]
          exact hpair.2 hjr
      · have hne : ¬ eligibleContact init ω S i (t + 1) := by
          rintro ⟨-, j', l', hjl', hmem, -⟩
          rw [hd] at hjl'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hjl')
          rcases hmem with h | h
          · exact hij h
          · exact hil h
        rw [if_neg hne, add_zero, hother i hij hil]

open Classical in
/-- The ledger from the all-cap time `ζ`: counter plus eligible contacts is conserved. -/
theorem counter_ledger (S ζ : ℕ) (i : Fin init.card) (hi : fixedRole init ω S .clock i)
    (v : ℕ) (hζv : ζ ≤ v)
    (hreg : ∀ t, ζ ≤ t → t ≤ v → AllCapAt init ω S t)
    (hlt4 : ∀ t, ζ < t → t ≤ v → ∀ k, (labelsAt init ω t k).phase.val < 4) :
    (labelsAt init ω v i).counter.val + eligibleContacts init ω S i ζ v =
      (labelsAt init ω ζ i).counter.val := by
  induction v, hζv using Nat.le_induction with
  | base =>
      unfold eligibleContacts
      rw [Finset.Ioc_self, Finset.filter_empty, Finset.card_empty, add_zero]
  | succ v hζv ih =>
      have ih' := ih (fun t h1 h2 => hreg t h1 (by omega)) (fun t h1 h2 => hlt4 t h1 (by omega))
      have hstep := counter_step init ω S v i (hreg v hζv (by omega)) hi
        (hlt4 (v + 1) (by omega) le_rfl)
      have hsum : eligibleContacts init ω S i ζ (v + 1) =
          eligibleContacts init ω S i ζ v +
            (if eligibleContact init ω S i (v + 1) then 1 else 0) := by
        unfold eligibleContacts
        rw [Finset.card_filter, Finset.card_filter, Finset.sum_Ioc_succ_top hζv]
      rw [hsum]
      omega

/-- If no agent has left Phase 3 by `ζ + N`, the tagged Clock had at most `50 H` eligible
contacts in `(ζ, ζ + N]`. -/
theorem eligibleContacts_le_of_no_exit (S ζ N : ℕ) (i : Fin init.card)
    (hi : fixedRole init ω S .clock i)
    (hreg : ∀ t, ζ ≤ t → t ≤ ζ + N → AllCapAt init ω S t)
    (hlt4 : ∀ t, ζ < t → t ≤ ζ + N → ∀ k, (labelsAt init ω t k).phase.val < 4) :
    eligibleContacts init ω S i ζ (ζ + N) ≤ 50 * (PhaseThreeModel.Numeric.hourIndex n + 1) := by
  have h := counter_ledger init ω S ζ i hi (ζ + N) (Nat.le_add_right ζ N) hreg hlt4
  have hb := (labelsAt init ω ζ i).counter.isLt
  omega

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCounterLedger

end

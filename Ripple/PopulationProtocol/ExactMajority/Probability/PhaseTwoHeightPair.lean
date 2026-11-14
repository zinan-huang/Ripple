import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoActivationLocal

/-!
# The actual mixed-phase clock-height pair bound

Inactive Clock fields receive effective minute zero. Successful Init-3 creates
no weight; only Clock-Clock Phase-3 interactions can increase weight. A backup
output is excluded here because the configuration potential is killed there.
-/

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

open PhaseTwoActivationLocal PhaseTwoProvenance

variable {L : ℕ}

def effectiveMinute (a : AgentState L 256) : ℕ :=
  if 3 ≤ a.phase.val then a.minute.val else 0

def clockWeight (a : AgentState L 256) : ℕ :=
  if a.role = .clock then 2 ^ effectiveMinute a else 0

theorem init_fields_weight_eq (before after : AgentState L 256)
    (hbefore : before.phase.val ≤ 3) (hafter : after.phase.val = 3)
    (h : InitFields before after) :
    clockWeight after = clockWeight before := by
  by_cases hc : before.role = .clock
  · simp only [clockWeight, h.1, if_pos hc]
    congr 1
    unfold effectiveMinute
    rw [if_pos (show 3 ≤ after.phase.val by omega), h.2.2 hc]
    by_cases hp : before.phase.val = 3
    · simp [hp]
    · have hsmall : ¬ 3 ≤ before.phase.val := by omega
      simp [hp, hsmall]
  · simp only [clockWeight, h.1, if_neg hc]

theorem pending_weight_eq (before after : AgentState L 256)
    (hbefore : before.phase.val ≤ 2) (hafter : after.phase.val ≤ 3)
    (hrole : after.role = before.role)
    (hfresh : after.phase.val = 3 → Phase3Pre3.Phase3EntryAgent after) :
    clockWeight after = clockWeight before := by
  have hsmall : ¬ 3 ≤ before.phase.val := by omega
  by_cases hc : before.role = .clock
  · have hca : after.role = .clock := hrole.trans hc
    have heffective : effectiveMinute after = 0 := by
      by_cases ha : 3 ≤ after.phase.val
      · simp only [effectiveMinute, if_pos ha]
        exact Phase3Pre3.clock_minute_zero_of_Phase3EntryAgent
          (hfresh (by omega)) hca
      · simp only [effectiveMinute, if_neg ha]
    simp only [clockWeight, if_pos hc, if_pos hca, heffective]
    simp [effectiveMinute, hsmall]
  · have hca : after.role ≠ .clock := by rwa [hrole]
    simp only [clockWeight, if_neg hc, if_neg hca]

theorem phase_three_weight_pair_le (s t : AgentState L 256)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hsl : ClockBelow s) (htl : ClockBelow t) :
    clockWeight (Phase3Transition L 256 s t).1 +
        clockWeight (Phase3Transition L 256 s t).2 ≤
      clockWeight s + clockWeight t +
        (if s.role = .clock ∧ t.role = .clock then clockWeight s + clockWeight t else 0) := by
  have hstatic := phase_three_static s t
    (fun hc => clockBelow_cap s hsl hc) (fun hc => clockBelow_cap t htl hc)
  by_cases hcc : s.role = .clock ∧ t.role = .clock
  · have hcap := clockBelow_cap s hsl hcc.1
    by_cases hdiff : s.minute ≠ t.minute
    · have heq : Phase3Transition L 256 s t =
          ({s with minute := max s.minute t.minute},
           {t with minute := max s.minute t.minute}) := by
        simp [Phase3Transition, hcc.1, hcc.2, hdiff]
      rw [heq]
      rcases le_total s.minute t.minute with hle | hle
      · simp [clockWeight, effectiveMinute, hcc.1, hcc.2, hs, ht,
          max_eq_right hle]
        <;> (have h1 := Nat.one_le_two_pow (n := s.minute.val)
             have h2 := Nat.one_le_two_pow (n := t.minute.val)
             omega)
      · simp [clockWeight, effectiveMinute, hcc.1, hcc.2, hs, ht,
          max_eq_left hle]
        <;> (have h1 := Nat.one_le_two_pow (n := s.minute.val)
             have h2 := Nat.one_le_two_pow (n := t.minute.val)
             omega)
    · have hsame : s.minute = t.minute := not_not.mp hdiff
      have heq : Phase3Transition L 256 s t =
          ({s with minute := ⟨s.minute.val + 1, by omega⟩}, t) := by
        simp [Phase3Transition, hcc.1, hcc.2, hdiff, hcap]
      rw [heq]
      simp [clockWeight, effectiveMinute, hcc.1, hcc.2, hs, ht, hsame, pow_succ]
      <;> omega
  · by_cases hsc : s.role = .clock
    · have htc : t.role ≠ .clock := fun h => hcc ⟨hsc, h⟩
      have hleft : (Phase3Transition L 256 s t).1 = s := by
        by_cases htm : t.role = .main <;> by_cases htb : t.bias = .zero <;>
          simp [Phase3Transition, hsc, htc, htm, htb]
      have hright : (Phase3Transition L 256 s t).2.role ≠ .clock := by
        rwa [hstatic.2.1]
      rw [hleft]
      simp [clockWeight, htc, hright, hcc]
    · by_cases htc : t.role = .clock
      · have hright : (Phase3Transition L 256 s t).2 = t := by
          by_cases hsm : s.role = .main <;> by_cases hsb : s.bias = .zero <;>
            simp [Phase3Transition, hsc, htc, hsm, hsb]
        have hleft : (Phase3Transition L 256 s t).1.role ≠ .clock := by
          rwa [hstatic.1.1]
        rw [hright]
        simp [clockWeight, hsc, hleft, hcc]
      · have hleft : (Phase3Transition L 256 s t).1.role ≠ .clock := by
          rwa [hstatic.1.1]
        have hright : (Phase3Transition L 256 s t).2.role ≠ .clock := by
          rwa [hstatic.2.1]
        simp [clockWeight, hsc, htc, hleft, hright, hcc]

/-- The full implemented transition, including pending initializers, obeys
the selected-clock weight ledger whenever it does not enter backup. -/
theorem transition_weight_pair_le (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hsl : s.phase.val = 3 → ClockBelow s)
    (htl : t.phase.val = 3 → ClockBelow t)
    (hlno : (Transition L 256 s t).1.phase.val ≠ 10)
    (hrno : (Transition L 256 s t).2.phase.val ≠ 10) :
    clockWeight (Transition L 256 s t).1 +
        clockWeight (Transition L 256 s t).2 ≤
      clockWeight s + clockWeight t +
        (if s.role = .clock ∧ t.role = .clock then clockWeight s + clockWeight t else 0) := by
  by_cases hmax : max s.phase.val t.phase.val ≤ 2
  · have hslo : s.phase.val ≤ 2 := (le_max_left _ _).trans hmax
    have htlo : t.phase.val ≤ 2 := (le_max_right _ _).trans hmax
    have hroles := mixed_range_roles s t hs ht hsl htl hlno hrno
    have hfreshLeft : (Transition L 256 s t).1.phase.val = 3 →
        Phase3Pre3.Phase3EntryAgent (Transition L 256 s t).1 := by
      intro hp
      exact (first_phase_three_pair s t hslo htlo hlno hrno
        (Or.inl (by omega))).1.1
    have hfreshRight : (Transition L 256 s t).2.phase.val = 3 →
        Phase3Pre3.Phase3EntryAgent (Transition L 256 s t).2 := by
      intro hp
      exact (first_phase_three_pair s t hslo htlo hlno hrno
        (Or.inr (by omega))).2.1
    have hwLeft := pending_weight_eq s _ hslo hroles.2.2.1 hroles.1 hfreshLeft
    have hwRight := pending_weight_eq t _ htlo hroles.2.2.2 hroles.2.1 hfreshRight
    rw [hwLeft, hwRight]
    exact Nat.le_add_right _ _
  · have hmaxeq : max s.phase.val t.phase.val = 3 := by omega
    have hdata := epidemic_three_fields s t hs ht hmaxeq
    have hphase := epidemic_three_phases_of_success s t hs ht hmaxeq hlno hrno
    have hla := init_fields_clockBelow s _ hdata.1 hsl
    have hlb := init_fields_clockBelow t _ hdata.2 htl
    have hweightLeft := init_fields_weight_eq s _ hs.2 hphase.1 hdata.1
    have hweightRight := init_fields_weight_eq t _ ht.2 hphase.2 hdata.2
    have heq := transition_eq_phase_three s t hphase.1 hphase.2 hla hlb
    have hp := phase_three_weight_pair_le
      (phaseEpidemicUpdate L 256 s t).1 (phaseEpidemicUpdate L 256 s t).2
      hphase.1 hphase.2 hla hlb
    rw [heq]
    simpa only [hweightLeft, hweightRight, hdata.1.1, hdata.2.1] using hp

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

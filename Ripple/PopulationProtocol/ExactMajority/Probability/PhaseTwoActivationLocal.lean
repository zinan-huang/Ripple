import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoSeedProfile
import Ripple.PopulationProtocol.ExactMajority.Probability.PositionalCluster

/-!
# Deterministic activation fields

Only Phase-3 agents contribute an activation payload. A pending agent receives
fresh fields from Init-3. The joint Main hour/index ceiling is propagated
directly by the cancel/split guard and clock dragging; no comparison of a
biased Main's index with its own hour is assumed.
-/

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoActivationLocal

open TimeTheorem PhaseTwoProvenance

variable {L : ℕ}

def Payload (top : ℕ) (a : AgentState L 256) : Prop :=
  (a.role = .main → a.hour.val ≤ top) ∧
  (a.role = .main → ∀ sigma i, a.bias = Bias.dyadic sigma i → i.val ≤ top) ∧
  (a.role ≠ .main → a.bias = Bias.zero) ∧
  (a.role = .clock → a.counter.val = 50 * (L + 1))

def ClockBelow (a : AgentState L 256) : Prop :=
  a.role = .clock → a.minute.val < 16 * (L + 1)

def SameStatic (before after : AgentState L 256) : Prop :=
  after.role = before.role ∧ after.phase = before.phase ∧
    after.counter = before.counter

def enterThree (a : AgentState L 256) : AgentState L 256 :=
  runInitsBetween L 256 a.phase.val 3 {a with phase := ⟨3, by decide⟩}

def InitData (top : ℕ) (before after : AgentState L 256) : Prop :=
  after.role = before.role ∧
  (after.phase.val = 3 ∨ after.phase.val = 10) ∧
  Payload top after ∧
  (before.role = .clock →
    after.minute.val = if before.phase.val = 3 then before.minute.val else 0)

theorem clockBelow_cap (a : AgentState L 256) (h : ClockBelow a)
    (hc : a.role = .clock) : a.minute.val < 256 * (L + 1) := by
  have hh := h hc
  omega

theorem clockBelow_stamp (a : AgentState L 256) (h : ClockBelow a)
    (hc : a.role = .clock) : min L (a.minute.val / 256) ≤ L / 16 := by
  have hh := h hc
  have hd : a.minute.val / 256 ≤ L / 16 := by omega
  exact (Nat.min_le_right _ _).trans hd

theorem payload_hour_update (top : ℕ) (a : AgentState L 256)
    (h : Fin (L + 1)) (hp : Payload top a) (hh : h.val ≤ top) :
    Payload top {a with hour := h} :=
  ⟨fun _ => hh, hp.2.1, hp.2.2.1, hp.2.2.2⟩

theorem payload_of_main (top : ℕ) (a : AgentState L 256)
    (hm : a.role = .main) (hh : a.hour.val ≤ top)
    (hi : ∀ sigma i, a.bias = Bias.dyadic sigma i → i.val ≤ top) :
    Payload top a := by
  refine ⟨fun _ => hh, fun _ => hi, fun hn => (hn hm).elim, ?_⟩
  intro hc
  rw [hm] at hc
  cases hc

theorem init_three_phase (a : AgentState L 256) :
    (phaseInit L 256 ⟨3, by decide⟩ a).phase = a.phase := by
  rcases a with ⟨input, output, phase, role, assigned, bias, smallBias,
    hour, minute, full, opinions, counter⟩
  cases role <;> simp [phaseInit]

theorem init_three_clock_minute (a : AgentState L 256) (hc : a.role = .clock) :
    (phaseInit L 256 ⟨3, by decide⟩ a).minute.val = 0 := by
  simp [phaseInit, hc]

theorem payload_init_three (top : ℕ) (a : AgentState L 256) :
    Payload top (phaseInit L 256 ⟨3, by decide⟩ a) := by
  rcases a with ⟨input, output, phase, role, assigned, bias, smallBias,
    hour, minute, full, opinions, counter⟩
  cases role <;> fin_cases smallBias <;> simp [Payload, phaseInit]

theorem enter_three_data (top : ℕ) (a : AgentState L 256)
    (ha : 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hp : a.phase.val = 3 → Payload top a) :
    InitData top a (enterThree a) := by
  have hcases : a.phase.val = 1 ∨ a.phase.val = 2 ∨ a.phase.val = 3 := by omega
  rcases hcases with hone | htwo | hthree
  · have hlist : (List.range 11).filter
        (fun k => decide (1 < k) && decide (k ≤ 3)) = [2, 3] := by decide
    have heq : enterThree a =
        phaseInit L 256 ⟨3, by decide⟩
          (phaseInit L 256 ⟨2, by decide⟩ {a with phase := ⟨3, by decide⟩}) := by
      simp [enterThree, hone, runInitsBetween, hlist]
    have hphase :
        (phaseInit L 256 ⟨2, by decide⟩
          {a with phase := ⟨3, by decide⟩}).phase.val = 3 ∨
        (phaseInit L 256 ⟨2, by decide⟩
          {a with phase := ⟨3, by decide⟩}).phase.val = 10 := by
      simp [phaseInit] <;> split_ifs <;> simp [enterPhase10, phase10]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [heq]
      simp [phaseInit_role]
    · rw [heq, init_three_phase]
      exact hphase
    · rw [heq]
      exact payload_init_three top _
    · intro hc
      have hc' :
          (phaseInit L 256 ⟨2, by decide⟩
            {a with phase := ⟨3, by decide⟩}).role = .clock := by
        simpa [phaseInit_role] using hc
      rw [heq, init_three_clock_minute _ hc']
      simp [hone]
  · have hlist : (List.range 11).filter
        (fun k => decide (2 < k) && decide (k ≤ 3)) = [3] := by decide
    have heq : enterThree a =
        phaseInit L 256 ⟨3, by decide⟩ {a with phase := ⟨3, by decide⟩} := by
      simp [enterThree, htwo, runInitsBetween, hlist]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [heq]
      simp [phaseInit_role]
    · rw [heq, init_three_phase]
      exact Or.inl rfl
    · rw [heq]
      exact payload_init_three top _
    · intro hc
      rw [heq, init_three_clock_minute {a with phase := ⟨3, by decide⟩} hc]
      simp [htwo]
  · have hpa : a.phase = ⟨3, by decide⟩ := Fin.ext hthree
    have heq : enterThree a = a := by
      unfold enterThree
      rw [hthree, runInitsBetween_self]
      cases a
      simp_all
    rw [heq]
    exact ⟨rfl, Or.inl hthree, hp hthree, fun _ => by simp [hthree]⟩

theorem init_data_backup (top : ℕ) (before after : AgentState L 256)
    (hb : before.phase.val < 10) (h : InitData top before after) :
    InitData top before (phase10EpidemicEntry L 256 before after) := by
  refine ⟨?_, Or.inr ?_, ?_, ?_⟩
  · simpa only [phase10EpidemicEntry_role] using h.1
  · exact phase10EpidemicEntry_phase_val_of_before_lt_10 (L := L) (K := 256) before after hb
  · simpa only [Payload, phase10EpidemicEntry_role, phase10EpidemicEntry_hour,
      phase10EpidemicEntry_bias, phase10EpidemicEntry_counter] using h.2.2.1
  · intro hc
    simpa only [phase10EpidemicEntry_minute] using h.2.2.2 hc

/-- A Clock's effective minute is preserved by the epidemic initialization:
pending Clocks enter at minute zero, while active Clocks retain their minute. -/
theorem epidemic_three_data (top : ℕ) (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hmax : max s.phase.val t.phase.val = 3)
    (hsp : s.phase.val = 3 → Payload top s)
    (htp : t.phase.val = 3 → Payload top t) :
    InitData top s (phaseEpidemicUpdate L 256 s t).1 ∧
      InitData top t (phaseEpidemicUpdate L 256 s t).2 := by
  have hmaxFin : max s.phase t.phase = ⟨3, by decide⟩ := Fin.ext hmax
  let a := enterThree s
  let b := enterThree t
  have ha : InitData top s a := enter_three_data top s hs hsp
  have hb : InitData top t b := enter_three_data top t ht htp
  have hepi : phaseEpidemicUpdate L 256 s t =
      if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (a.phase.val = 10 ∨ b.phase.val = 10) then
        (phase10EpidemicEntry L 256 s a, phase10EpidemicEntry L 256 t b)
      else (a, b) := by
    unfold phaseEpidemicUpdate
    rw [hmaxFin]
    rfl
  rw [hepi]
  split_ifs
  · exact ⟨init_data_backup top s a (by omega) ha,
      init_data_backup top t b (by omega) hb⟩
  · exact ⟨ha, hb⟩

theorem init_data_clockBelow (top : ℕ) (before after : AgentState L 256)
    (h : InitData top before after)
    (hlow : before.phase.val = 3 → ClockBelow before) :
    ClockBelow after := by
  intro hc
  have hbefore : before.role = .clock := h.1.symm.trans hc
  rw [h.2.2.2 hbefore]
  by_cases hp : before.phase.val = 3
  · simpa only [if_pos hp] using hlow hp hbefore
  · simp only [if_neg hp]
    omega

theorem cancel_split_static (s t : AgentState L 256) :
    SameStatic s (phase3CancelSplit L 256 s t).1 ∧
      SameStatic t (phase3CancelSplit L 256 s t).2 := by
  unfold phase3CancelSplit
  match s.bias, t.bias with
  | .zero, .zero => simp [SameStatic]
  | .zero, .dyadic _ _ => simp only; split_ifs <;> simp [SameStatic]
  | .dyadic _ _, .zero => simp only; split_ifs <;> simp [SameStatic]
  | .dyadic .pos _, .dyadic .pos _ => simp [SameStatic]
  | .dyadic .pos _, .dyadic .neg _ => simp only; split_ifs <;> simp [SameStatic]
  | .dyadic .neg _, .dyadic .pos _ => simp only; split_ifs <;> simp [SameStatic]
  | .dyadic .neg _, .dyadic .neg _ => simp [SameStatic]

/-- Below the Clock cap, the local Phase-3 rule preserves corresponding roles,
phases and counters. This theorem does not assume any Main payload. -/
theorem phase_three_static (s t : AgentState L 256)
    (hs : s.role = .clock → s.minute.val < 256 * (L + 1))
    (ht : t.role = .clock → t.minute.val < 256 * (L + 1)) :
    SameStatic s (Phase3Transition L 256 s t).1 ∧
      SameStatic t (Phase3Transition L 256 s t).2 := by
  by_cases hcc : s.role = .clock ∧ t.role = .clock
  · have hcap := hs hcc.1
    by_cases hdiff : s.minute ≠ t.minute <;>
      simp [Phase3Transition, SameStatic, hcc.1, hcc.2, hdiff, hcap]
  · by_cases hl : s.role = .main ∧ s.bias = .zero ∧ t.role = .clock
    · simp [Phase3Transition, SameStatic, hcc, hl, hl.1, hl.2.2]
    · by_cases hr : t.role = .main ∧ t.bias = .zero ∧ s.role = .clock
      · simp [Phase3Transition, SameStatic, hcc, hl, hr, hr.1, hr.2.2]
      · simp only [Phase3Transition, if_neg hcc, if_neg hl, if_neg hr]
        by_cases hmm : s.role = .main ∧ t.role = .main
        · rw [if_pos hmm]
          exact cancel_split_static s t
        · rw [if_neg hmm]
          exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem phase_three_payload (s t : AgentState L 256)
    (hsp : Payload (L / 16) s) (htp : Payload (L / 16) t)
    (hsl : ClockBelow s) (htl : ClockBelow t) :
    Payload (L / 16) (Phase3Transition L 256 s t).1 ∧
      Payload (L / 16) (Phase3Transition L 256 s t).2 := by
  by_cases hcc : s.role = .clock ∧ t.role = .clock
  · have hcap := clockBelow_cap s hsl hcc.1
    by_cases hdiff : s.minute ≠ t.minute <;>
      simpa [Phase3Transition, Payload, hcc.1, hcc.2, hdiff, hcap]
        using And.intro hsp htp
  · by_cases hl : s.role = .main ∧ s.bias = .zero ∧ t.role = .clock
    · let q : Fin (L + 1) :=
        ⟨max s.hour.val (min L (t.minute.val / 256)),
          (Nat.max_lt).mpr ⟨s.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩
      have heq : Phase3Transition L 256 s t = ({s with hour := q}, t) := by
        simp [Phase3Transition, hcc, hl, hl.1, hl.2.2, q]
      have hq : q.val ≤ L / 16 :=
        max_le (hsp.1 hl.1) (clockBelow_stamp t htl hl.2.2)
      rw [heq]
      exact ⟨payload_hour_update _ s q hsp hq, htp⟩
    · by_cases hr : t.role = .main ∧ t.bias = .zero ∧ s.role = .clock
      · let q : Fin (L + 1) :=
          ⟨max t.hour.val (min L (s.minute.val / 256)),
            (Nat.max_lt).mpr ⟨t.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩
        have heq : Phase3Transition L 256 s t = (s, {t with hour := q}) := by
          simp [Phase3Transition, hcc, hl, hr, hr.1, hr.2.2, q]
        have hq : q.val ≤ L / 16 :=
          max_le (htp.1 hr.1) (clockBelow_stamp s hsl hr.2.2)
        rw [heq]
        exact ⟨hsp, payload_hour_update _ t q htp hq⟩
      · by_cases hmm : s.role = .main ∧ t.role = .main
        · have heq : Phase3Transition L 256 s t = phase3CancelSplit L 256 s t := by
            simp only [Phase3Transition, if_neg hcc, if_neg hl, if_neg hr, if_pos hmm]
          have hhour := PositionalCluster.mainHour_le_of_clockBelow_cancelSplit s t
            (hsp.1 hmm.1) (htp.1 hmm.2) (hsp.2.1 hmm.1) (htp.2.1 hmm.2)
          have hindex := DoublingEdges.phase3CancelSplit_preserves_top_edge s t
            (hsp.2.1 hmm.1) (htp.2.1 hmm.2) (hsp.1 hmm.1) (htp.1 hmm.2)
          have hstatic := cancel_split_static s t
          rw [heq]
          exact ⟨payload_of_main _ _ (hstatic.1.1.trans hmm.1) hhour.1 hindex.1,
            payload_of_main _ _ (hstatic.2.1.trans hmm.2) hhour.2 hindex.2⟩
        · have heq : Phase3Transition L 256 s t = (s, t) := by
            simp only [Phase3Transition, if_neg hcc, if_neg hl, if_neg hr, if_neg hmm]
          rw [heq]
          exact ⟨hsp, htp⟩

/-- The epidemic fields needed for the height potential do not require a Main
payload or a counter reserve. -/
def InitFields (before after : AgentState L 256) : Prop :=
  after.role = before.role ∧
  (after.phase.val = 3 ∨ after.phase.val = 10) ∧
  (before.role = .clock →
    after.minute.val = if before.phase.val = 3 then before.minute.val else 0)

theorem enter_three_fields (a : AgentState L 256)
    (ha : 1 ≤ a.phase.val ∧ a.phase.val ≤ 3) :
    InitFields a (enterThree a) := by
  by_cases hp : a.phase.val = 3
  · have hpa : a.phase = ⟨3, by decide⟩ := Fin.ext hp
    have heq : enterThree a = a := by
      unfold enterThree
      rw [hp, runInitsBetween_self]
      cases a
      simp_all
    rw [heq]
    exact ⟨rfl, Or.inl hp, fun _ => by simp [hp]⟩
  · have h := enter_three_data 0 a ha (fun hthree => (hp hthree).elim)
    exact ⟨h.1, h.2.1, h.2.2.2⟩

theorem init_fields_backup (before after : AgentState L 256)
    (hb : before.phase.val < 10) (h : InitFields before after) :
    InitFields before (phase10EpidemicEntry L 256 before after) := by
  refine ⟨?_, Or.inr ?_, ?_⟩
  · simpa only [phase10EpidemicEntry_role] using h.1
  · exact phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := 256) before after hb
  · intro hc
    simpa only [phase10EpidemicEntry_minute] using h.2.2 hc

theorem epidemic_three_fields (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hmax : max s.phase.val t.phase.val = 3) :
    InitFields s (phaseEpidemicUpdate L 256 s t).1 ∧
      InitFields t (phaseEpidemicUpdate L 256 s t).2 := by
  have hmaxFin : max s.phase t.phase = ⟨3, by decide⟩ := Fin.ext hmax
  let a := enterThree s
  let b := enterThree t
  have ha : InitFields s a := enter_three_fields s hs
  have hb : InitFields t b := enter_three_fields t ht
  have hepi : phaseEpidemicUpdate L 256 s t =
      if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (a.phase.val = 10 ∨ b.phase.val = 10) then
        (phase10EpidemicEntry L 256 s a, phase10EpidemicEntry L 256 t b)
      else (a, b) := by
    unfold phaseEpidemicUpdate
    rw [hmaxFin]
    rfl
  rw [hepi]
  split_ifs
  · exact ⟨init_fields_backup s a (by omega) ha,
      init_fields_backup t b (by omega) hb⟩
  · exact ⟨ha, hb⟩

theorem init_fields_clockBelow (before after : AgentState L 256)
    (h : InitFields before after)
    (hlow : before.phase.val = 3 → ClockBelow before) :
    ClockBelow after := by
  intro hc
  have hbefore : before.role = .clock := h.1.symm.trans hc
  rw [h.2.2 hbefore]
  by_cases hp : before.phase.val = 3
  · simpa only [if_pos hp] using hlow hp hbefore
  · simp only [if_neg hp]
    omega

theorem epidemic_three_phases_of_success (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hmax : max s.phase.val t.phase.val = 3)
    (hlno : (Transition L 256 s t).1.phase.val ≠ 10)
    (hrno : (Transition L 256 s t).2.phase.val ≠ 10) :
    (phaseEpidemicUpdate L 256 s t).1.phase.val = 3 ∧
      (phaseEpidemicUpdate L 256 s t).2.phase.val = 3 := by
  have hdata := epidemic_three_fields s t hs ht hmax
  have hmono := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := 256) s t
  constructor
  · rcases hdata.1.2.1 with hthree | hten
    · exact hthree
    · have hout := (Transition L 256 s t).1.phase.isLt
      omega
  · rcases hdata.2.2.1 with hthree | hten
    · exact hthree
    · have hout := (Transition L 256 s t).2.phase.isLt
      omega

theorem transition_eq_phase_three (s t : AgentState L 256)
    (hel : (phaseEpidemicUpdate L 256 s t).1.phase.val = 3)
    (her : (phaseEpidemicUpdate L 256 s t).2.phase.val = 3)
    (hsl : ClockBelow (phaseEpidemicUpdate L 256 s t).1)
    (htl : ClockBelow (phaseEpidemicUpdate L 256 s t).2) :
    Transition L 256 s t =
      Phase3Transition L 256 (phaseEpidemicUpdate L 256 s t).1
        (phaseEpidemicUpdate L 256 s t).2 := by
  rcases he : phaseEpidemicUpdate L 256 s t with ⟨a, b⟩
  have ha : a.phase.val = 3 := by simpa only [he] using hel
  have hb : b.phase.val = 3 := by simpa only [he] using her
  have hla : ClockBelow a := by simpa only [he] using hsl
  have hlb : ClockBelow b := by simpa only [he] using htl
  have hstatic := phase_three_static a b
    (fun hc => clockBelow_cap a hla hc) (fun hc => clockBelow_cap b hlb hc)
  have hlout : (Phase3Transition L 256 a b).1.phase.val ≠ 10 := by
    rw [hstatic.1.2.1, ha]
    decide
  have hrout : (Phase3Transition L 256 a b).2.phase.val ≠ 10 := by
    rw [hstatic.2.2.1, hb]
    decide
  have hpa : a.phase = ⟨3, by decide⟩ := Fin.ext ha
  have hactual : Transition L 256 s t =
      (finishPhase10Entry L 256 a (Phase3Transition L 256 a b).1,
       finishPhase10Entry L 256 b (Phase3Transition L 256 a b).2) := by
    unfold Transition
    rw [he]
    simp only [hpa]
  rw [hactual]
  simp only [he, finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := 256) a _ hlout,
    finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := 256) b _ hrout]

/-- Domain closure below the active Clock height barrier. No Main bound,
non-Main bias assumption, or counter reserve is needed for this conclusion. -/
theorem mixed_range_roles (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hsl : s.phase.val = 3 → ClockBelow s)
    (htl : t.phase.val = 3 → ClockBelow t)
    (hlno : (Transition L 256 s t).1.phase.val ≠ 10)
    (hrno : (Transition L 256 s t).2.phase.val ≠ 10) :
    (Transition L 256 s t).1.role = s.role ∧
      (Transition L 256 s t).2.role = t.role ∧
      (Transition L 256 s t).1.phase.val ≤ 3 ∧
      (Transition L 256 s t).2.phase.val ≤ 3 := by
  by_cases hmax : max s.phase.val t.phase.val ≤ 2
  · have hslo : s.phase.val ≤ 2 := (le_max_left _ _).trans hmax
    have htlo : t.phase.val ≤ 2 := (le_max_right _ _).trans hmax
    have hcap : (Transition L 256 s t).1.phase.val ≤ 3 ∧
        (Transition L 256 s t).2.phase.val ≤ 3 := by
      by_cases hnew : 3 ≤ (Transition L 256 s t).1.phase.val ∨
          3 ≤ (Transition L 256 s t).2.phase.val
      · have hfresh := first_phase_three_pair s t hslo htlo hlno hrno hnew
        exact ⟨le_of_eq hfresh.1.1.1, le_of_eq hfresh.2.1.1⟩
      · omega
    have hroles := PhaseTwoSeedProfile.mixed_transition_roles s t
      ⟨hs.1, hslo⟩ ⟨ht.1, htlo⟩ hcap.1 hcap.2
    exact ⟨hroles.1, hroles.2, hcap⟩
  · have hmaxeq : max s.phase.val t.phase.val = 3 := by omega
    have hdata := epidemic_three_fields s t hs ht hmaxeq
    have hphase := epidemic_three_phases_of_success s t hs ht hmaxeq hlno hrno
    have hla := init_fields_clockBelow s _ hdata.1 hsl
    have hlb := init_fields_clockBelow t _ hdata.2 htl
    have heq := transition_eq_phase_three s t hphase.1 hphase.2 hla hlb
    have hstatic := phase_three_static
      (phaseEpidemicUpdate L 256 s t).1 (phaseEpidemicUpdate L 256 s t).2
      (fun hc => clockBelow_cap _ hla hc) (fun hc => clockBelow_cap _ hlb hc)
    rw [heq]
    refine ⟨hstatic.1.1.trans hdata.1.1, hstatic.2.1.trans hdata.2.1, ?_, ?_⟩
    · rw [hstatic.1.2.1]
      exact le_of_eq hphase.1
    · rw [hstatic.2.2.1]
      exact le_of_eq hphase.2

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoActivationLocal

import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEmbeddingBridge
import Ripple.PopulationProtocol.ExactMajority.Probability.HourCoupling

/-!
# The P11 exposure-and-cancellation ledger at the pair level (N12, Main row)

PHASE3 P11 (51) bounds the Main outlier counts of threshold `h` by two credits: `D`, the
number of Main/Clock contacts with the Clock at minute at least `(h + 1) K`, and `J`,
the number of opposite-sign equal-index Main cancellations at an index above `h`:

* `V = 2 Z + B ≤ 2 D + 2 J`, with `Z` the active zero Mains of stored hour `> h` and
  `B` the active biased Mains of index `> h`;
* `H ≤ D + 2 J`, with `H` the active Mains of stored hour `> h`.

Both are sums over the agents of per-agent indicators, and every step of the virtual
process changes only the two drawn agents. This file proves the per-step inequality on
one ordered pair for the implemented Phase-3 rule (`Phase3Transition`: Clock epidemic,
hour drag, cancel, split) and for the virtual rule on two Phase-3 agents
(`virtualRule_ledger`): the pairwise outlier credits after the step are at most the
credits before the step plus `2 ⋅ contact + 2 ⋅ deepCancel` (for `V`) and
`contact + 2 ⋅ deepCancel` (for `H`), where `contact` is the indicator that the pair is a
Main and a Phase-3 Clock at minute `≥ (h + 1) K`, and `deepCancel` the indicator of a
deep cancellation. The implemented rule agrees with the ledger of P11: a drag raises
`V` by at most two and `H` by at most one; a deep cancellation turns two deep biased
agents into two high-hour zeros (`V` up by two, `H` up by at most two); a split across
or above `h` does not increase `V` or `H`; every other branch is inert.

The ceiling of item 38 (no Main field above `h` before the first Clock at minute
`(h + 1) K`) is the special case of the ledger with zero credits
(`virtualRule_ceiling`).
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainLedger

open PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge

variable {L K : ℕ}

/-! ## Per-agent outlier indicators at threshold `h` -/

/-- An active Main with stored hour above `h`. -/
def highHourInd (h : ℕ) (a : AgentState L K) : ℕ :=
  if 3 ≤ a.phase.val ∧ a.role = .main ∧ h < a.hour.val then 1 else 0

/-- An active zero Main with stored hour above `h`. -/
def highZeroInd (h : ℕ) (a : AgentState L K) : ℕ :=
  if 3 ≤ a.phase.val ∧ a.role = .main ∧ a.bias = .zero ∧ h < a.hour.val then 1 else 0

/-- The deep-index indicator of a bias. -/
def deepIdx (h : ℕ) : Bias L → ℕ
  | .zero => 0
  | .dyadic _ j => if h < j.val then 1 else 0

/-- An active biased Main with index above `h`. -/
def deepInd (h : ℕ) (a : AgentState L K) : ℕ :=
  if 3 ≤ a.phase.val ∧ a.role = .main then deepIdx h a.bias else 0

/-- The per-agent contribution to `V = 2 Z + B`. -/
def creditV (h : ℕ) (a : AgentState L K) : ℕ := 2 * highZeroInd h a + deepInd h a

/-! ## Per-pair credits -/

/-- A Main meets a Phase-3 Clock at minute at least `(h + 1) K` (either order; the Main
may be inactive, so activation contacts are counted). -/
def contactInd (h : ℕ) (s t : AgentState L K) : ℕ :=
  if (s.role = .main ∧ t.role = .clock ∧ 3 ≤ t.phase.val ∧ (h + 1) * K ≤ t.minute.val) ∨
      (t.role = .main ∧ s.role = .clock ∧ 3 ≤ s.phase.val ∧ (h + 1) * K ≤ s.minute.val)
  then 1 else 0

/-- Opposite signs at a common index above `h`. -/
def cancelIdx (h : ℕ) : Bias L → Bias L → ℕ
  | .dyadic .pos i, .dyadic .neg j => if i.val = j.val ∧ h < i.val then 1 else 0
  | .dyadic .neg i, .dyadic .pos j => if i.val = j.val ∧ h < i.val then 1 else 0
  | _, _ => 0

/-- A deep cancellation: two active Mains with opposite signs at a common index above
`h`. -/
def deepCancelInd (h : ℕ) (s t : AgentState L K) : ℕ :=
  if 3 ≤ s.phase.val ∧ 3 ≤ t.phase.val ∧ s.role = .main ∧ t.role = .main
  then cancelIdx h s.bias t.bias else 0

theorem highHourInd_le_one (h : ℕ) (a : AgentState L K) : highHourInd h a ≤ 1 := by
  unfold highHourInd; split_ifs <;> omega

theorem highZeroInd_le_one (h : ℕ) (a : AgentState L K) : highZeroInd h a ≤ 1 := by
  unfold highZeroInd; split_ifs <;> omega

theorem deepIdx_le_one (h : ℕ) (b : Bias L) : deepIdx h b ≤ 1 := by
  cases b with
  | zero => simp [deepIdx]
  | dyadic σ j => simp only [deepIdx]; split_ifs <;> omega

theorem deepInd_le_one (h : ℕ) (a : AgentState L K) : deepInd h a ≤ 1 := by
  unfold deepInd; split_ifs
  · exact deepIdx_le_one h a.bias
  · omega

theorem highZeroInd_le_highHourInd (h : ℕ) (a : AgentState L K) :
    highZeroInd h a ≤ highHourInd h a := by
  unfold highZeroInd highHourInd
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1, h1.2.2.2⟩ h2
  · omega
  · exact le_rfl

theorem contactInd_le_one (h : ℕ) (s t : AgentState L K) : contactInd h s t ≤ 1 := by
  unfold contactInd; split_ifs <;> omega

theorem deepCancelInd_le_one (h : ℕ) (s t : AgentState L K) : deepCancelInd h s t ≤ 1 := by
  unfold deepCancelInd
  split_ifs
  · cases hs : s.bias with
    | zero => simp [cancelIdx]
    | dyadic σ i =>
        cases ht : t.bias with
        | zero => cases σ <;> simp [cancelIdx]
        | dyadic τ j =>
            cases σ <;> cases τ <;> simp only [cancelIdx] <;>
              first | omega | (split_ifs <;> omega)
  · omega

/-- Indicators vanish on a non-Main. -/
theorem creditV_eq_zero_of_not_main (h : ℕ) (a : AgentState L K) (ha : a.role ≠ .main) :
    creditV h a = 0 := by
  simp [creditV, highZeroInd, deepInd, ha]

theorem highHourInd_eq_zero_of_not_main (h : ℕ) (a : AgentState L K) (ha : a.role ≠ .main) :
    highHourInd h a = 0 := by
  simp [highHourInd, ha]

/-- Indicators vanish on an inactive agent. -/
theorem creditV_eq_zero_of_inactive (h : ℕ) (a : AgentState L K) (ha : a.phase.val < 3) :
    creditV h a = 0 := by
  simp [creditV, highZeroInd, deepInd, show ¬ 3 ≤ a.phase.val by omega]

theorem highHourInd_eq_zero_of_inactive (h : ℕ) (a : AgentState L K) (ha : a.phase.val < 3) :
    highHourInd h a = 0 := by
  simp [highHourInd, show ¬ 3 ≤ a.phase.val by omega]

/-! ## The pair ledger -/

/-- The P11 ledger (51) on one ordered pair `(s, t) ↦ (s', t')`. -/
structure PairLedger (h : ℕ) (s t s' t' : AgentState L K) : Prop where
  v : creditV h s' + creditV h t' ≤
    creditV h s + creditV h t + 2 * contactInd h s t + 2 * deepCancelInd h s t
  hh : highHourInd h s' + highHourInd h t' ≤
    highHourInd h s + highHourInd h t + contactInd h s t + 2 * deepCancelInd h s t

theorem PairLedger.refl (h : ℕ) (s t : AgentState L K) : PairLedger h s t s t :=
  ⟨by omega, by omega⟩

theorem pairLedger_of_eq {h : ℕ} {s t s' t' : AgentState L K} (hs : s' = s) (ht : t' = t) :
    PairLedger h s t s' t' := by
  rw [hs, ht]; exact PairLedger.refl h s t

/-- Two Clock outputs carry no Main credit. -/
theorem pairLedger_of_clocks {h : ℕ} {s t s' t' : AgentState L K}
    (hs : s'.role = .clock) (ht : t'.role = .clock) : PairLedger h s t s' t' := by
  have h1 := creditV_eq_zero_of_not_main h s' (by rw [hs]; decide)
  have h2 := creditV_eq_zero_of_not_main h t' (by rw [ht]; decide)
  have h3 := highHourInd_eq_zero_of_not_main h s' (by rw [hs]; decide)
  have h4 := highHourInd_eq_zero_of_not_main h t' (by rw [ht]; decide)
  exact ⟨by omega, by omega⟩

/-- The inert branches of the Phase-3 rule. -/
theorem phase3Transition_eq_self (s t : AgentState L K)
    (hcc : ¬ (s.role = .clock ∧ t.role = .clock))
    (hdl : ¬ (s.role = .main ∧ s.bias = .zero ∧ t.role = .clock))
    (hdr : ¬ (t.role = .main ∧ t.bias = .zero ∧ s.role = .clock))
    (hmm : ¬ (s.role = .main ∧ t.role = .main)) :
    Phase3Transition L K s t = (s, t) := by
  unfold Phase3Transition
  simp [hcc, hdl, hdr, hmm]

/-- The both-Main branch of the Phase-3 rule. -/
theorem phase3Transition_eq_cancelSplit (s t : AgentState L K)
    (hsm : s.role = .main) (htm : t.role = .main) :
    Phase3Transition L K s t = phase3CancelSplit L K s t := by
  unfold Phase3Transition
  simp [hsm, htm]

/-- The drag by a Clock below minute `(h + 1) K` creates no stored hour above `h`. -/
theorem drag_hour_lt_iff (h : ℕ) (hour minute : ℕ) (hK : 0 < K)
    (hlt : minute < (h + 1) * K) :
    (h < max hour (min L (minute / K))) ↔ h < hour := by
  have hdiv : minute / K < h + 1 := (Nat.div_lt_iff_lt_mul hK).mpr hlt
  constructor
  · intro hmax
    rcases lt_max_iff.mp hmax with h1 | h1
    · exact h1
    · have h2 : h < minute / K := lt_of_lt_of_le h1 (min_le_right _ _)
      omega
  · intro h1
    exact lt_max_iff.mpr (Or.inl h1)

/-- The drag case, core: a zero Main `s` meets a Phase-3 Clock `t`; the Main's hour becomes
`max hour (min L (minute / K))` and nothing else changes. -/
theorem ledger_drag_core (h : ℕ) (s t s' : AgentState L K) (ht3 : t.phase.val = 3)
    (hsm : s.role = .main) (hsz : s.bias = .zero) (htc : t.role = .clock)
    (hrole : s'.role = s.role) (hphase : s'.phase = s.phase) (hbias : s'.bias = s.bias)
    (hhour : s'.hour.val = max s.hour.val (min L (t.minute.val / K))) :
    PairLedger h s t s' t := by
  have ht1 := creditV_eq_zero_of_not_main h t (by rw [htc]; decide)
  have ht2 := highHourInd_eq_zero_of_not_main h t (by rw [htc]; decide)
  have hsv : creditV h s = 2 * highZeroInd h s := by simp [creditV, deepInd, hsz, deepIdx]
  have hs'v : creditV h s' = 2 * highZeroInd h s' := by
    simp [creditV, deepInd, hbias, hsz, deepIdx]
  have hz : highZeroInd h s' = highHourInd h s' := by
    simp [highZeroInd, highHourInd, hbias, hsz]
  have hz0 : highZeroInd h s = highHourInd h s := by simp [highZeroInd, highHourInd, hsz]
  by_cases hc : (h + 1) * K ≤ t.minute.val
  · have hcontact : contactInd h s t = 1 := by
      unfold contactInd
      rw [if_pos (Or.inl ⟨hsm, htc, by omega, hc⟩)]
    have h1 := highHourInd_le_one h s'
    exact ⟨by rw [hcontact]; omega, by rw [hcontact]; omega⟩
  · have hK : 0 < K := by
      rcases Nat.eq_zero_or_pos K with h0 | h0
      · exfalso
        apply hc
        have hz0K : (h + 1) * K = 0 := by simp [h0]
        rw [hz0K]; exact Nat.zero_le _
      · exact h0
    have hiff := drag_hour_lt_iff (L := L) h s.hour.val t.minute.val hK (by omega)
    have hh : highHourInd h s' = highHourInd h s := by
      unfold highHourInd
      rw [hrole, hphase, hhour]
      simp only [hiff]
    exact ⟨by omega, by omega⟩

/-- The drag case with the Clock first, core. -/
theorem ledger_drag_core_right (h : ℕ) (s t t' : AgentState L K) (hs3 : s.phase.val = 3)
    (hsc : s.role = .clock) (htm : t.role = .main) (htz : t.bias = .zero)
    (hrole : t'.role = t.role) (hphase : t'.phase = t.phase) (hbias : t'.bias = t.bias)
    (hhour : t'.hour.val = max t.hour.val (min L (s.minute.val / K))) :
    PairLedger h s t s t' := by
  have hs1 := creditV_eq_zero_of_not_main h s (by rw [hsc]; decide)
  have hs2 := highHourInd_eq_zero_of_not_main h s (by rw [hsc]; decide)
  have htv : creditV h t = 2 * highZeroInd h t := by simp [creditV, deepInd, htz, deepIdx]
  have ht'v : creditV h t' = 2 * highZeroInd h t' := by
    simp [creditV, deepInd, hbias, htz, deepIdx]
  have hz : highZeroInd h t' = highHourInd h t' := by
    simp [highZeroInd, highHourInd, hbias, htz]
  have hz0 : highZeroInd h t = highHourInd h t := by simp [highZeroInd, highHourInd, htz]
  by_cases hc : (h + 1) * K ≤ s.minute.val
  · have hcontact : contactInd h s t = 1 := by
      unfold contactInd
      rw [if_pos (Or.inr ⟨htm, hsc, by omega, hc⟩)]
    have h1 := highHourInd_le_one h t'
    exact ⟨by rw [hcontact]; omega, by rw [hcontact]; omega⟩
  · have hK : 0 < K := by
      rcases Nat.eq_zero_or_pos K with h0 | h0
      · exfalso
        apply hc
        have hz0K : (h + 1) * K = 0 := by simp [h0]
        rw [hz0K]; exact Nat.zero_le _
      · exact h0
    have hiff := drag_hour_lt_iff (L := L) h t.hour.val s.minute.val hK (by omega)
    have hh : highHourInd h t' = highHourInd h t := by
      unfold highHourInd
      rw [hrole, hphase, hhour]
      simp only [hiff]
    exact ⟨by omega, by omega⟩

/-- The drag case: a zero Main `s` meets a Phase-3 Clock `t`. -/
theorem phase3Transition_ledger_drag_left (h : ℕ) (s t : AgentState L K)
    (ht3 : t.phase.val = 3)
    (hsm : s.role = .main) (hsz : s.bias = .zero) (htc : t.role = .clock) :
    PairLedger h s t (Phase3Transition L K s t).1 (Phase3Transition L K s t).2 := by
  rw [HourCoupling.phase3_drag_left s t hsm hsz htc]
  exact ledger_drag_core h s t _ ht3 hsm hsz htc rfl rfl rfl rfl

/-- The drag case with the Clock first. -/
theorem phase3Transition_ledger_drag_right (h : ℕ) (s t : AgentState L K)
    (hs3 : s.phase.val = 3)
    (hsc : s.role = .clock) (htm : t.role = .main) (htz : t.bias = .zero) :
    PairLedger h s t (Phase3Transition L K s t).1 (Phase3Transition L K s t).2 := by
  rw [HourCoupling.phase3_drag_right s t hsc htm htz]
  exact ledger_drag_core_right h s t _ hs3 hsc htm htz rfl rfl rfl rfl

set_option maxHeartbeats 800000 in -- sixteen constructor cases, each closed by simp_all and omega
/-- The both-Main case: cancel and split. -/
theorem phase3Transition_ledger_mains (h : ℕ) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsm : s.role = .main) (htm : t.role = .main) :
    PairLedger h s t (Phase3Transition L K s t).1 (Phase3Transition L K s t).2 := by
  rw [phase3Transition_eq_cancelSplit s t hsm htm]
  cases hsb : s.bias with
  | zero =>
      cases htb : t.bias with
      | zero =>
          constructor <;>
            (simp [creditV, highZeroInd, deepInd, deepIdx, highHourInd, contactInd,
              deepCancelInd, cancelIdx, phase3CancelSplit, hsb, htb, hs3, ht3, hsm, htm] <;>
              first | omega | (split_ifs <;> (try dsimp only at *) <;> first | omega | (simp_all <;> first | omega | (split_ifs <;> omega))))
      | dyadic τ j =>
          cases τ <;> constructor <;>
            (simp [creditV, highZeroInd, deepInd, deepIdx, highHourInd, contactInd,
              deepCancelInd, cancelIdx, phase3CancelSplit, hsb, htb, hs3, ht3, hsm, htm] <;>
              first | omega | (split_ifs <;> (try dsimp only at *) <;> first | omega | (simp_all <;> first | omega | (split_ifs <;> omega))))
  | dyadic σ i =>
      cases htb : t.bias with
      | zero =>
          cases σ <;> constructor <;>
            (simp [creditV, highZeroInd, deepInd, deepIdx, highHourInd, contactInd,
              deepCancelInd, cancelIdx, phase3CancelSplit, hsb, htb, hs3, ht3, hsm, htm] <;>
              first | omega | (split_ifs <;> (try dsimp only at *) <;> first | omega | (simp_all <;> first | omega | (split_ifs <;> omega))))
      | dyadic τ j =>
          cases σ <;> cases τ <;> constructor <;>
            (simp [creditV, highZeroInd, deepInd, deepIdx, highHourInd, contactInd,
              deepCancelInd, cancelIdx, phase3CancelSplit, hsb, htb, hs3, ht3, hsm, htm] <;>
              first | omega | (split_ifs <;> (try dsimp only at *) <;> first | omega | (simp_all <;> first | omega | (split_ifs <;> omega))))

/-- The P11 pair ledger for the implemented Phase-3 rule on two Phase-3 agents. -/
theorem phase3Transition_ledger (h : ℕ) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3) :
    PairLedger h s t (Phase3Transition L K s t).1 (Phase3Transition L K s t).2 := by
  by_cases hcc : s.role = .clock ∧ t.role = .clock
  · exact pairLedger_of_clocks (Phase3Transition_preserves_clock_role L K s t hcc.1)
      (Phase3Transition_second_preserves_clock_role L K s t hcc.2)
  by_cases hmm : s.role = .main ∧ t.role = .main
  · exact phase3Transition_ledger_mains h s t hs3 ht3 hmm.1 hmm.2
  by_cases hdl : s.role = .main ∧ s.bias = .zero ∧ t.role = .clock
  · exact phase3Transition_ledger_drag_left h s t ht3 hdl.1 hdl.2.1 hdl.2.2
  by_cases hdr : t.role = .main ∧ t.bias = .zero ∧ s.role = .clock
  · exact phase3Transition_ledger_drag_right h s t hs3 hdr.2.2 hdr.1 hdr.2.1
  rw [phase3Transition_eq_self s t hcc hdl hdr hmm]
  exact PairLedger.refl h s t

/-- The P11 pair ledger for the virtual rule on two Phase-3 agents. -/
theorem virtualRule_ledger (h : ℕ) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3) :
    PairLedger h s t (virtualRule s t).1 (virtualRule s t).2 := by
  by_cases hcc : s.role = .clock ∧ t.role = .clock
  · have hr := virtualRule_active_clock_pair s t hs3 ht3 hcc.1 hcc.2
    exact pairLedger_of_clocks hr.1 hr.2.1
  · have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs3 ht3
    have hnc : ¬ CapCounterPair s t := by
      intro hc
      apply hcc
      simpa only [hepi] using And.intro hc.2.2.1 hc.2.2.2.1
    have hleft : (Phase3Transition L K s t).1.phase = s.phase :=
      (Phase3Transition_left_output_eq_rule1 L K s t s (by rw [if_neg hcc])).2
    have hright : (Phase3Transition L K s t).2.phase = t.phase :=
      (Phase3Transition_right_output_eq_rule1 L K s t t (by rw [if_neg hcc])).2
    have h1 : (Phase3Transition L K s t).1.phase.val ≠ 10 := by rw [hleft]; omega
    have h2 : (Phase3Transition L K s t).2.phase.val ≠ 10 := by rw [hright]; omega
    rw [virtualRule_eq_transition_of_not_cap s t hnc,
      HourCoupling.transition_eq_phase3 s t hs3 ht3 h1 h2]
    exact phase3Transition_ledger h s t hs3 ht3

/-! ## The ceiling (item 38) -/

/-- All Main fields of an agent at or below `h`: an active Main has stored hour `≤ h`
and, if biased, index `≤ h`. -/
def MainFieldsLe (h : ℕ) (a : AgentState L K) : Prop :=
  3 ≤ a.phase.val → a.role = .main →
    a.hour.val ≤ h ∧ ∀ σ j, a.bias = Bias.dyadic σ j → j.val ≤ h

theorem creditV_eq_zero_of_mainFieldsLe {h : ℕ} {a : AgentState L K} (ha : MainFieldsLe h a) :
    creditV h a = 0 := by
  unfold creditV highZeroInd deepInd
  by_cases h1 : 3 ≤ a.phase.val ∧ a.role = .main ∧ a.bias = .zero ∧ h < a.hour.val
  · exact absurd h1.2.2.2 (by have := (ha h1.1 h1.2.1).1; omega)
  · by_cases h2 : 3 ≤ a.phase.val ∧ a.role = .main
    · rw [if_neg h1, if_pos h2]
      cases hb : a.bias with
      | zero => simp [deepIdx]
      | dyadic σ j =>
          have hne : ¬ h < j.val := by have := (ha h2.1 h2.2).2 σ j hb; omega
          simp [deepIdx, hne]
    · simp [h1, h2]

theorem highHourInd_eq_zero_of_mainFieldsLe {h : ℕ} {a : AgentState L K}
    (ha : MainFieldsLe h a) : highHourInd h a = 0 := by
  unfold highHourInd
  split_ifs with h1
  · exact absurd h1.2.2 (by have := (ha h1.1 h1.2.1).1; omega)
  · rfl

theorem mainFieldsLe_of_zero {h : ℕ} {a : AgentState L K}
    (hv : creditV h a = 0) (hh : highHourInd h a = 0) : MainFieldsLe h a := by
  intro h3 hm
  constructor
  · by_contra hcon
    have : highHourInd h a = 1 := by
      unfold highHourInd
      rw [if_pos ⟨h3, hm, by omega⟩]
    omega
  · intro σ j hb
    by_contra hcon
    have : deepInd h a = 1 := by
      unfold deepInd
      rw [if_pos ⟨h3, hm⟩, hb]
      simp only [deepIdx]
      rw [if_pos (by omega)]
    unfold creditV at hv
    omega

/-- Zero deep-cancellation credit when both Main fields are at or below `h`. -/
theorem deepCancelInd_eq_zero_of_mainFieldsLe {h : ℕ} {s t : AgentState L K}
    (hs : MainFieldsLe h s) (ht : MainFieldsLe h t) : deepCancelInd h s t = 0 := by
  unfold deepCancelInd
  split_ifs with hc
  · cases hsb : s.bias with
    | zero => simp [cancelIdx]
    | dyadic σ i =>
        cases htb : t.bias with
        | zero => cases σ <;> simp [cancelIdx]
        | dyadic τ j =>
            have hi := (hs hc.1 hc.2.2.1).2 σ i hsb
            cases σ <;> cases τ <;> simp only [cancelIdx] <;> try rfl
            · split_ifs with hc'
              · exact absurd hc'.2 (by omega)
              · rfl
            · split_ifs with hc'
              · exact absurd hc'.2 (by omega)
              · rfl
  · rfl

/-- Item 38: without a contact with a Clock at minute `≥ (h + 1) K`, the virtual rule
keeps all Main fields at or below `h`. -/
theorem virtualRule_ceiling (h : ℕ) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hs : MainFieldsLe h s) (ht : MainFieldsLe h t) (hc : contactInd h s t = 0) :
    MainFieldsLe h (virtualRule s t).1 ∧ MainFieldsLe h (virtualRule s t).2 := by
  have hl := virtualRule_ledger h s t hs3 ht3
  have hd := deepCancelInd_eq_zero_of_mainFieldsLe hs ht
  have hv := hl.v
  have hh := hl.hh
  rw [creditV_eq_zero_of_mainFieldsLe hs, creditV_eq_zero_of_mainFieldsLe ht, hc, hd] at hv
  rw [highHourInd_eq_zero_of_mainFieldsLe hs, highHourInd_eq_zero_of_mainFieldsLe ht, hc, hd]
    at hh
  exact ⟨mainFieldsLe_of_zero (by omega) (by omega), mainFieldsLe_of_zero (by omega) (by omega)⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainLedger

end

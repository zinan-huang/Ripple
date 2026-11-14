-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingCreditClockBridge.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingPendingCreditTransitions
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingLiveProduct

/-!
# Clock-history exceptions are exactly the terminal credit exceptions

This bridge uses the original fixed physical roles and the actual active flag.
No inactive stale hour or bias field contributes to the count.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingCreditClockBridge

open TimeTheorem PairLog StageEventSpec
open AveragingCreditCount AveragingTerminalDebt AveragingPendingCredit
open AveragingMixedLedgers AveragingLiveProduct

variable {L K : ℕ}

def HighZeroAt (k : ℕ) (a : AgentState L K) : Prop :=
  a.phase.val = 3 ∧ a.role = .main ∧ a.bias = .zero ∧ k < a.hour.val

open Classical in
def highZeroAtom (k : ℕ) (a : AgentState L K) : ℕ :=
  if HighZeroAt k a then 1 else 0

def highZeroCount (k : ℕ) (c : Cfg L K) : ℕ :=
  (c.map (highZeroAtom k)).sum

theorem exceptionWeight_split (k : ℕ) (a : AgentState L K)
    (hcap : a.phase.val ≤ 3) :
    exceptionWeight k a = highZeroAtom k a + deepAtom k a := by
  by_cases hp : a.phase.val = 3
  · by_cases hm : a.role = .main <;> cases hb : a.bias <;>
      simp [exceptionWeight, highZeroAtom, HighZeroAt, deepAtom, hp, hm, hb]
  · have hlo : a.phase.val < 3 := by omega
    simp [exceptionWeight, highZeroAtom, HighZeroAt, deepAtom, hp, hlo]

theorem exceptionCount_split (k : ℕ) (c : Cfg L K)
    (hcap : ∀ a ∈ c, a.phase.val ≤ 3) :
    exceptionCount k c = highZeroCount k c + deepCount k c := by
  revert hcap
  induction c using Multiset.induction_on with
  | empty =>
      intro _
      simp [exceptionCount, highZeroCount, deepCount]
  | cons a c ih =>
      intro hcap
      have ha := exceptionWeight_split k a (hcap a (Multiset.mem_cons_self a c))
      have ht := ih (fun b hb => hcap b (Multiset.mem_cons_of_mem hb))
      simp only [exceptionCount, highZeroCount, deepCount, Multiset.map_cons,
        Multiset.sum_cons] at ht ⊢
      omega

open Classical in
theorem highZeroCount_eq_countP (k : ℕ) (c : Cfg L K) :
    highZeroCount k c = c.countP (HighZeroAt k) := by
  classical
  induction c using Multiset.induction_on with
  | empty => simp [highZeroCount]
  | cons a c ih =>
      by_cases ha : HighZeroAt k a <;>
        simp [highZeroCount, highZeroAtom, Multiset.countP_cons, ha] at ih ⊢ <;> omega

theorem highZeroCount_clockHistory {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ v : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (hSv : S ≤ v) (hvρ : v < ρ) (k : ℕ) :
    highZeroCount k (trace init ω v) = highHourZeroMains init ω S v k := by
  classical
  rw [highZeroCount_eq_countP, countP_trace_eq_labelCount]
  unfold highHourZeroMains
  apply congrArg (labelCount init)
  funext i
  apply propext
  have hi : labelsAt init ω v i ∈ trace init ω v := by
    rw [← labelsAt_config init ω v]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hphase := (h.phase_range v hSv hvρ _ hi).2
  have hrole := h.roles_fixed v hSv hvρ i
  simp only [HighZeroAt, fixedRole, active, hrole]
  constructor
  · rintro ⟨hp, hr, hb, hh⟩
    exact ⟨hr, by omega, hb, hh⟩
  · rintro ⟨hr, hp, hb, hh⟩
    exact ⟨by omega, hr, hb, hh⟩

theorem exceptionCount_clockHistory {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ v : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (hSv : S ≤ v) (hvρ : v < ρ) (k : ℕ) :
    exceptionCount k (trace init ω v) =
      highHourZeroMains init ω S v k + deepBiasedMains init ω S v k := by
  rw [exceptionCount_split k _ (fun a ha => (h.phase_range v hSv hvρ a ha).2),
    highZeroCount_clockHistory h hSv hvρ,
    deepCount_clockHistory h hSv hvρ]

theorem exceptionCount_bound_clockHistory {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ v : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (hSv : S ≤ v) (hvρ : v < ρ) (k : ℕ)
    (hk : k ≤ PhaseThreeModel.Numeric.hourIndex n) (hv : v ≤ w.finish k) :
    (exceptionCount k (trace init ω v) : ℚ) ≤
      (3 / 1250 : ℚ) * timeMainCount (trace init ω S) := by
  have hn := h.main_deep_tail k hk v hSv hv
  rw [← exceptionCount_clockHistory h hSv hvρ k] at hn
  have hq : (1250 : ℚ) * (exceptionCount k (trace init ω v) : ℚ) ≤
      3 * (timeMainCount (trace init ω S) : ℚ) := by exact_mod_cast hn
  linarith

/-- The actual clock-history exception bound discharges the count premise
of the .9616 M initial mixed-credit certificate. -/
theorem initial_mixed_credit_clockHistory {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ v : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (hSv : S ≤ v) (hvρ : v < ρ) (σ : Sign) (ell : ℕ)
    (hk : ell + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hv : v ≤ w.finish (ell + 2))
    (hY : debtY σ (ell + 2) (trace init ω v) ≤
      (7 / 200 : ℚ) * timeMainCount (trace init ω S))
    (hphi : augmentedPhi ell (trace init ω v) ≤
      (1 / 1000 : ℚ) * timeMainCount (trace init ω S)) :
    (601 / 625 : ℚ) * timeMainCount (trace init ω S) ≤
      mixedTotalCredit σ ell (ell + 2) (trace init ω v) := by
  have hM : RoleSplitConcentration.mainCount (trace init ω v) =
      timeMainCount (trace init ω S) := by
    convert h.main_count v hSv hvρ using 1 <;>
      simp only [RoleSplitConcentration.mainCount, timeMainCount] <;> congr!
  exact initial_mixed_credit_of_terminal_bounds σ ell _ _
    hM hY (exceptionCount_bound_clockHistory h hSv hvρ (ell + 2) hk hv) hphi

end Ripple.PopulationProtocol.ExactMajority.AveragingCreditClockBridge

end

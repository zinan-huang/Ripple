import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainActivation
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRows

/-!
# The P11 ledger along the virtual path (N12, Main row)

The pair ledger of `PhaseThreeClockMainActivation.virtualRule_step_ledger` summed over
the labels gives the pathwise form of PHASE3 (51) on the virtual continuation from an
asynchronous entry `(S, T)`:

* `vSum h f = 2 Z + B` and `hSum h f = H` on a labelling `f`, with the step credit
  `stepCredit h t = [Main/high-Clock contact] + 2 [deep cancellation]` of the pair drawn
  at `t + 1` evaluated at the virtual labelling of time `t`;
* `vSum_le_of_credit`: for `S ≤ u ≤ v`, `vSum (v) ≤ vSum (u) + 2 credit h u v` and
  `hSum (v) ≤ hSum (u) + credit h u v`, with `credit h u v = ∑_{t ∈ [u, v)} stepCredit h t`;
* `mainFieldsLe_of_noHighClock` (item 38): while no Phase-3 Clock has minute `≥ (h+1) K`,
  every active Main keeps hour and index at most `h`;
* the row counts `highHourMainsL`, `highHourZeroMainsL + deepBiasedMainsL` of
  `PhaseThreeClockCore` are `hSum` and at most `vSum` (roles fixed after the seed).
-/

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainPath

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockEmbedding PhaseThreeClockEmbeddingBridge
  PhaseThreeClockCore PhaseThreeClockMainLedger PhaseThreeClockMainActivation

variable {n : ℕ} (init : InputCfg n) (ω : InputLog n)

/-! ## Sums and credits -/

/-- `2 Z + B` on a labelling. -/
def vSum (h : ℕ) (f : Lab init) : ℕ := ∑ i, creditV h (f i)

/-- `H` on a labelling. -/
def hSum (h : ℕ) (f : Lab init) : ℕ := ∑ i, highHourInd h (f i)

/-- The credit of the step `t → t + 1`. -/
def stepCredit (h t : ℕ) : ℕ :=
  match drawLabels init ω (t + 1) with
  | none => 0
  | some (i, j) =>
      contactInd h (virtualLabels init ω t i) (virtualLabels init ω t j) +
        2 * deepCancelInd h (virtualLabels init ω t i) (virtualLabels init ω t j)

/-- The accumulated credit on `[u, v)`. -/
def credit (h u v : ℕ) : ℕ := ∑ t ∈ Finset.Ico u v, stepCredit init ω h t

theorem credit_self (h u : ℕ) : credit init ω h u u = 0 := by
  simp [credit]

theorem credit_succ (h u v : ℕ) (huv : u ≤ v) :
    credit init ω h u (v + 1) = credit init ω h u v + stepCredit init ω h v := by
  unfold credit
  rw [Finset.sum_Ico_succ_top huv]

theorem stepCredit_of_none (h t : ℕ) (hd : drawLabels init ω (t + 1) = none) :
    stepCredit init ω h t = 0 := by
  simp [stepCredit, hd]

theorem stepCredit_of_some (h t : ℕ) (i j : Fin init.card)
    (hd : drawLabels init ω (t + 1) = some (i, j)) :
    stepCredit init ω h t =
      contactInd h (virtualLabels init ω t i) (virtualLabels init ω t j) +
        2 * deepCancelInd h (virtualLabels init ω t i) (virtualLabels init ω t j) := by
  simp [stepCredit, hd]

/-! ## The one-step inequality -/

theorem sums_succ_le {S T : ℕ} (hentry : AsyncEntry init ω S T) (h t : ℕ) (hSt : S ≤ t) :
    vSum init h (virtualLabels init ω (t + 1)) ≤
        vSum init h (virtualLabels init ω t) + 2 * stepCredit init ω h t ∧
      hSum init h (virtualLabels init ω (t + 1)) ≤
        hSum init h (virtualLabels init ω t) + stepCredit init ω h t := by
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      rw [virtualLabels_succ, hd, stepCredit_of_none init ω h t hd]
      exact ⟨by simp [auxStep], by simp [auxStep]⟩
  | some p =>
      rcases p with ⟨i, j⟩
      have hij := (labelsAt_selected_transition init ω t i j hd).1
      set f := virtualLabels init ω t with hf
      have hpre := (henv t hSt).phase_range
      have hpost := fun k => ((henv (t + 1) (by omega)).phase_range k).2
      have hleft : (virtualRule (f i) (f j)).1.phase.val ≤ 3 := by
        have h := hpost i
        rw [virtualLabels_succ, hd] at h
        simpa only [auxStep, ruleUpdate, Function.update_of_ne hij, Function.update_self] using h
      have hright : (virtualRule (f i) (f j)).2.phase.val ≤ 3 := by
        have h := hpost j
        rw [virtualLabels_succ, hd] at h
        simpa only [auxStep, ruleUpdate, Function.update_self] using h
      have hl := virtualRule_step_ledger (by decide) h (f i) (f j) (hpre i) (hpre j) hleft hright
      have hv := sum_update_pair (creditV h) f i j hij (virtualRule (f i) (f j)).1
        (virtualRule (f i) (f j)).2
      have hh := sum_update_pair (highHourInd h) f i j hij (virtualRule (f i) (f j)).1
        (virtualRule (f i) (f j)).2
      rw [stepCredit_of_some init ω h t i j hd, virtualLabels_succ, hd]
      simp only [auxStep, ruleUpdate]
      unfold vSum hSum
      have h1 := hl.v
      have h2 := hl.hh
      rw [← hf]
      constructor <;> omega

/-! ## Accumulation -/

theorem sums_le_of_credit {S T : ℕ} (hentry : AsyncEntry init ω S T) (h u v : ℕ)
    (hSu : S ≤ u) (huv : u ≤ v) :
    vSum init h (virtualLabels init ω v) ≤
        vSum init h (virtualLabels init ω u) + 2 * credit init ω h u v ∧
      hSum init h (virtualLabels init ω v) ≤
        hSum init h (virtualLabels init ω u) + credit init ω h u v := by
  induction v, huv using Nat.le_induction with
  | base => simp [credit_self]
  | succ v huv ih =>
      have hstep := sums_succ_le init ω hentry h v (by omega)
      rw [credit_succ init ω h u v huv]
      constructor <;> omega

/-! ## The ceiling (item 38) -/

/-- No Phase-3 Clock at minute `≥ (h + 1) K` in the labelling. -/
def NoHighClock (h : ℕ) (f : Lab init) : Prop :=
  ∀ i, (f i).role = .clock → 3 ≤ (f i).phase.val → (f i).minute.val < (h + 1) * 256

theorem contactInd_eq_zero_of_noHighClock (h : ℕ) (f : Lab init) (hf : NoHighClock init h f)
    (i j : Fin init.card) : contactInd h (f i) (f j) = 0 := by
  unfold contactInd
  rw [if_neg]
  rintro (⟨-, hc, h3, hm⟩ | ⟨-, hc, h3, hm⟩)
  · have := hf j hc h3
    omega
  · have := hf i hc h3
    omega

theorem stepCredit_eq_zero_of_ceiling (h t : ℕ)
    (hall : ∀ i, MainFieldsLe h (virtualLabels init ω t i))
    (hnh : NoHighClock init h (virtualLabels init ω t)) :
    stepCredit init ω h t = 0 := by
  cases hd : drawLabels init ω (t + 1) with
  | none => exact stepCredit_of_none init ω h t hd
  | some p =>
      rcases p with ⟨i, j⟩
      rw [stepCredit_of_some init ω h t i j hd,
        contactInd_eq_zero_of_noHighClock init h _ hnh i j,
        deepCancelInd_eq_zero_of_mainFieldsLe (hall i) (hall j)]

/-- All Main fields at or below `h` on the whole labelling, from zero sums. -/
theorem mainFieldsLe_of_sums_zero (h : ℕ) (f : Lab init)
    (hv : vSum init h f = 0) (hh : hSum init h f = 0) : ∀ i, MainFieldsLe h (f i) := by
  intro i
  unfold vSum at hv
  unfold hSum at hh
  have h1 : creditV h (f i) = 0 :=
    (Finset.sum_eq_zero_iff.mp hv) i (Finset.mem_univ i)
  have h2 : highHourInd h (f i) = 0 :=
    (Finset.sum_eq_zero_iff.mp hh) i (Finset.mem_univ i)
  exact mainFieldsLe_of_zero h1 h2

theorem sums_zero_of_mainFieldsLe (h : ℕ) (f : Lab init) (hall : ∀ i, MainFieldsLe h (f i)) :
    vSum init h f = 0 ∧ hSum init h f = 0 := by
  constructor
  · exact Finset.sum_eq_zero fun i _ => creditV_eq_zero_of_mainFieldsLe (hall i)
  · exact Finset.sum_eq_zero fun i _ => highHourInd_eq_zero_of_mainFieldsLe (hall i)

/-- The ceiling propagates one step. -/
theorem mainFieldsLe_succ {S T : ℕ} (hentry : AsyncEntry init ω S T) (h t : ℕ) (hSt : S ≤ t)
    (hall : ∀ i, MainFieldsLe h (virtualLabels init ω t i))
    (hnh : NoHighClock init h (virtualLabels init ω t)) :
    ∀ i, MainFieldsLe h (virtualLabels init ω (t + 1) i) := by
  have hstep := sums_succ_le init ω hentry h t hSt
  have hz := sums_zero_of_mainFieldsLe init h _ hall
  have hc := stepCredit_eq_zero_of_ceiling init ω h t hall hnh
  rw [hz.1, hc] at hstep
  rw [hz.2] at hstep
  exact mainFieldsLe_of_sums_zero init h _ (by omega) (by omega)

/-- Item 38: all Main fields are at or below `h` on `[S, σ]` when no Phase-3 Clock reaches
minute `(h + 1) K` before `σ`, given the ceiling at the seed. -/
theorem mainFieldsLe_of_noHighClock {S T : ℕ} (hentry : AsyncEntry init ω S T) (h σ : ℕ)
    (hSσ : S ≤ σ)
    (hseed : ∀ i, MainFieldsLe h (virtualLabels init ω S i))
    (hnh : ∀ t, S ≤ t → t < σ → NoHighClock init h (virtualLabels init ω t)) :
    ∀ t, S ≤ t → t ≤ σ → ∀ i, MainFieldsLe h (virtualLabels init ω t i) := by
  intro t hSt htσ
  induction t, hSt using Nat.le_induction with
  | base => exact hseed
  | succ t hSt ih =>
      exact mainFieldsLe_succ init ω hentry h t hSt (ih (by omega)) (hnh t hSt (by omega))

/-- The ceiling at the seed: every active agent at the seed is a fresh Phase-3 entry
agent. -/
theorem mainFieldsLe_seed {S T : ℕ} (hentry : AsyncEntry init ω S T) (h : ℕ) :
    ∀ i, MainFieldsLe h (virtualLabels init ω S i) := by
  intro i h3 _
  have heq := virtualLabels_eq_labelsAt_through_asyncEntry init ω S T hentry S hentry.order
  have hmem : virtualLabels init ω S i ∈ trace init ω S := by
    rw [heq]
    exact labelsAt_mem_trace init ω S i
  have hphase : (virtualLabels init ω S i).phase.val = 3 := by
    have := (hentry.seed_profile.phase_range _ hmem).2
    omega
  have hfresh := hentry.seed_profile.fresh _ hmem hphase
  exact mainFieldsLe_of_entry h _ hfresh h3 ‹_›

/-! ## The row counts are the sums -/

theorem fixedRole_iff {S T : ℕ} (hentry : AsyncEntry init ω S T) (v : ℕ) (hSv : S ≤ v)
    (i : Fin init.card) (r : Role) :
    fixedRoleL init (virtualLabels init ω S) r i ↔ (virtualLabels init ω v i).role = r := by
  unfold fixedRoleL
  rw [virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry v hSv i,
    virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry S le_rfl i]

theorem highHourMainsL_eq_hSum {S T : ℕ} (hentry : AsyncEntry init ω S T) (h v : ℕ)
    (hSv : S ≤ v) :
    highHourMainsL init (virtualLabels init ω S) (virtualLabels init ω v) h =
      hSum init h (virtualLabels init ω v) := by
  classical
  unfold highHourMainsL labelCount hSum
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  unfold highHourInd activeL
  simp only [fixedRole_iff init ω hentry v hSv i .main]
  by_cases h1 : (virtualLabels init ω v i).role = .main ∧ 3 ≤ (virtualLabels init ω v i).phase.val ∧
      h < (virtualLabels init ω v i).hour.val
  · rw [if_pos h1, if_pos ⟨h1.2.1, h1.1, h1.2.2⟩]
  · rw [if_neg h1, if_neg (fun h2 => h1 ⟨h2.2.1, h2.1, h2.2.2⟩)]

theorem highHourZero_add_deep_le_vSum {S T : ℕ} (hentry : AsyncEntry init ω S T) (h v : ℕ)
    (hSv : S ≤ v) :
    highHourZeroMainsL init (virtualLabels init ω S) (virtualLabels init ω v) h +
        deepBiasedMainsL init (virtualLabels init ω S) (virtualLabels init ω v) h ≤
      vSum init h (virtualLabels init ω v) := by
  classical
  unfold highHourZeroMainsL deepBiasedMainsL labelCount vSum
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  dsimp only
  unfold creditV highZeroInd deepInd activeL
  simp only [fixedRole_iff init ω hentry v hSv i .main]
  set a := virtualLabels init ω v i with ha
  have hdeep : (if a.role = .main ∧ 3 ≤ a.phase.val ∧ ∃ σ j, a.bias = Bias.dyadic σ j ∧ h < j.val
      then 1 else 0) ≤ (if 3 ≤ a.phase.val ∧ a.role = .main then deepIdx h a.bias else 0) := by
    split_ifs with h1 h2 h2
    · obtain ⟨-, -, σ, j, hb, hj⟩ := h1
      rw [hb]
      simp [deepIdx, hj]
    · exact absurd ⟨h1.2.1, h1.1⟩ h2
    · omega
    · omega
  have hzero : (if a.role = .main ∧ 3 ≤ a.phase.val ∧ a.bias = Bias.zero ∧ h < a.hour.val
      then 1 else 0) ≤ 2 * (if 3 ≤ a.phase.val ∧ a.role = .main ∧ a.bias = Bias.zero ∧ h < a.hour.val
      then 1 else 0) := by
    split_ifs with h1 h2 h2
    · omega
    · exact absurd ⟨h1.2.1, h1.1, h1.2.2⟩ h2
    · omega
    · omega
  omega

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainPath

end

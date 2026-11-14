-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingClockBlocks.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingWorkBudget

/-!
# Completion and ordering of the earlier old-potential work blocks

For h = r + q, the q-6 work hours are r+1 through h-6.
This file proves their actual clock-window alignment. The supplied stopping
times must agree with those clock work starts on the history in question;
AveragingHourStops supplies the canonical first-hit functions separately.
No inductive mass bound or current-potential gate is assumed by this alignment
lemma, and neither is produced here.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingClockBlocks

open TimeTheorem StageEventSpec AveragingNumerics AveragingOldBlocks
open AveragingTerminalDebtDeadlines AveragingCancellationAlgebra
open AveragingObservedBlocks AveragingWorkBudget

theorem clockHistory_start_mono {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ}
    {w : ClockTimes init} (H : ClockHistory init ω S T ρ w) (hn : 0 < n)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ PhaseThreeModel.Numeric.hourIndex n) :
    w.start a ≤ w.start b := by
  have hsucc (j : ℕ) (hj : j + 1 ≤ PhaseThreeModel.Numeric.hourIndex n) :
      w.start j ≤ w.start (j + 1) := by
    have hfit := clockHistory_raw_work_fits H hn j (by omega)
    have hnext := H.previous_end (j + 1) (by omega) hj
    have hpred : j + 1 - 1 = j := by omega
    rw [hpred] at hnext
    omega
  have hmono : ∀ d a : ℕ, a + d ≤ PhaseThreeModel.Numeric.hourIndex n →
      w.start a ≤ w.start (a + d) := by
    intro d
    induction d with
    | zero =>
        intro a ha
        simp
    | succ d ih =>
        intro a ha
        have hfirst := ih a (by omega)
        have hlast := hsucc (a + d) (by omega)
        simpa only [Nat.add_succ] using hfirst.trans hlast
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact hmono d a hb

/-- All q-6 earlier blocks lie between the successful r-potential checkpoint
and the current h-warmup. The assertion is pointwise on the original log. -/
theorem clockHistory_old_blocks_complete {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ}
    {w : ClockTimes init} (H : ClockHistory init ω S T ρ w) (hn : 0 < n)
    (r q : ℕ) (hq : 7 ≤ q)
    (hrq : r + q ≤ PhaseThreeModel.Numeric.hourIndex n)
    (σ : Fin (q - 6) → InputLog n → WithTop ℕ)
    (hσ : ∀ j : Fin (q - 6),
      σ j ω = ((w.start (r + 1 + j.val) +
        clockWarmup n (clockCount (trace init ω S)) : ℕ) : WithTop ℕ)) :
    let C := clockCount (trace init ω S)
    let M := timeMainCount (trace init ω S)
    let P := w.start r + clockWarmup n C + potentialTrials n M
    let W := w.start (r + q) + clockWarmup n C
    BlocksComplete P (oldWorkTrials n M) σ (W - P) ω := by
  let C := clockCount (trace init ω S)
  let M := timeMainCount (trace init ω S)
  let P := w.start r + clockWarmup n C + potentialTrials n M
  let W := w.start (r + q) + clockWarmup n C
  let a : Fin (q - 6) → ℕ :=
    fun j => w.start (r + 1 + j.val) + clockWarmup n C
  change BlocksComplete P (oldWorkTrials n M) σ (W - P) ω
  have hcheckpoint : P < w.finish r := by
    have hfit := clockHistory_raw_work_fits H hn r (by omega)
    have hbudget : clockWarmup n C + potentialTrials n M ≤ rawWork n M C := by
      unfold clockWarmup potentialTrials rawWork
      omega
    have hle : P ≤ w.start r + rawWork n M C := by
      simpa only [P, Nat.add_assoc] using
        (add_le_add (le_refl (w.start r)) hbudget)
    exact hle.trans_lt hfit
  have hnext : w.finish r < w.start (r + 1) := by
    have h := H.previous_end (r + 1) (by omega) (by omega)
    simpa only [Nat.add_sub_cancel] using h
  have hpw : P ≤ W := by
    have hmono := clockHistory_start_mono H hn (r + 1) (r + q) (by omega) hrq
    dsimp only [W]
    omega
  have hend : P + (W - P) = W := by omega
  refine ⟨a, ?_, ?_⟩
  · intro j
    have hj := j.isLt
    have hbefore := clockHistory_start_mono H hn (r + 1)
      (r + 1 + j.val) (by omega) (by omega)
    have hdone :
        w.start (r + 1 + j.val) + clockWarmup n C + oldWorkTrials n M <
          w.start (r + 1 + j.val + 1) :=
      clockHistory_oldWork_before_next H hn (r + 1 + j.val) (by omega)
    have hafter := clockHistory_start_mono H hn (r + 1 + j.val + 1)
      (r + q) (by omega) hrq
    refine ⟨hσ j, ?_, ?_⟩
    · dsimp only [a]
      omega
    · rw [hend]
      dsimp only [a, W]
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hval : i.val < j.val := hij
    have hdone :
        w.start (r + 1 + i.val) + clockWarmup n C + oldWorkTrials n M <
          w.start (r + 1 + i.val + 1) :=
      clockHistory_oldWork_before_next H hn (r + 1 + i.val) (by omega)
    have hafter := clockHistory_start_mono H hn (r + 1 + i.val + 1)
      (r + 1 + j.val) (by omega) (by omega)
    dsimp only [a]
    omega

end Ripple.PopulationProtocol.ExactMajority.AveragingClockBlocks

end

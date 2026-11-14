-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedReceiptProducer.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingSeedReceipt
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedTwoLevelAlternative

/-!
# Retained-credit N16 receipt producer

The existing N16 proof converts its protected credits to raw bands.  This file
keeps the credits and packages exactly the receipt required by N18.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem StageEventSpec
open AveragingSparseEntry
open AveragingCreditTransitions AveragingPendingCredit
open AveragingPendingCreditTransitions AveragingCreditCount
open AveragingMixedLedgers AveragingTerminalDebt
open AveragingCheckpointReadout AveragingTerminalReadout
open AveragingIntegerPotential LateSamplingSeedReceipt

variable {n : ℕ}

/-- Any retained credit produced before the first Phase-4 seed survives through
that genuine first-exit interaction.  The source configurations are all Phase 3,
and `totalCredit_trace_mono` permits the last transition to enter Phase 4. -/
theorem receipt_credit_at_first_exit
    {init : InputCfg n} {ω : InputLog n}
    {S T ρ u ell k : ℕ} {w : ClockTimes init}
    {σ : Sign} {q : ℚ}
    (H : ClockHistory init ω S T ρ w)
    (hTu : T ≤ u) (huρ : u ≤ ρ)
    (hcredit : q ≤ totalCredit σ ell k (trace init ω u)) :
    q ≤ totalCredit σ ell k (trace init ω ρ) := by
  have hmono := totalCredit_trace_mono σ ell k init ω huρ
    (by
      intro v huv hvρ a ha
      exact Or.inl (H.all_three v (hTu.trans huv) hvρ a ha))
  exact hcredit.trans hmono

/-- The mixed two-level barrier already proves the retained `.9695` credit.
This is `near_two_levels_at_initialized_checkpoint` with the final lossy
`two_level_band_of_mixed_credit` conversion removed. -/
theorem receipt_near_credit_at_initialized_checkpoint
    {init : InputCfg n} (hvalid : validInitial init) {ω : InputLog n}
    {S T ρ s u M ell : ℕ} {w : ClockTimes init} {σ : Sign}
    (H : ClockHistory init ω S T ρ w)
    (hseed : SafeSparseSeed init ω S)
    (hn : timePopulationThreshold ≤ n)
    (hM : timeMainCount (trace init ω S) = M)
    (hell : 0 < ell)
    (hSs : S ≤ s) (hsu : s ≤ u)
    (hTu : T ≤ u) (huρ : u < ρ)
    (hbarrier :
      twoLevelBarrier M
          (mixedShallowPositiveNat σ ell (trace init ω s))
          (debtY σ (ell + 1) (trace init ω s)) ≤
        twoLevelTarget M)
    (hexception :
      (exceptionCount (ell + 1) (trace init ω s) : ℚ) ≤
        (3 / 1250 : ℚ) * M)
    (hphi :
      augmentedPhi ell (trace init ω s) ≤
        (1 / 1000 : ℚ) * M) :
    10000 * scaledShallowPositive σ ell (trace init ω u) ≤
        111 * (M : ℚ) ∨
      (1939 / 2000 : ℚ) * (M : ℚ) ≤
        totalCredit σ ell (ell + 1) (trace init ω u) := by
  classical
  have hSρ : S < ρ := lt_of_le_of_lt (hSs.trans hsu) huρ
  have hmain : 12 * n ≤ 25 * M := by
    simpa only [hM] using (H.density S le_rfl hSρ).1
  have hMlarge := main_count_large_for_two_level_rounding hn hmain
  have hrange :
      ∀ v, s ≤ v → v ≤ u →
        ∀ a ∈ trace init ω v,
          1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
    intro v hsv hvu
    exact H.phase_range v (hSs.trans hsv) (lt_of_le_of_lt hvu huρ)
  have hsafe :
      ∀ v, s ≤ v → v ≤ u →
        ∀ a ∈ trace init ω v,
          a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    intro v hsv hvu
    exact
      (mixed_window_safety hvalid H hseed
        (hSs.trans hsv) (lt_of_le_of_lt hvu huρ)).1
  have hcarrier :
      ∀ v, s ≤ v → v ≤ u →
        ∀ a ∈ trace init ω v,
          a.role ≠ .main → a.smallBias.val = 3 := by
    intro v hsv hvu
    exact
      (mixed_window_safety hvalid H hseed
        (hSs.trans hsv) (lt_of_le_of_lt hvu huρ)).2
  have hphase : ∀ a ∈ trace init ω u, 3 ≤ a.phase.val :=
    fun a ha => (H.all_three u hTu huρ a ha).ge
  rcases
      mixed_two_level_alternative_of_barrier
        σ ell M (trace init ω s)
        hMlarge (hsafe s le_rfl hsu) hbarrier with hX | hY
  · left
    have hmono :=
      mixedShallowPositive_trace_le σ ell init ω s u hsu
        hrange hsafe hcarrier
    rw [mixedShallowPositive_eq_scaledShallowPositive
      σ ell (trace init ω u) hphase] at hmono
    linarith only [hX, hmono]
  · right
    have hcount :
        RoleSplitConcentration.mainCount (trace init ω s) = M := by
      simpa only [RoleSplitConcentration.mainCount, timeMainCount,
        AveragingEventInterface.countP_classical] using
          (H.main_count s hSs (lt_of_le_of_lt hsu huρ)).trans hM
    have hcredit :=
      initial_mixed_two_level_credit σ ell M (trace init ω s)
        hcount hY hexception hphi
    have hmono :=
      mixedTotalCredit_trace_mono σ ell (ell + 1) hell
        init ω s u hsu hrange hsafe hcarrier
    have hcreditU :
        (1939 / 2000 : ℚ) * (M : ℚ) ≤
          mixedTotalCredit σ ell (ell + 1) (trace init ω u) :=
      hcredit.trans hmono
    simpa only [
      AveragingPendingCredit.mixedTotalCredit_eq_totalCredit
        σ ell (ell + 1) (trace init ω u) hphase] using hcreditU

/-- The retained near-level alternative at the genuine first Phase-4 seed.
The shallow branch uses exact role/bias transport; the credit branch uses
monotonicity through the final interaction. -/
theorem receipt_near_credit_at_first_exit
    {init : InputCfg n} (hvalid : validInitial init) {ω : InputLog n}
    {S T ρ s M ell : ℕ} {w : ClockTimes init} {σ : Sign}
    (H : ClockHistory init ω S T ρ w)
    (hseed : SafeSparseSeed init ω S)
    (hn : timePopulationThreshold ≤ n)
    (hM : timeMainCount (trace init ω S) = M)
    (hell : 0 < ell)
    (hSs : S ≤ s) (hsρ : s < ρ)
    (hbarrier :
      twoLevelBarrier M
          (mixedShallowPositiveNat σ ell (trace init ω s))
          (debtY σ (ell + 1) (trace init ω s)) ≤
        twoLevelTarget M)
    (hexception :
      (exceptionCount (ell + 1) (trace init ω s) : ℚ) ≤
        (3 / 1250 : ℚ) * M)
    (hphi :
      augmentedPhi ell (trace init ω s) ≤
        (1 / 1000 : ℚ) * M) :
    10000 * scaledShallowPositive σ ell (trace init ω ρ) ≤
        111 * (M : ℚ) ∨
      (1939 / 2000 : ℚ) * (M : ℚ) ≤
        totalCredit σ ell (ell + 1) (trace init ω ρ) := by
  have hST := AveragingEventInterface.clockHistory_seed_lt_exit H
  have hpre : ρ - 1 < ρ := by omega
  have hTpre : T ≤ ρ - 1 := by omega
  have hsPre : s ≤ ρ - 1 := by omega
  have hnear :=
    receipt_near_credit_at_initialized_checkpoint
      hvalid H hseed hn hM hell hSs hsPre hTpre hpre
      hbarrier hexception hphi
  rcases hnear with hshallow | hcredit
  · left
    rw [scaledShallowPositive_first_exit_step σ ell H]
    exact hshallow
  · right
    exact receipt_credit_at_first_exit H hTpre (by omega) hcredit

/-- The complete N18 receipt at the genuine first Phase-4 seed.

The hypotheses `hcredit`, `hbarrier`, `hexception`, `hphi`, and `hold` are the
checkpoint outputs selected by the later global induction.  No raw-band premise
is used. -/
theorem lateSamplingSeedReceipt_of_checkpoint_data
    {init : InputCfg n} (hvalid : validInitial init) {ω : InputLog n}
    {S T ρ s u M ell : ℕ} {w : ClockTimes init} {σ : Sign}
    (H : ClockHistory init ω S T ρ w)
    (hseed : SafeSparseSeed init ω S)
    (hn : timePopulationThreshold ≤ n)
    (hTu : T ≤ u) (huρ : u < ρ)
    (hM : timeMainCount (trace init ω S) = M)
    (hwinning : winningSign init σ)
    (hnonzero : 0 < gapMagnitude init)
    (hgap : 40 * gapMagnitude init < M)
    (hell : 5 ≤ ell)
    (hellcap : ell + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hscale : 2 * M ≤ 5 * 2 ^ ell * gapMagnitude init)
    (hscaleUpper : 5 * 2 ^ ell * gapMagnitude init < 4 * M)
    (hcredit :
      (601 / 625 : ℚ) * (M : ℚ) ≤
        totalCredit σ ell (ell + 2) (trace init ω u))
    (hminority :
      250 * (2 : ℚ) ^ ell *
          AveragingLiveProduct.sideMass
            (oppositeSign σ) (trace init ω u) ≤
        M)
    (hpotential :
      (1000 : ℚ) *
          AveragingMixedLedgers.augmentedPhi ell (trace init ω u) ≤
        M)
    (hSs : S ≤ s) (hsρ : s < ρ)
    (hbarrier :
      twoLevelBarrier M
          (mixedShallowPositiveNat σ ell (trace init ω s))
          (debtY σ (ell + 1) (trace init ω s)) ≤
        twoLevelTarget M)
    (hexception :
      (exceptionCount (ell + 1) (trace init ω s) : ℚ) ≤
        (3 / 1250 : ℚ) * M)
    (hphi :
      augmentedPhi ell (trace init ω s) ≤
        (1 / 1000 : ℚ) * M)
    (hold :
      augmentedPhiNat (ell - terminalCutoff n)
        (trace init ω u) = 0) :
    LateSamplingSeedReceipt init M ell σ (trace init ω ρ) := by
  have hsmall : SmallReadout init M ell σ (trace init ω ρ) :=
    smallReadout_at_first_exit_of_checkpoint
      hvalid H hTu huρ hM hwinning hnonzero hgap
      hell hellcap hscale hscaleUpper
      hcredit hminority hpotential
  have hprotected :
      (601 / 625 : ℚ) * (M : ℚ) ≤
        totalCredit σ ell (ell + 2) (trace init ω ρ) :=
    receipt_credit_at_first_exit H hTu huρ.le hcredit
  have hnear :
      10000 * scaledShallowPositive σ ell (trace init ω ρ) ≤
          111 * (M : ℚ) ∨
        (1939 / 2000 : ℚ) * (M : ℚ) ≤
          totalCredit σ ell (ell + 1) (trace init ω ρ) :=
    receipt_near_credit_at_first_exit
      hvalid H hseed hn hM (by omega) hSs hsρ
      hbarrier hexception hphi
  have holdCutoff :
      noIndexBelow (ell - terminalCutoff n) (trace init ω ρ) :=
    oldIndexCutoff_at_first_exit_of_checkpoint
      hvalid H hTu huρ hold
  refine
    { toSmallReadout := hsmall
      main_count := (mainCount_at_first_exit H).trans hM
      protected_credit := hprotected
      near_credit := hnear
      old_index_cutoff := holdCutoff }

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end

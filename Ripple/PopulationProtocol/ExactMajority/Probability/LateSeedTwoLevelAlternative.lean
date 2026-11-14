-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedTwoLevelAlternative.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedTwoLevelArithmetic
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedMixedPositive
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedSparseEntry
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingPendingCreditTransitions

/-!
# The two-level alternative on the actual mixed trace

A successfully tested integer barrier at a mixed checkpoint gives either a
small pending-aware majority mass or a small changing-zero debt. The first
quantity decreases through pending activation. The second branch produces
protected credit, which increases through pending activation. At an initialized
checkpoint these are the literal readout mass and the actual two-level band.
The last Phase-4 seed interaction is transported separately.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem StageEventSpec
open AveragingSparseEntry AveragingPendingCredit AveragingPendingCreditTransitions
open AveragingCreditCount AveragingMixedLedgers AveragingTerminalDebt
open AveragingCheckpointReadout

variable {L K n : ℕ}

/-- A genuine safe sparse seed supplies safety of pending agents as well as
initialized ones. Carrier safety uses reachability and the actual role range. -/
theorem mixed_window_safety
    {init : InputCfg n} (hvalid : validInitial init) {ω : InputLog n}
    {S T ρ v : ℕ} {w : ClockTimes init}
    (H : ClockHistory init ω S T ρ w) (hseed : SafeSparseSeed init ω S)
    (hSv : S ≤ v) (hvρ : v < ρ) :
    (∀ a ∈ trace init ω v,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) ∧
    (∀ a ∈ trace init ω v, a.role ≠ .main → a.smallBias.val = 3) := by
  have hsafe := safeSparseSeed_small_safe_future init ω S v hseed hSv
  have hreach :
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init ω v) := by
    simpa only [TimeTheorem.trace_zero] using
      TimeTheorem.trace_reachable init ω (s := 0) (t := v) (Nat.zero_le v)
  constructor
  · intro a ha
    have hs : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4 := hsafe a ha
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro a ha hm
    have hroles := PhaseTwoActivation.trace_final_roles_of_range init hvalid ω v
      (H.phase_range v hSv hvρ)
    have hz := reachable_nonMain_smallBias_zero init (trace init ω v) hvalid hreach
    rcases hroles a ha with hmain | hc | hr
    · exact (hm hmain).elim
    · exact hz a ha (Or.inr hc)
    · exact hz a ha (Or.inl hr)

/-- Both ceiling losses are paid before interpreting the mixed integer X. -/
theorem mixed_two_level_alternative_of_barrier
    (σ : Sign) (ell M : ℕ) (c : Cfg L K)
    (hM : 30000 ≤ M)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hbarrier :
      twoLevelBarrier M (mixedShallowPositiveNat σ ell c)
        (debtY σ (ell + 1) c) ≤ twoLevelTarget M) :
    mixedShallowPositive σ ell c ≤ (111 / 10000 : ℚ) * M ∨
      debtY σ (ell + 1) c ≤ (271 / 10000 : ℚ) * M := by
  have h := two_level_alternative M (mixedShallowPositiveNat σ ell c)
    (debtY σ (ell + 1) c) hM hbarrier
  simpa only [mixedShallowPositive_eq_nat σ ell c hsafe] using h

/-- The mixed checkpoint need not be fully activated. Its mass/debt alternative
is transported to any later initialized checkpoint before the actual exit. -/
theorem near_two_levels_at_initialized_checkpoint
    {init : InputCfg n} (hvalid : validInitial init) {ω : InputLog n}
    {S T ρ s u M ell : ℕ} {w : ClockTimes init} {σ : Sign}
    (H : ClockHistory init ω S T ρ w) (hseed : SafeSparseSeed init ω S)
    (hn : timePopulationThreshold ≤ n) (hM : timeMainCount (trace init ω S) = M)
    (hell : 0 < ell) (hSs : S ≤ s) (hsu : s ≤ u)
    (hTu : T ≤ u) (huρ : u < ρ)
    (hbarrier :
      twoLevelBarrier M (mixedShallowPositiveNat σ ell (trace init ω s))
        (debtY σ (ell + 1) (trace init ω s)) ≤ twoLevelTarget M)
    (hexception : (exceptionCount (ell + 1) (trace init ω s) : ℚ) ≤
      (3 / 1250 : ℚ) * M)
    (hphi : augmentedPhi ell (trace init ω s) ≤ (1 / 1000 : ℚ) * M) :
    10000 * scaledShallowPositive σ ell (trace init ω u) ≤ 111 * (M : ℚ) ∨
      939 * M ≤ 1000 * bandCount σ ell 1 (trace init ω u) := by
  classical
  have hSρ : S < ρ := lt_of_le_of_lt (hSs.trans hsu) huρ
  have hmain : 12 * n ≤ 25 * M := by
    simpa only [hM] using (H.density S le_rfl hSρ).1
  have hMlarge := main_count_large_for_two_level_rounding hn hmain
  have hrange : ∀ v, s ≤ v → v ≤ u → ∀ a ∈ trace init ω v,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
    intro v hsv hvu
    exact H.phase_range v (hSs.trans hsv) (lt_of_le_of_lt hvu huρ)
  have hsafe : ∀ v, s ≤ v → v ≤ u → ∀ a ∈ trace init ω v,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    intro v hsv hvu
    exact (mixed_window_safety hvalid H hseed
      (hSs.trans hsv) (lt_of_le_of_lt hvu huρ)).1
  have hcarrier : ∀ v, s ≤ v → v ≤ u → ∀ a ∈ trace init ω v,
      a.role ≠ .main → a.smallBias.val = 3 := by
    intro v hsv hvu
    exact (mixed_window_safety hvalid H hseed
      (hSs.trans hsv) (lt_of_le_of_lt hvu huρ)).2
  have hphase : ∀ a ∈ trace init ω u, 3 ≤ a.phase.val :=
    fun a ha => (H.all_three u hTu huρ a ha).ge
  rcases mixed_two_level_alternative_of_barrier σ ell M (trace init ω s)
      hMlarge (hsafe s le_rfl hsu) hbarrier with hX | hY
  · left
    have hmono := mixedShallowPositive_trace_le σ ell init ω s u hsu
      hrange hsafe hcarrier
    rw [mixedShallowPositive_eq_scaledShallowPositive σ ell
      (trace init ω u) hphase] at hmono
    linarith only [hX, hmono]
  · right
    have hcount : RoleSplitConcentration.mainCount (trace init ω s) = M := by
      simpa only [RoleSplitConcentration.mainCount, timeMainCount, AveragingEventInterface.countP_classical]
        using (H.main_count s hSs (lt_of_le_of_lt hsu huρ)).trans hM
    have hcredit := initial_mixed_two_level_credit σ ell M (trace init ω s)
      hcount hY hexception hphi
    have hmono := mixedTotalCredit_trace_mono σ ell (ell + 1) hell
      init ω s u hsu hrange hsafe hcarrier
    exact two_level_band_of_mixed_credit σ ell M (trace init ω u)
      ((H.main_count u (hSs.trans hsu) huρ).trans hM) hphase
      (hcredit.trans hmono)

/-- The literal near-two-level field holds at the first Phase-4 seed.
No mixed-window hypothesis is extended across the final interaction. -/
theorem near_two_levels_at_first_exit_of_mixed_barrier
    {init : InputCfg n} (hvalid : validInitial init) {ω : InputLog n}
    {S T ρ s M ell : ℕ} {w : ClockTimes init} {σ : Sign}
    (H : ClockHistory init ω S T ρ w) (hseed : SafeSparseSeed init ω S)
    (hn : timePopulationThreshold ≤ n) (hM : timeMainCount (trace init ω S) = M)
    (hell : 0 < ell) (hSs : S ≤ s) (hsρ : s < ρ)
    (hbarrier :
      twoLevelBarrier M (mixedShallowPositiveNat σ ell (trace init ω s))
        (debtY σ (ell + 1) (trace init ω s)) ≤ twoLevelTarget M)
    (hexception : (exceptionCount (ell + 1) (trace init ω s) : ℚ) ≤
      (3 / 1250 : ℚ) * M)
    (hphi : augmentedPhi ell (trace init ω s) ≤ (1 / 1000 : ℚ) * M) :
    10000 * scaledShallowPositive σ ell (trace init ω ρ) ≤ 111 * (M : ℚ) ∨
      939 * M ≤ 1000 * bandCount σ ell 1 (trace init ω ρ) := by
  have hST := AveragingEventInterface.clockHistory_seed_lt_exit H
  have hpre : ρ - 1 < ρ := by omega
  have hTpre : T ≤ ρ - 1 := by omega
  have hsPre : s ≤ ρ - 1 := by omega
  have hnear := near_two_levels_at_initialized_checkpoint hvalid H hseed hn hM
    hell hSs hsPre hTpre hpre hbarrier hexception hphi
  rw [scaledShallowPositive_first_exit_step σ ell H,
    AveragingFirstExit.bandCount_first_exit_step σ ell 1 H]
  exact hnear

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end

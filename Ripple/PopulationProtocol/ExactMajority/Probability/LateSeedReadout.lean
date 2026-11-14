-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedReadout.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCheckpointReadout
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingAtomBound
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCreditCount

/-!
# The literal late-strengthening readout and deterministic N13 bridges

These are the exact N16 observables proposed in DOTY-LEAN-PLAN. The existing
SmallReadout is extended without changing any field. The results below transport
actual role/bias observables through the first Phase-4 interaction, convert
protected credits into the two required bands, and convert extinction of the
compiled integer potential into the old-index cutoff.

No probability estimate is asserted in this file. In particular, the near-two-level
alternative is not asserted to follow deterministically from bare SmallReadout.
-/

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem StageEventSpec
open AveragingCreditTransitions AveragingTerminalReadout AveragingFirstExit
open AveragingIntegerPotential AveragingCheckpointReadout

variable {L K n : ℕ}

/-- N16's majority mass at indices at most ell, scaled by 2^ell.
At the first Phase-4 seed every agent has already initialized Phase 3. -/
noncomputable def scaledShallowPositive
    (σ : Sign) (ell : ℕ) (c : InputCfg n) : ℚ := by
  classical
  exact (2 : ℚ) ^ ell *
    (c.map (fun a =>
      if a.role = .main then
        match a.bias with
        | .zero => 0
        | .dyadic σ' j =>
            if σ' = σ ∧ j.val ≤ ell then
              (2 : ℚ) ^ (-(j.val : ℤ))
            else 0
      else 0)).sum

/-- No nonzero Main has an index strictly below the specified cutoff. -/
def noIndexBelow (ell : ℕ) (c : InputCfg n) : Prop :=
  ∀ a ∈ c, a.role = .main →
    ∀ σ j, a.bias = Bias.dyadic σ j → ell ≤ j.val

noncomputable def terminalCutoff (n : ℕ) : ℕ :=
  Nat.floor (Real.log (n : ℝ) / 25)

/-- The exact N16 extension of the compiled N10 readout. -/
structure LateSeedReadout
    (init : InputCfg n) (M ell : ℕ) (σ : Sign)
    (c : InputCfg n) : Prop extends SmallReadout init M ell σ c where
  protectedBand : 9232 * M ≤ 10000 * bandCount σ ell 2 c
  nearTwoLevels :
    10000 * scaledShallowPositive σ ell c ≤ 111 * (M : ℚ) ∨
      939 * M ≤ 1000 * bandCount σ ell 1 c
  oldIndexCutoff : noIndexBelow (ell - terminalCutoff n) c

/-- The new cutoff predicate is exactly the existing integer extinction test. -/
theorem noIndexBelow_iff_shallowPotential_eq_zero (ell : ℕ) (c : InputCfg n) :
    noIndexBelow ell c ↔ shallowPotential ell c = 0 :=
  (AveragingTieReadout.shallowPotential_eq_zero_iff ell c).symm

theorem noIndexBelow_zero (c : InputCfg n) : noIndexBelow 0 c := by
  intro a ha hm σ j hb
  omega

theorem noIndexBelow_mono {r s : ℕ} (hrs : r ≤ s) {c : InputCfg n}
    (h : noIndexBelow s c) : noIndexBelow r c := by
  intro a ha hm σ j hb
  exact hrs.trans (h a ha hm σ j hb)

/-- The truncated subtraction in the plan makes the early-cutoff case automatic. -/
theorem oldIndexCutoff_of_level_le (ell : ℕ) (c : InputCfg n)
    (hell : ell ≤ terminalCutoff n) :
    noIndexBelow (ell - terminalCutoff n) c := by
  simpa only [Nat.sub_eq_zero_of_le hell] using noIndexBelow_zero c

/-- The compiled augmented potential removes every initialized old Main atom.
No assumption about non-Main bias fields is needed for this implication. -/
theorem noIndexBelow_of_augmentedPhiNat_eq_zero (r : ℕ) (c : InputCfg n)
    (hphase : ∀ a ∈ c, a.role = .main → 3 ≤ a.phase.val)
    (hzero : augmentedPhiNat r c = 0) :
    noIndexBelow r c := by
  intro a ha hm σ j hb
  have hz := AveragingAtomBound.old_agent_atom_zero r c hzero a ha
  have hp : ¬ a.phase.val < 3 := by
    have := hphase a ha hm
    omega
  by_contra hindex
  have hj : j.val < r := by omega
  have hzpow : (4 : ℕ) ^ (r - 1 - j.val) = 0 := by
    simpa only [augmentedAgentPhiNat, if_neg hp, activeAgentPhiNat, hb,
      if_pos hj] using hz
  have hpositive : 0 < (4 : ℕ) ^ (r - 1 - j.val) := by positivity
  omega

/-- Exact role/bias transport supplies the observable at the actual exit,
rather than extending a strict-before-exit window across its last interaction. -/
theorem scaledShallowPositive_first_exit_step
    {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (σ : Sign) (ell : ℕ)
    (h : ClockHistory init ω S T ρ w) :
    scaledShallowPositive σ ell (trace init ω ρ) =
      scaledShallowPositive σ ell (trace init ω (ρ - 1)) := by
  classical
  have hsum := sum_roleBias_at_first_exit
    (fun r b => if r = Role.main then
      match b with
      | .zero => (0 : ℚ)
      | .dyadic τ j =>
          if τ = σ ∧ j.val ≤ ell then (2 : ℚ) ^ (-(j.val : ℤ)) else 0
    else 0) h
  simpa only [scaledShallowPositive, Config.sumOf] using
    congrArg (fun x : ℚ => (2 : ℚ) ^ ell * x) hsum

theorem noIndexBelow_first_exit
    {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (r : ℕ)
    (h : ClockHistory init ω S T ρ w)
    (hpre : noIndexBelow r (trace init ω (ρ - 1))) :
    noIndexBelow r (trace init ω ρ) := by
  exact roleBias_property_at_first_exit
    (fun role bias => role = Role.main →
      ∀ σ j, bias = Bias.dyadic σ j → r ≤ j.val) h hpre

/-- All three additional N16 clauses survive the exact first Phase-4 interaction. -/
theorem lateSeedReadout_first_exit
    {init : InputCfg n} {ω : InputLog n}
    {S T ρ M ell : ℕ} {w : ClockTimes init} {σ : Sign}
    (h : ClockHistory init ω S T ρ w)
    (hpre : LateSeedReadout init M ell σ (trace init ω (ρ - 1))) :
    LateSeedReadout init M ell σ (trace init ω ρ) := by
  refine
    { toSmallReadout := smallReadout_first_exit h hpre.toSmallReadout
      protectedBand := ?_
      nearTwoLevels := ?_
      oldIndexCutoff := noIndexBelow_first_exit _ h hpre.oldIndexCutoff }
  · rw [bandCount_first_exit_step σ ell 2 h]
    exact hpre.protectedBand
  · rw [scaledShallowPositive_first_exit_step σ ell h,
      bandCount_first_exit_step σ ell 1 h]
    exact hpre.nearTwoLevels

/-- The changing-zero debt .0271, exceptions .0024, and shallow potential .001
give the required .9695 credit. This is the generic compiled mixed ledger at
k = ell + 1, including pending agents. -/
theorem initial_mixed_two_level_credit
    (σ : Sign) (ell M : ℕ) (c : Cfg L K)
    (hM : RoleSplitConcentration.mainCount c = M)
    (hY : AveragingTerminalDebt.debtY σ (ell + 1) c ≤ (271 / 10000 : ℚ) * M)
    (hexception : (AveragingCreditCount.exceptionCount (ell + 1) c : ℚ) ≤
      (3 / 1250 : ℚ) * M)
    (hphi : AveragingMixedLedgers.augmentedPhi ell c ≤ (1 / 1000 : ℚ) * M) :
    (1939 / 2000 : ℚ) * M ≤
      AveragingPendingCredit.mixedTotalCredit σ ell (ell + 1) c := by
  have hd := AveragingCreditCount.credit_count_decomposition σ ell (ell + 1) c
  have hs := AveragingCreditCount.shallowMajorityCount_le_phi σ ell c
  rw [hM] at hd
  linarith

/-- Lemma 4's .9695 protected two-level credit gives the literal .939 band.
This uses the existing capacity estimate on the actual configuration. -/
theorem two_level_band_of_credit (σ : Sign) (ell M : ℕ) (c : InputCfg n)
    (hcount : timeMainCount c = M)
    (hcredit : (1939 / 2000 : ℚ) * (M : ℚ) ≤
      totalCredit σ ell (ell + 1) c) :
    939 * M ≤ 1000 * bandCount σ ell 1 c := by
  have hcap := totalCredit_capacity σ ell 1 c
  rw [hcount] at hcap
  have hq : (939 : ℚ) * (M : ℚ) ≤
      1000 * (bandCount σ ell 1 c : ℚ) := by linarith
  exact_mod_cast hq

/-- Once all agents have initialized, the mixed credit is exactly the existing
credit of the configuration. Thus no pending-mass term is dropped at readout. -/
theorem two_level_band_of_mixed_credit (σ : Sign) (ell M : ℕ) (c : InputCfg n)
    (hcount : timeMainCount c = M)
    (hphase : ∀ a ∈ c, 3 ≤ a.phase.val)
    (hcredit : (1939 / 2000 : ℚ) * (M : ℚ) ≤
      AveragingPendingCredit.mixedTotalCredit σ ell (ell + 1) c) :
    939 * M ≤ 1000 * bandCount σ ell 1 c := by
  apply two_level_band_of_credit σ ell M c hcount
  simpa only [AveragingPendingCredit.mixedTotalCredit_eq_totalCredit
    σ ell (ell + 1) c hphase] using hcredit

/-- A produced two-level credit persists to the first seed on the actual trace. -/
theorem two_level_band_at_first_exit
    {init : InputCfg n} {ω : InputLog n}
    {S T ρ u ell : ℕ} {w : ClockTimes init} (σ : Sign)
    (h : ClockHistory init ω S T ρ w) (hTu : T ≤ u) (huρ : u ≤ ρ)
    (hcredit : (1939 / 2000 : ℚ) * (timeMainCount (trace init ω S) : ℚ) ≤
      totalCredit σ ell (ell + 1) (trace init ω u)) :
    939 * timeMainCount (trace init ω S) ≤
      1000 * bandCount σ ell 1 (trace init ω ρ) := by
  have hmono := totalCredit_trace_mono σ ell (ell + 1) init ω huρ
    (by
      intro v huv hvρ a ha
      exact Or.inl (h.all_three v (by omega) hvρ a ha))
  exact two_level_band_of_credit σ ell _ _ (mainCount_at_first_exit h)
    (hcredit.trans hmono)

/-- An extinct old potential at an initialized checkpoint remains extinct up
to the last Phase-3 snapshot, then the exact exit transport gives the cutoff. -/
theorem oldIndexCutoff_at_first_exit_of_checkpoint
    {init : InputCfg n} (hvalid : validInitial init) {ω : InputLog n}
    {S T ρ u ell : ℕ} {w : ClockTimes init}
    (h : ClockHistory init ω S T ρ w) (hTu : T ≤ u) (huρ : u < ρ)
    (hzero : augmentedPhiNat (ell - terminalCutoff n) (trace init ω u) = 0) :
    noIndexBelow (ell - terminalCutoff n) (trace init ω ρ) := by
  by_cases hell : ell ≤ terminalCutoff n
  · exact oldIndexCutoff_of_level_le ell _ hell
  · have hr : 1 ≤ ell - terminalCutoff n := by omega
    have huPre : u ≤ ρ - 1 := by omega
    have hpre : ρ - 1 < ρ := by omega
    have hmono := trace_augmentedPhiNat_le (ell - terminalCutoff n) hr
      init ω u (ρ - 1) huPre
      (by
        intro v huv hvPre
        exact h.phase_range v (h.entry.order.trans (hTu.trans huv)) (by omega))
      (by
        intro v huv hvPre
        exact (postActivationSafety hvalid h (hTu.trans huv) (by omega)).1)
      (by
        intro v huv hvPre
        exact (postActivationSafety hvalid h (hTu.trans huv) (by omega)).2)
    have hzPre :
        augmentedPhiNat (ell - terminalCutoff n) (trace init ω (ρ - 1)) = 0 := by
      rw [hzero] at hmono
      omega
    apply noIndexBelow_first_exit _ h
    apply noIndexBelow_of_augmentedPhiNat_eq_zero _ _ _ hzPre
    intro a ha hm
    exact (h.all_three (ρ - 1) (hTu.trans huPre) hpre a ha).ge

/-- In the strict nonzero small-gap branch, the reviewed successful history
really supplies N10's SmallReadout; the tie and strong alternatives are excluded. -/
theorem smallReadout_of_successfulHistory
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ}
    (h : successfulHistory (reviewedStageEvents n init) ω S T ρ)
    (hnonzero : 0 < gapMagnitude init)
    (hgap : 40 * gapMagnitude init < timeMainCount (trace init ω S)) :
    ∃ ell σ, SmallReadout init (timeMainCount (trace init ω S))
      ell σ (trace init ω ρ) := by
  have havg := h.2.2.2
  change averageReadout init (timeMainCount (trace init ω S))
    (trace init ω ρ) at havg
  rcases havg with htie | hsmall | hstrong
  · have hz : gapMagnitude init = 0 := by
      simp only [gapMagnitude, htie.1, Int.natAbs_zero]
    omega
  · exact hsmall
  · have hlarge := hstrong.lowerGap
    omega

/-- N13's actual checkpoint producer plus an independently supplied pre-exit
two-level alternative and old-potential extinction yields the exact N16 readout.
The stochastic production of those extra premises is a separate obligation. -/
theorem lateSeedReadout_at_first_exit_of_checkpoint
    {init : InputCfg n} (hvalid : validInitial init) {ω : InputLog n}
    {S T ρ u M ell : ℕ} {w : ClockTimes init} {σ : Sign}
    (h : ClockHistory init ω S T ρ w)
    (hTu : T ≤ u) (huρ : u < ρ)
    (hM : timeMainCount (trace init ω S) = M)
    (hwinning : winningSign init σ)
    (hnonzero : 0 < gapMagnitude init)
    (hgap : 40 * gapMagnitude init < M)
    (hell : 5 ≤ ell) (hellcap : ell + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hscale : 2 * M ≤ 5 * 2 ^ ell * gapMagnitude init)
    (hscaleUpper : 5 * 2 ^ ell * gapMagnitude init < 4 * M)
    (hcredit : (601 / 625 : ℚ) * M ≤
      totalCredit σ ell (ell + 2) (trace init ω u))
    (hminority : 250 * (2 : ℚ) ^ ell *
      AveragingLiveProduct.sideMass (oppositeSign σ) (trace init ω u) ≤ M)
    (hpotential : (1000 : ℚ) *
      AveragingMixedLedgers.augmentedPhi ell (trace init ω u) ≤ M)
    (hnear :
      10000 * scaledShallowPositive σ ell (trace init ω (ρ - 1)) ≤ 111 * (M : ℚ) ∨
        939 * M ≤ 1000 * bandCount σ ell 1 (trace init ω (ρ - 1)))
    (hold : augmentedPhiNat (ell - terminalCutoff n) (trace init ω u) = 0) :
    LateSeedReadout init M ell σ (trace init ω ρ) := by
  have hsmall := smallReadout_at_first_exit_of_checkpoint hvalid h hTu huρ hM
    hwinning hnonzero hgap hell hellcap hscale hscaleUpper
    hcredit hminority hpotential
  have hband := protected_band_at_first_exit σ h hTu huρ.le
    (by simpa only [hM] using hcredit)
  refine
    { toSmallReadout := hsmall
      protectedBand := by simpa only [hM] using hband
      nearTwoLevels := ?_
      oldIndexCutoff :=
        oldIndexCutoff_at_first_exit_of_checkpoint hvalid h hTu huρ hold }
  rw [scaledShallowPositive_first_exit_step σ ell h,
    bandCount_first_exit_step σ ell 1 h]
  exact hnear

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

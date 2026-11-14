-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingCheckpointReadout.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCancellationLedger
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingIntegerPotential
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTieReadout
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoActivation

/-!
# Small-gap readout from an actual terminal checkpoint

The inputs are the produced credit, minority mass and augmented-potential
bounds at a checkpoint after activation. Reachability supplies the safety
premises of the compiled mixed-trace monotonicity lemmas. The last interaction
is handled by AveragingFirstExit, rather than extending a strict clock-history
window through its endpoint.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingCheckpointReadout

open TimeTheorem StageEventSpec P3DeterministicAlgebra
open AveragingMixedAlgebra AveragingMixedLedgers AveragingIntegerPotential
open AveragingMixedPotentialTransitions AveragingLiveProduct
open AveragingCancellationLedger AveragingCreditTransitions AveragingTerminalReadout
open AveragingFirstExit AveragingTieReadout

variable {n : ℕ}

theorem postActivationSafety
    {init : InputCfg n} (hvalid : validInitial init) {ω : InputLog n}
    {S T ρ v : ℕ} {w : ClockTimes init}
    (h : ClockHistory init ω S T ρ w) (hTv : T ≤ v) (hvρ : v < ρ) :
    (∀ a ∈ trace init ω v,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) ∧
    (∀ a ∈ trace init ω v,
      a.role ≠ .main → a.smallBias.val = 3) := by
  have hSv : S ≤ v := h.entry.order.trans hTv
  have hthree := h.all_three v hTv hvρ
  have hreach :
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init ω v) := by
    simpa only [TimeTheorem.trace_zero] using
      TimeTheorem.trace_reachable init ω (s := 0) (t := v) (Nat.zero_le v)
  have hcap : ∀ a ∈ trace init ω v, a.phase.val ≤ 4 := by
    intro a ha
    rw [hthree a ha]
    decide
  constructor
  · intro a ha
    exact reachable_phase_ge2_smallBias_noerror_of_phases_le_four
      init (trace init ω v) hvalid hreach hcap a ha
      (by rw [hthree a ha]; decide)
  · intro a ha hm
    have hroles := PhaseTwoActivation.trace_final_roles_of_range init hvalid ω v
      (h.phase_range v hSv hvρ)
    have hz := reachable_nonMain_smallBias_zero init (trace init ω v) hvalid hreach
    rcases hroles a ha with hmain | hc | hr
    · exact (hm hmain).elim
    · exact hz a ha (Or.inr hc)
    · exact hz a ha (Or.inl hr)

theorem sideMass_eq_signMass (σ : Sign) (c : InputCfg n)
    (hphase : ∀ a ∈ c, 3 ≤ a.phase.val)
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.bias = .zero) :
    sideMass σ c = signMass σ c := by
  classical
  revert hphase hcarrier
  induction c using Multiset.induction_on with
  | empty => intro _ _; simp [sideMass, signMass]
  | cons a c ih =>
      intro hphase hcarrier
      have ha : a ∈ a ::ₘ c := Multiset.mem_cons_self _ _
      have hnot : ¬ a.phase.val < 3 := by have := hphase a ha; omega
      have ht := ih
        (fun b hb => hphase b (Multiset.mem_cons_of_mem hb))
        (fun b hb => hcarrier b (Multiset.mem_cons_of_mem hb))
      simp only [sideMass, signMass, Multiset.map_cons, Multiset.sum_cons] at ht ⊢
      rw [ht]
      congr 1
      by_cases hm : a.role = .main
      · rw [if_pos hm]
        cases hb : a.bias with
        | zero => cases σ <;> simp [sideAtom, prePhase4Mass, hnot, hb, Bias.toRat]
        | dyadic τ j =>
            have hw : (0 : ℚ) ≤ ((2 : ℚ) ^ j.val)⁻¹ := by positivity
            cases σ <;> cases τ <;>
              simp [sideAtom, prePhase4Mass, hnot, hb, Bias.toRat,
                zpow_neg, zpow_natCast, one_div, neg_div,
                max_eq_left hw, max_eq_right (neg_nonpos.mpr hw)]
      · rw [if_neg hm]
        have hb := hcarrier a ha hm
        cases σ <;> simp [sideAtom, prePhase4Mass, hnot, hb, Bias.toRat]

theorem mixedShallowMass_eq_shallowMass (ell : ℕ) (c : InputCfg n)
    (hphase : ∀ a ∈ c, 3 ≤ a.phase.val)
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.bias = .zero) :
    mixedShallowMass ell c = shallowMass ell c := by
  classical
  revert hphase hcarrier
  induction c using Multiset.induction_on with
  | empty => intro _ _; simp [mixedShallowMass, shallowMass]
  | cons a c ih =>
      intro hphase hcarrier
      have ha : a ∈ a ::ₘ c := Multiset.mem_cons_self _ _
      have hnot : ¬ a.phase.val < 3 := by have := hphase a ha; omega
      have ht := ih
        (fun b hb => hphase b (Multiset.mem_cons_of_mem hb))
        (fun b hb => hcarrier b (Multiset.mem_cons_of_mem hb))
      simp only [mixedShallowMass, shallowMass, Multiset.map_cons,
        Multiset.sum_cons] at ht ⊢
      rw [ht]
      congr 1
      by_cases hm : a.role = .main
      · rw [if_pos hm]
        cases hb : a.bias with
        | zero =>
            simp [mixedShallowWeight, hnot, agentMassAboveQ, biasMassAboveQ, hb]
        | dyadic σ j =>
            by_cases hj : j.val < ell <;>
              simp [mixedShallowWeight, hnot, agentMassAboveQ, biasMassAboveQ, hb,
                hj, weightQ, zpow_neg, zpow_natCast, one_div]
      · rw [if_neg hm]
        have hb := hcarrier a ha hm
        simp [mixedShallowWeight, hnot, agentMassAboveQ, biasMassAboveQ, hb]

/-- Full literal small-gap readout at the first Phase-4 seed. No stochastic
checkpoint production is assumed implicitly: its three bounds are explicit. -/
theorem smallReadout_at_first_exit_of_checkpoint
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
      sideMass (oppositeSign σ) (trace init ω u) ≤ M)
    (hpotential : (1000 : ℚ) * augmentedPhi ell (trace init ω u) ≤ M) :
    SmallReadout init M ell σ (trace init ω ρ) := by
  have hST := AveragingEventInterface.clockHistory_seed_lt_exit h
  have hpre : ρ - 1 < ρ := by omega
  have huPre : u ≤ ρ - 1 := by omega
  have hTpre : T ≤ ρ - 1 := hTu.trans huPre
  have hphase : ∀ a ∈ trace init ω (ρ - 1), 3 ≤ a.phase.val :=
    fun a ha => (h.all_three (ρ - 1) hTpre hpre a ha).ge
  have hcarrier := nonmainZero_of_clockHistory h hTpre (Nat.sub_le _ _)
  have hrange : ∀ v, u ≤ v → v ≤ ρ - 1 → ∀ a ∈ trace init ω v,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
    intro v huv hvPre
    exact h.phase_range v (h.entry.order.trans (hTu.trans huv)) (by omega)
  have hsafe : ∀ v, u ≤ v → v ≤ ρ - 1 → ∀ a ∈ trace init ω v,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    intro v huv hvPre
    exact (postActivationSafety hvalid h (hTu.trans huv) (by omega)).1
  have hsmall : ∀ v, u ≤ v → v ≤ ρ - 1 → ∀ a ∈ trace init ω v,
      a.role ≠ .main → a.smallBias.val = 3 := by
    intro v huv hvPre
    exact (postActivationSafety hvalid h (hTu.trans huv) (by omega)).2
  have hminorMono := sideMass_trace_le (oppositeSign σ) init hvalid ω
    u (ρ - 1) huPre hrange hsafe hsmall
  have hphiMono := trace_augmentedPhi_le ell (by omega) init ω
    u (ρ - 1) huPre hrange hsafe hsmall
  have hphiPre : (1000 : ℚ) * augmentedPhi ell (trace init ω (ρ - 1)) ≤ M := by
    linarith only [hpotential, hphiMono]
  have hband := required_band_at_first_exit σ h hTu huρ.le
    (by simpa only [hM] using hcredit)
  rw [hM] at hband
  refine ⟨hwinning, hnonzero, hgap, hell, hellcap, hscale, hscaleUpper,
    hband, ?_, ?_, ?_⟩
  · rw [signMass_first_exit_step (oppositeSign σ) h,
      ← sideMass_eq_signMass (oppositeSign σ) _ hphase hcarrier]
    have hscaled := mul_le_mul_of_nonneg_left hminorMono
      (show (0 : ℚ) ≤ 250 * (2 : ℚ) ^ ell by positivity)
    exact hscaled.trans hminority
  · rw [shallowMass_first_exit_step ell h]
    have hs := scaled_mixedShallowMass_le_phi ell (by omega)
      (trace init ω (ρ - 1))
    rw [mixedShallowMass_eq_shallowMass ell _ hphase hcarrier] at hs
    linarith only [hs, hphiPre]
  · rw [shallowPotential_first_exit_step ell h]
    exact readout_potential_of_augmented_bound ell M _ hphase hcarrier hphiPre

end Ripple.PopulationProtocol.ExactMajority.AveragingCheckpointReadout

end

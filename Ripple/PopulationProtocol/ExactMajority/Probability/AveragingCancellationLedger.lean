-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingCancellationLedger.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingLiveProduct

/-!
# Cancellation counts on the actual mixed trace

Every recorded opposite-level interaction removes one dyadic unit from each
signed side. The two orientation events are already combined by the compiled
cancellationIndicator. Telescoping these actual losses supplies the missing
deterministic target-failure count implication for a cancellation block.
-/

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingCancellationLedger

open TimeTheorem PairLog P3DeterministicAlgebra StageEventSpec
open AveragingMixedAlgebra AveragingMixedLedgers AveragingLiveProduct
open AveragingCancellationProbability

variable {L K m : ℕ}

/-- Two changed labels are removed from both sums, while every remaining
physical label is literally the same. -/
theorem sum_two_changes (f g : Fin m → ℚ) (i j : Fin m) (hij : i ≠ j)
    (hrest : ∀ k, k ≠ i → k ≠ j → g k = f k) :
    (∑ k, g k) + f i + f j = (∑ k, f k) + g i + g j := by
  classical
  let s : Finset (Fin m) := (Finset.univ.erase i).erase j
  have hdecomp (v : Fin m → ℚ) :
      (∑ k, v k) = (∑ k ∈ s, v k) + v j + v i := by
    symm
    dsimp only [s]
    rw [Finset.sum_erase_add (Finset.univ.erase i) v
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩)]
    rw [Finset.sum_erase_add Finset.univ v (Finset.mem_univ _)]
  have hsum : (∑ k ∈ s, g k) = ∑ k ∈ s, f k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    exact hrest k hki hkj
  rw [hdecomp g, hdecomp f, hsum]
  ring

theorem sideMass_trace_eq_sum (σ : Sign)
    (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    sideMass σ (trace init ω t) = ∑ i, sideAtom σ (labelsAt init ω t i) := by
  rw [← labelsAt_config init ω t]
  simp only [sideMass, Multiset.map_map, Function.comp_def, Finset.sum]

theorem cancelled_side_pair_mass (σ : Sign) (level : Fin (L + 1))
    (f : Fin m → AgentState L K) (i j : Fin m)
    (hpair : CancellingPair level f i j) :
    sideAtom σ (f i) + sideAtom σ (f j) = weightQ level := by
  have hw : (0 : ℚ) ≤ 1 / (2 : ℚ) ^ level.val := by positivity
  rcases hpair with hpair | hpair
  · obtain ⟨hi, hj⟩ := hpair
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    cases σ <;>
      simp [sideAtom, prePhase4Mass, hi.1, hj.1, hi.2.2, hj.2.2,
        Bias.toRat, weightQ, neg_div, max_eq_left hw, max_eq_right (neg_nonpos.mpr hw)]
  · obtain ⟨hi, hj⟩ := hpair
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    cases σ <;>
      simp [sideAtom, prePhase4Mass, hi.1, hj.1, hi.2.2, hj.2.2,
        Bias.toRat, weightQ, neg_div, max_eq_left hw, max_eq_right (neg_nonpos.mpr hw)]

theorem selected_cancelling_mass_zero
    (init : Cfg L K) (level : Fin (L + 1)) (t : ℕ) (ω : Ω L K)
    (i j : Fin init.card)
    (hdraw : drawLabels init ω (t + 1) = some (i, j))
    (hpair : CancellingPair level (labelsAt init ω t) i j) :
    prePhase4Mass (labelsAt init ω (t + 1) i) = 0 ∧
      prePhase4Mass (labelsAt init ω (t + 1) j) = 0 := by
  obtain ⟨-, hi, hj, -⟩ := labelsAt_selected_transition init ω t i j hdraw
  rw [hi, hj]
  change prePhase4Mass (Transition L K (labelsAt init ω t i)
      (labelsAt init ω t j)).1 = 0 ∧
    prePhase4Mass (Transition L K (labelsAt init ω t i)
      (labelsAt init ω t j)).2 = 0
  rcases hpair with hpair | hpair
  · obtain ⟨hip, hjn⟩ := hpair
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hip hjn
    have hc := transition_cancel_opposite _ _ level .pos .neg (by decide)
      hip.1 hjn.1 hip.2.1 hjn.2.1 hip.2.2 hjn.2.2
    simp [hc, prePhase4Mass, hip.1, hjn.1, Bias.toRat]
  · obtain ⟨hin, hjp⟩ := hpair
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hin hjp
    have hc := transition_cancel_opposite _ _ level .neg .pos (by decide)
      hin.1 hjp.1 hin.2.1 hjp.2.1 hin.2.2 hjp.2.2
    simp [hc, prePhase4Mass, hin.1, hjp.1, Bias.toRat]

/-- Equality for every counted interaction, without probability or any
future gate premise. -/
theorem sideMass_selected_cancel
    (σ : Sign) (init : Cfg L K) (level : Fin (L + 1)) (t : ℕ) (ω : Ω L K)
    (i j : Fin init.card)
    (hdraw : drawLabels init ω (t + 1) = some (i, j))
    (hpair : CancellingPair level (labelsAt init ω t) i j) :
    sideMass σ (trace init ω (t + 1)) + weightQ level =
      sideMass σ (trace init ω t) := by
  obtain ⟨hij, -, -, hrest⟩ := labelsAt_selected_transition init ω t i j hdraw
  have hz := selected_cancelling_mass_zero init level t ω i j hdraw hpair
  have hleft : sideAtom σ (labelsAt init ω (t + 1) i) = 0 := by
    cases σ <;> simp [sideAtom, hz.1]
  have hright : sideAtom σ (labelsAt init ω (t + 1) j) = 0 := by
    cases σ <;> simp [sideAtom, hz.2]
  have hsum := sum_two_changes
    (fun k => sideAtom σ (labelsAt init ω t k))
    (fun k => sideAtom σ (labelsAt init ω (t + 1) k))
    i j hij
    (fun k hki hkj => congrArg (sideAtom σ) (hrest k hki hkj))
  have hpairmass := cancelled_side_pair_mass σ level (labelsAt init ω t) i j hpair
  dsimp only at hsum
  rw [← sideMass_trace_eq_sum, ← sideMass_trace_eq_sum, hleft, hright] at hsum
  linarith only [hsum, hpairmass]

theorem sideMass_trace_le (σ : Sign)
    (init : Cfg L 256) (hinit : validInitial init)
    (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    sideMass σ (trace init ω t) ≤ sideMass σ (trace init ω s) := by
  have h := trace_mixedSides_le init hinit ω s t hst hrange hsafe hcarrier
  cases σ
  · exact h.1
  · exact h.2

theorem sideMass_cancellation_step
    (σ : Sign) (init : Cfg L 256) (hinit : validInitial init)
    (level : Fin (L + 1)) (t : ℕ) (ω : Ω L 256)
    (hrange : ∀ u, t ≤ u → u ≤ t + 1 → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, t ≤ u → u ≤ t + 1 → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, t ≤ u → u ≤ t + 1 → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    (2 : ℝ) ^ level.val * (sideMass σ (trace init ω (t + 1)) : ℝ) +
        cancellationIndicator init level t ω ≤
      (2 : ℝ) ^ level.val * (sideMass σ (trace init ω t) : ℝ) := by
  classical
  by_cases hc : ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
      CancellingPair level (labelsAt init ω t) i j
  · obtain ⟨i, j, hdraw, hpair⟩ := hc
    have hc : ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
        CancellingPair level (labelsAt init ω t) i j := ⟨i, j, hdraw, hpair⟩
    have hmass := sideMass_selected_cancel σ init level t ω i j hdraw hpair
    have hscaled := congrArg (fun x : ℚ => (2 : ℚ) ^ level.val * x) hmass
    dsimp only at hscaled
    rw [mul_add, scaled_weight_at_level] at hscaled
    have hscaledR :
        (2 : ℝ) ^ level.val * (sideMass σ (trace init ω (t + 1)) : ℝ) + 1 =
          (2 : ℝ) ^ level.val * (sideMass σ (trace init ω t) : ℝ) := by
      exact_mod_cast hscaled
    simpa only [cancellationIndicator, if_pos hc] using hscaledR.le
  · have hmass := sideMass_trace_le σ init hinit ω t (t + 1) (by omega)
      hrange hsafe hcarrier
    have hmassR : (sideMass σ (trace init ω (t + 1)) : ℝ) ≤
        (sideMass σ (trace init ω t) : ℝ) := by exact_mod_cast hmass
    simpa only [cancellationIndicator, if_neg hc, add_zero] using
      mul_le_mul_of_nonneg_left hmassR (by positivity : (0 : ℝ) ≤ 2 ^ level.val)

def cancellationCountFrom (init : Cfg L K) (level : Fin (L + 1))
    (s N : ℕ) (ω : Ω L K) : ℝ :=
  ∑ k ∈ Finset.range N, cancellationIndicator init level (s + k) ω

theorem cancellationCountFrom_zero_start
    (init : Cfg L K) (level : Fin (L + 1)) (N : ℕ) (ω : Ω L K) :
    cancellationCountFrom init level 0 N ω =
      PhaseThreeScalar.bernoulliCount (cancellationIndicator init level) N ω := by
  simp only [cancellationCountFrom, PhaseThreeScalar.bernoulliCount, Nat.zero_add]

/-- The actual side-mass ledger, at an arbitrary raw interaction offset. -/
theorem sideMass_cancellation_ledger
    (σ : Sign) (init : Cfg L 256) (hinit : validInitial init)
    (level : Fin (L + 1)) (ω : Ω L 256) (s N : ℕ)
    (hrange : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    (2 : ℝ) ^ level.val * (sideMass σ (trace init ω (s + N)) : ℝ) +
        cancellationCountFrom init level s N ω ≤
      (2 : ℝ) ^ level.val * (sideMass σ (trace init ω s) : ℝ) := by
  revert hrange hsafe hcarrier
  induction N with
  | zero => intro _ _ _; simp [cancellationCountFrom]
  | succ N ih =>
      intro hrange hsafe hcarrier
      have hprevious := ih
        (fun u hsu hut => hrange u hsu (by omega))
        (fun u hsu hut => hsafe u hsu (by omega))
        (fun u hsu hut => hcarrier u hsu (by omega))
      have hstep := sideMass_cancellation_step σ init hinit level (s + N) ω
        (fun u hsu hut => hrange u (by omega) (by omega))
        (fun u hsu hut => hsafe u (by omega) (by omega))
        (fun u hsu hut => hcarrier u (by omega) (by omega))
      have hcount :
          cancellationCountFrom init level s (N + 1) ω =
            cancellationCountFrom init level s N ω +
              cancellationIndicator init level (s + N) ω := by
        exact Finset.sum_range_succ _ _
      rw [hcount, show s + (N + 1) = (s + N) + 1 by omega]
      linarith only [hprevious, hstep]

theorem totalMass_cancellation_ledger
    (init : Cfg L 256) (hinit : validInitial init)
    (level : Fin (L + 1)) (ω : Ω L 256) (s N : ℕ)
    (hrange : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    (2 : ℝ) ^ level.val * (mixedAbsoluteMass (trace init ω (s + N)) : ℝ) +
        2 * cancellationCountFrom init level s N ω ≤
      (2 : ℝ) ^ level.val * (mixedAbsoluteMass (trace init ω s) : ℝ) := by
  have hp := sideMass_cancellation_ledger .pos init hinit level ω s N
    hrange hsafe hcarrier
  have hn := sideMass_cancellation_ledger .neg init hinit level ω s N
    hrange hsafe hcarrier
  have hstart := congrArg (fun q : ℚ => (q : ℝ)) (sideMass_add (trace init ω s))
  have hfinish := congrArg (fun q : ℚ => (q : ℝ))
    (sideMass_add (trace init ω (s + N)))
  push_cast at hstart hfinish
  rw [← hstart, ← hfinish]
  nlinarith only [hp, hn]

/-- Failure of the next total target forces fewer than
(previous - target/2) M of the actual level cancellations. -/
theorem total_target_failure_count
    (init : Cfg L 256) (hinit : validInitial init)
    (level : Fin (L + 1)) (ω : Ω L 256) (s N : ℕ)
    (hrange : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3)
    {previous target M : ℝ}
    (hstart : (2 : ℝ) ^ level.val * (mixedAbsoluteMass (trace init ω s) : ℝ) ≤
      2 * previous * M)
    (hfail : target * M <
      (2 : ℝ) ^ level.val * (mixedAbsoluteMass (trace init ω (s + N)) : ℝ)) :
    cancellationCountFrom init level s N ω < (previous - target / 2) * M := by
  have h := totalMass_cancellation_ledger init hinit level ω s N
    hrange hsafe hcarrier
  nlinarith only [h, hstart, hfail]

/-- The minority ledger removes one unit per actual cancellation. -/
theorem minority_target_failure_count
    (σ : Sign) (init : Cfg L 256) (hinit : validInitial init)
    (level : Fin (L + 1)) (ω : Ω L 256) (s N : ℕ)
    (hrange : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ s + N → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3)
    {previous target M : ℝ}
    (hstart : (2 : ℝ) ^ level.val *
      (sideMass (oppositeSign σ) (trace init ω s) : ℝ) ≤ 2 * previous * M)
    (hfail : target * M < (2 : ℝ) ^ level.val *
      (sideMass (oppositeSign σ) (trace init ω (s + N)) : ℝ)) :
    cancellationCountFrom init level s N ω < (2 * previous - target) * M := by
  have h := sideMass_cancellation_ledger (oppositeSign σ) init hinit level ω s N
    hrange hsafe hcarrier
  nlinarith only [h, hstart, hfail]

end Ripple.PopulationProtocol.ExactMajority.AveragingCancellationLedger

end

/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase1Productive
import Tri.ByzantinePhase1Ladder
import Tri.StagedLazyHitting

/-!
# Raw-clock stopped Phase-I ladder

The productive Phase-I estimate is converted rung by rung to raw interaction
time.  Since dyadic checkpoints are not absorbing for the ordinary raw kernel,
each rung is target-frozen and the varying frozen blocks are composed through
the staged-lazy-hitting comparison.
-/

namespace Tri.Byzantine

open scoped BigOperators ENNReal

noncomputable section

variable {n B z : ℕ}

/-- Stop set for dyadic rung `j`: the lower half-gap boundary or the next
checkpoint. -/
def Phase1DyadicStop
    (n d₀ j : ℕ) (q : Phase1Level n B z) : Prop :=
  Phase1LowerFailure
      (n := n) (B := B) (z := z)
      (phase1DyadicScale n d₀ j) q ∨
    Phase1DyadicCheckpoint
      (B := B) (z := z) n d₀ (j + 1) q

instance phase1DyadicStopDecidable (n d₀ j : ℕ) :
    DecidablePred
      (Phase1DyadicStop (B := B) (z := z) n d₀ j) := by
  intro q
  unfold Phase1DyadicStop
  infer_instance

/-- Correct raw horizon for one rung. -/
def phase1RawDyadicRungHorizon (n : ℕ) : ℕ :=
  40 * n

/-- Lemma-6 error plus the raw/productive clock error. -/
noncomputable def phase1RawDyadicRungError
    (n d₀ j : ℕ) : ℝ≥0∞ :=
  phase1DyadicRungEnvelope n d₀ j +
    ((1 : ℝ≥0∞) / 2) ^ n

/-- Correct total raw horizon for `J` rungs. -/
def phase1RawDyadicLadderHorizon (n J : ℕ) : ℕ :=
  J * (40 * n)

/-- Exact sum of the corrected raw rung errors. -/
noncomputable def phase1RawDyadicLadderError
    (n d₀ J : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range J, phase1RawDyadicRungError n d₀ j

/-- Convert one stopped productive rung to the corresponding target-frozen
raw rung. -/
theorem phase1_reference_raw_dyadic_rung_of_productive
    (h3 : 3 ≤ n) (d₀ j : ℕ)
    (hlive :
      ∀ q,
        ¬ Phase1DyadicStop (B := B) (z := z) n d₀ j q →
          0 < State.x q.1 ∧ 0 < State.y q.1)
    (hpFloor :
      ∀ q,
        ¬ Phase1DyadicStop (B := B) (z := z) n d₀ j q →
          (phase1ClockP : ℝ≥0∞) ≤ phase1ProductiveMass h3 q)
    (hproductive :
      Reaches
        (freeze
          (Phase1DyadicStop (B := B) (z := z) n d₀ j)
          (phase1ProductiveReferenceStep h3))
        (5 * n)
        (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j)
        (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1))
        (phase1DyadicRungEnvelope n d₀ j)) :
    Reaches
      (freeze
        (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1))
        (phase1ReferenceStep h3))
      (phase1RawDyadicRungHorizon n)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1))
      (phase1RawDyadicRungError n d₀ j) := by
  intro q hq
  have hclock :=
    phase1ReferenceStep_failure_le_productive_add_clock_40n
      (n := n) (B := B) (z := z)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1))
      (Phase1DyadicStop (B := B) (z := z) n d₀ j)
      h3 hlive hpFloor q
  have hbound :=
    hclock.trans (add_le_add (hproductive q hq) le_rfl)
  -- the goal is the unfolded form of `terminalFailureMass`
  simpa [phase1RawDyadicRungHorizon,
    phase1RawDyadicRungError, terminalFailureMass] using hbound

/-- Correct replacement for `phase1_reference_dyadic_ladder_to_half`.

Every rung uses its own target-frozen raw block.  The unpaused raw chain frozen
only at the final half target has no more failure than this adaptively paused
schedule. -/
theorem phase1_reference_raw_stopped_ladder_to_half
    (h3 : 3 ≤ n) (d₀ J : ℕ)
    (hfinal : n ≤ 2 * phase1DyadicScale n d₀ J)
    (hrungs :
      ∀ j < J,
        Reaches
          (freeze
            (Phase1DyadicCheckpoint
              (B := B) (z := z) n d₀ (j + 1))
            (phase1ReferenceStep h3))
          (phase1RawDyadicRungHorizon n)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1))
          (phase1RawDyadicRungError n d₀ j)) :
    Reaches
      (freeze
        (Phase1HalfTarget (n := n) (B := B) (z := z))
        (phase1ReferenceStep h3))
      (phase1RawDyadicLadderHorizon n J)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ 0)
      (Phase1HalfTarget (n := n) (B := B) (z := z))
      (phase1RawDyadicLadderError n d₀ J) := by
  let P : ℕ → Phase1Level n B z → Prop :=
    fun j => Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j
  let T : ℕ → ℕ := fun _ => phase1RawDyadicRungHorizon n
  let Stop : ℕ → Phase1Level n B z → Phase1Level n B z → Prop :=
    fun j _ q => P (j + 1) q
  letI : ∀ j, DecidablePred (P j) := by
    intro j q
    dsimp only [P]
    infer_instance
  letI : ∀ j a, DecidablePred (Stop j a) := by
    intro j a q
    exact inferInstanceAs (Decidable (P (j + 1) q))
  have hT : ∀ j < J, 0 < T j := by
    intro j hj
    dsimp only [T, phase1RawDyadicRungHorizon]
    omega
  have hstage :
      ∀ j < J, ∀ q, P j q →
        terminalFailureMass
          (StagedFreezeControl.block
            (phase1ReferenceStep h3) Stop T j q)
          (P (j + 1)) ≤
        phase1RawDyadicRungError n d₀ j := by
    intro j hj q hq
    change
      terminalFailureMass
        (iter
          (freeze (P (j + 1)) (phase1ReferenceStep h3))
          (phase1RawDyadicRungHorizon n) q)
        (P (j + 1)) ≤
      phase1RawDyadicRungError n d₀ j
    exact hrungs j hj q hq
  intro q₀ hq₀
  have hstaged :=
    terminalFailureMass_stagedIter
      (K := StagedFreezeControl.block
        (phase1ReferenceStep h3) Stop T)
      (P := P)
      (ε := fun j => phase1RawDyadicRungError n d₀ j)
      (m := J) hstage q₀ hq₀
  have hcompare :=
    StagedFreezeControl.targetFreeze_failure_le_stagedFreeze
      (Phase1HalfTarget (n := n) (B := B) (z := z))
      (phase1ReferenceStep h3) Stop T J hT q₀
  have hsumT :
      (∑ j ∈ Finset.range J, T j) =
        phase1RawDyadicLadderHorizon n J := by
    simp [T, phase1RawDyadicRungHorizon,
      phase1RawDyadicLadderHorizon]
  rw [hsumT] at hcompare
  have hpost :
      terminalFailureMass
          (stagedIter
            (StagedFreezeControl.block
              (phase1ReferenceStep h3) Stop T) J q₀)
          (Phase1HalfTarget (n := n) (B := B) (z := z)) ≤
        terminalFailureMass
          (stagedIter
            (StagedFreezeControl.block
              (phase1ReferenceStep h3) Stop T) J q₀)
          (P J) :=
    terminalFailureMass_mono _ _ _ (by
      intro q hq
      exact phase1DyadicCheckpoint_implies_half
        (n := n) (B := B) (z := z) hfinal hq)
  exact hcompare.trans (hpost.trans hstaged)

/-- Full raw-clock assembly once the stopped productive rungs are supplied. -/
theorem phase1_reference_raw_dyadic_ladder_to_half_of_productive
    (h3 : 3 ≤ n) (d₀ J : ℕ)
    (hfinal : n ≤ 2 * phase1DyadicScale n d₀ J)
    (hlive :
      ∀ j < J, ∀ q,
        ¬ Phase1DyadicStop (B := B) (z := z) n d₀ j q →
          0 < State.x q.1 ∧ 0 < State.y q.1)
    (hpFloor :
      ∀ j < J, ∀ q,
        ¬ Phase1DyadicStop (B := B) (z := z) n d₀ j q →
          (phase1ClockP : ℝ≥0∞) ≤ phase1ProductiveMass h3 q)
    (hproductive :
      ∀ j < J,
        Reaches
          (freeze
            (Phase1DyadicStop (B := B) (z := z) n d₀ j)
            (phase1ProductiveReferenceStep h3))
          (5 * n)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ j)
          (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ (j + 1))
          (phase1DyadicRungEnvelope n d₀ j)) :
    Reaches
      (freeze
        (Phase1HalfTarget (n := n) (B := B) (z := z))
        (phase1ReferenceStep h3))
      (phase1RawDyadicLadderHorizon n J)
      (Phase1DyadicCheckpoint (B := B) (z := z) n d₀ 0)
      (Phase1HalfTarget (n := n) (B := B) (z := z))
      (phase1RawDyadicLadderError n d₀ J) := by
  apply phase1_reference_raw_stopped_ladder_to_half
    (n := n) (B := B) (z := z) h3 d₀ J hfinal
  intro j hj
  exact phase1_reference_raw_dyadic_rung_of_productive
    (n := n) (B := B) (z := z)
    h3 d₀ j (hlive j hj) (hpFloor j hj) (hproductive j hj)

end

end Tri.Byzantine

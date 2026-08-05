/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase2ClockFloor
import Tri.StagedLazyHitting

/-!
# Raw-clock stopped Phase-II ladder

Every productive Phase-II rung is converted to a target-frozen raw block.
The varying frozen blocks are composed by the staged hitting interface because
neither a dyadic aggregate cap nor the strong target is absorbing for the
ordinary raw reference kernel.
-/

namespace Tri.Byzantine

open scoped BigOperators ENNReal NNReal

noncomputable section

variable {n B z : ℕ}

/-- A rung stops on the Phase-I handoff failure or on reaching the next
cumulative Phase-II target. -/
def Phase2DyadicRawStop
    (j : ℕ) (q : Phase2Level n B z) : Prop :=
  Phase2EntryFailure q ∨
    Phase2LadderTarget (n := n) (B := B) (z := z) (j + 1) q

instance phase2DyadicRawStopDecidable (j : ℕ) :
    DecidablePred
      (Phase2DyadicRawStop (n := n) (B := B) (z := z) j) := by
  intro q
  unfold Phase2DyadicRawStop
  infer_instance

/-- Productive quota at denominator `K_j`. This is not a raw horizon. -/
def phase2DyadicProductiveQuota (n j : ℕ) : ℕ :=
  n / phase2DyadicK j

/-- The m-dependent clock conversion gives a constant raw deadline. -/
def phase2RawDyadicRungHorizon (n : ℕ) : ℕ :=
  4 * n

/-- Rung-specific productive floor `1/(2K_j)`. -/
noncomputable def phase2DyadicClockP (j : ℕ) : NNReal :=
  (1 : NNReal) /
    (((2 * phase2DyadicK j : ℕ) : NNReal))

/-- Complement of the rung-specific productive floor. -/
noncomputable def phase2DyadicClockP' (j : ℕ) : NNReal :=
  1 - phase2DyadicClockP j

theorem phase2DyadicClockP_le_one (j : ℕ) :
    phase2DyadicClockP j ≤ 1 := by
  unfold phase2DyadicClockP
  rw [div_le_one]
  · -- `K j = 2 ^ j * 4`, so `2 * K j ≥ 8 ≥ 1`.  omega cannot handle `2 ^ j`;
    -- bound it below by `1` first.
    have hK : 1 ≤ phase2DyadicK j := by
      unfold phase2DyadicK
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      nlinarith
    exact_mod_cast (by omega : 1 ≤ 2 * phase2DyadicK j)
  · have hK : 1 ≤ phase2DyadicK j := by
      unfold phase2DyadicK
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      nlinarith
    have : 0 < 2 * phase2DyadicK j := by omega
    exact_mod_cast this

theorem phase2DyadicClockP_add_complement (j : ℕ) :
    (phase2DyadicClockP j : ℝ≥0∞) +
        (phase2DyadicClockP' j : ℝ≥0∞) = 1 := by
  have hNN :
      phase2DyadicClockP j + phase2DyadicClockP' j =
        (1 : NNReal) := by
    unfold phase2DyadicClockP'
    rw [add_comm,
      tsub_add_cancel_of_le (phase2DyadicClockP_le_one j)]
  simpa using
    congrArg (fun x : NNReal => (x : ℝ≥0∞)) hNN

/-- The raw-clock parameter is the paper floor proved from the current
Phase-II dyadic state. -/
theorem phase2DyadicClockP_eq_floor (j : ℕ) :
    (phase2DyadicClockP j : ℝ≥0∞) =
      (phase2DyadicClockFloor j : ℝ≥0∞) := by
  rfl

/-- The raw stop and the clock-floor stop are the same event. -/
theorem phase2DyadicRawStop_iff_clockStop
    (j : ℕ) (q : Phase2Level n B z) :
    Phase2DyadicRawStop
        (n := n) (B := B) (z := z) j q ↔
      Phase2DyadicClockStop
        (n := n) (B := B) (z := z) j q := by
  rw [phase2DyadicClockStop_iff]
  rfl

/-- Every non-stopped Phase-II dyadic state has both honest species present. -/
theorem phase2DyadicRawStop_live
    (h3 : 3 ≤ n) (j : ℕ) (q : Phase2Level n B z)
    (hlive :
      ¬ Phase2DyadicRawStop
        (n := n) (B := B) (z := z) j q) :
    0 < State.x q.1 ∧ 0 < State.y q.1 := by
  have hentry : ¬ Phase2EntryFailure q := by
    intro h
    exact hlive (Or.inl h)
  have htarget :
      ¬ Phase2LadderTarget
        (n := n) (B := B) (z := z) (j + 1) q := by
    intro h
    exact hlive (Or.inr h)
  have hstrong : ¬ Phase2StrongTarget q := by
    intro h
    exact htarget (Or.inl h)
  constructor
  · unfold Phase2EntryFailure at hentry
    have hx : 3 * n ≤ 4 * State.x q.1 :=
      Nat.le_of_not_gt hentry
    omega
  · have hyz : State.z q.1 < State.y q.1 := by
      apply Nat.lt_of_not_ge
      intro h
      exact hstrong ((phase2StrongTarget_iff_y_le_z q).2 h)
    omega

/-- The proved state-dependent floor discharges the `hpFloor` input of the
generic raw/productive clock comparison. -/
theorem phase2DyadicProductiveMass_ge_rawStop
    (h3 : 3 ≤ n) (j : ℕ) (q : Phase2Level n B z)
    (hlive :
      ¬ Phase2DyadicRawStop
        (n := n) (B := B) (z := z) j q) :
    (phase2DyadicClockP j : ℝ≥0∞) ≤
      phase1ProductiveMass h3 q := by
  rw [phase2DyadicClockP_eq_floor]
  apply phase2DyadicProductiveMass_ge_canonical h3 j q
  rwa [← phase2DyadicRawStop_iff_clockStop j q]

/-- Exact clock-failure term produced by the generic productive countdown.
No stronger uniform simplification is assumed here. -/
noncomputable def phase2RawDyadicClockError
    (n j : ℕ) : ℝ≥0∞ :=
  ((phase2DyadicClockP' j : ℝ≥0∞) +
      (phase2DyadicClockP j : ℝ≥0∞) *
        ((1 : ℝ≥0∞) / 2)) ^
      phase2RawDyadicRungHorizon n *
    (2 : ℝ≥0∞) ^ phase2DyadicProductiveQuota n j

/-- Productive rung error plus its explicit raw-clock conversion error. -/
noncomputable def phase2RawDyadicRungError
    (A₂ a₂ : ℝ) (γ n j : ℕ) : ℝ≥0∞ :=
  phase2RungEnvelope A₂ a₂ γ n +
    phase2RawDyadicClockError n j

/-- Total raw deadline for `J` constant-cost rungs. -/
def phase2RawDyadicLadderHorizon (n J : ℕ) : ℕ :=
  J * (4 * n)

/-- Exact sum of all raw Phase-II rung errors. -/
noncomputable def phase2RawDyadicLadderError
    (A₂ a₂ : ℝ) (γ n J : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range J,
    phase2RawDyadicRungError A₂ a₂ γ n j

/-- Convert one stopped productive Phase-II rung to the corresponding
next-target-frozen raw rung. The actual productive probability estimate is the
explicit hypothesis `hproductive`. -/
theorem phase2_reference_raw_dyadic_rung_of_productive
    (h3 : 3 ≤ n) (γ j : ℕ) (A₂ a₂ : ℝ)
    (hlive :
      ∀ q,
        ¬ Phase2DyadicRawStop
            (n := n) (B := B) (z := z) j q →
          0 < State.x q.1 ∧ 0 < State.y q.1)
    (hpFloor :
      ∀ q,
        ¬ Phase2DyadicRawStop
            (n := n) (B := B) (z := z) j q →
          (phase2DyadicClockP j : ℝ≥0∞) ≤
            phase1ProductiveMass h3 q)
    (hproductive :
      Reaches
        (freeze
          (Phase2DyadicRawStop
            (n := n) (B := B) (z := z) j)
          (phase1ProductiveReferenceStep h3))
        (phase2DyadicProductiveQuota n j)
        (Phase2LadderTarget
          (n := n) (B := B) (z := z) j)
        (Phase2LadderTarget
          (n := n) (B := B) (z := z) (j + 1))
        (phase2RungEnvelope A₂ a₂ γ n)) :
    Reaches
      (freeze
        (Phase2LadderTarget
          (n := n) (B := B) (z := z) (j + 1))
        (phase2ReferenceStep h3))
      (phase2RawDyadicRungHorizon n)
      (Phase2LadderTarget
        (n := n) (B := B) (z := z) j)
      (Phase2LadderTarget
        (n := n) (B := B) (z := z) (j + 1))
      (phase2RawDyadicRungError A₂ a₂ γ n j) := by
  intro q hq
  have hclock :=
    phase1ReferenceStep_failure_le_productive_add_clock
      (Phase2LadderTarget
        (n := n) (B := B) (z := z) (j + 1))
      (Phase2DyadicRawStop
        (n := n) (B := B) (z := z) j)
      h3
      (phase2DyadicClockP j : ℝ≥0∞)
      (phase2DyadicClockP' j : ℝ≥0∞)
      (phase2DyadicClockP_add_complement j)
      hlive hpFloor
      (phase2RawDyadicRungHorizon n)
      (phase2DyadicProductiveQuota n j) q
  have hbound :=
    hclock.trans (add_le_add (hproductive q hq) le_rfl)
  simpa [phase2RawDyadicRungHorizon,
    phase2RawDyadicRungError,
    phase2RawDyadicClockError,
    terminalFailureMass] using hbound

/-- Compose target-frozen raw blocks through a stage-indexed hitting schedule.
This is the sound replacement for `phase2_reference_ladder_chain`. -/
theorem phase2_reference_raw_stopped_ladder_to_entry_or_endpoint
    (h3 : 3 ≤ n) (γ J : ℕ) (A₂ a₂ : ℝ)
    (hrungs :
      ∀ j < J,
        Reaches
          (freeze
            (Phase2LadderTarget
              (n := n) (B := B) (z := z) (j + 1))
            (phase2ReferenceStep h3))
          (phase2RawDyadicRungHorizon n)
          (Phase2LadderTarget
            (n := n) (B := B) (z := z) j)
          (Phase2LadderTarget
            (n := n) (B := B) (z := z) (j + 1))
          (phase2RawDyadicRungError A₂ a₂ γ n j)) :
    Reaches
      (freeze
        (Phase2LadderTarget
          (n := n) (B := B) (z := z) J)
        (phase2ReferenceStep h3))
      (phase2RawDyadicLadderHorizon n J)
      (Phase2DyadicCheckpoint
        (n := n) (B := B) (z := z) 0)
      (Phase2LadderTarget
        (n := n) (B := B) (z := z) J)
      (phase2RawDyadicLadderError A₂ a₂ γ n J) := by
  let P : ℕ → Phase2Level n B z → Prop :=
    fun j =>
      Phase2LadderTarget (n := n) (B := B) (z := z) j
  let T : ℕ → ℕ := fun _ => phase2RawDyadicRungHorizon n
  let Stop :
      ℕ → Phase2Level n B z → Phase2Level n B z → Prop :=
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
    dsimp only [T, phase2RawDyadicRungHorizon]
    omega
  have hstage :
      ∀ j < J, ∀ q, P j q →
        terminalFailureMass
          (StagedFreezeControl.block
            (phase2ReferenceStep h3) Stop T j q)
          (P (j + 1)) ≤
        phase2RawDyadicRungError A₂ a₂ γ n j := by
    intro j hj q hq
    change
      terminalFailureMass
        (iter
          (freeze (P (j + 1)) (phase2ReferenceStep h3))
          (phase2RawDyadicRungHorizon n) q)
        (P (j + 1)) ≤
      phase2RawDyadicRungError A₂ a₂ γ n j
    exact hrungs j hj q hq
  intro q₀ hq₀
  have hP₀ : P 0 q₀ := by
    exact Or.inr hq₀
  have hstaged :=
    terminalFailureMass_stagedIter
      (K := StagedFreezeControl.block
        (phase2ReferenceStep h3) Stop T)
      (P := P)
      (ε := fun j =>
        phase2RawDyadicRungError A₂ a₂ γ n j)
      (m := J) hstage q₀ hP₀
  have hcompare :=
    StagedFreezeControl.targetFreeze_failure_le_stagedFreeze
      (Phase2LadderTarget
        (n := n) (B := B) (z := z) J)
      (phase2ReferenceStep h3) Stop T J hT q₀
  have hsumT :
      (∑ j ∈ Finset.range J, T j) =
        phase2RawDyadicLadderHorizon n J := by
    simp [T, phase2RawDyadicRungHorizon,
      phase2RawDyadicLadderHorizon]
  rw [hsumT] at hcompare
  exact hcompare.trans (by
    simpa [P, phase2RawDyadicLadderError] using hstaged)

/-- Full raw-clock assembly once the productive rung estimates are supplied. -/
theorem phase2_reference_raw_dyadic_ladder_of_productive
    (h3 : 3 ≤ n) (γ J : ℕ) (A₂ a₂ : ℝ)
    (hlive :
      ∀ j < J, ∀ q,
        ¬ Phase2DyadicRawStop
            (n := n) (B := B) (z := z) j q →
          0 < State.x q.1 ∧ 0 < State.y q.1)
    (hpFloor :
      ∀ j < J, ∀ q,
        ¬ Phase2DyadicRawStop
            (n := n) (B := B) (z := z) j q →
          (phase2DyadicClockP j : ℝ≥0∞) ≤
            phase1ProductiveMass h3 q)
    (hproductive :
      ∀ j < J,
        Reaches
          (freeze
            (Phase2DyadicRawStop
              (n := n) (B := B) (z := z) j)
            (phase1ProductiveReferenceStep h3))
          (phase2DyadicProductiveQuota n j)
          (Phase2LadderTarget
            (n := n) (B := B) (z := z) j)
          (Phase2LadderTarget
            (n := n) (B := B) (z := z) (j + 1))
          (phase2RungEnvelope A₂ a₂ γ n)) :
    Reaches
      (freeze
        (Phase2LadderTarget
          (n := n) (B := B) (z := z) J)
        (phase2ReferenceStep h3))
      (phase2RawDyadicLadderHorizon n J)
      (Phase2DyadicCheckpoint
        (n := n) (B := B) (z := z) 0)
      (Phase2LadderTarget
        (n := n) (B := B) (z := z) J)
      (phase2RawDyadicLadderError A₂ a₂ γ n J) := by
  apply phase2_reference_raw_stopped_ladder_to_entry_or_endpoint
    (n := n) (B := B) (z := z) h3 γ J A₂ a₂
  intro j hj
  exact phase2_reference_raw_dyadic_rung_of_productive
    (n := n) (B := B) (z := z)
    h3 γ j A₂ a₂
    (hlive j hj) (hpFloor j hj) (hproductive j hj)

/-- Full raw-clock Phase-II assembly with the live-state and productive-floor
inputs discharged from the actual dyadic stop predicate. -/
theorem phase2_reference_raw_dyadic_ladder_of_productive_canonical
    (h3 : 3 ≤ n) (γ J : ℕ) (A₂ a₂ : ℝ)
    (hproductive :
      ∀ j < J,
        Reaches
          (freeze
            (Phase2DyadicRawStop
              (n := n) (B := B) (z := z) j)
            (phase1ProductiveReferenceStep h3))
          (phase2DyadicProductiveQuota n j)
          (Phase2LadderTarget
            (n := n) (B := B) (z := z) j)
          (Phase2LadderTarget
            (n := n) (B := B) (z := z) (j + 1))
          (phase2RungEnvelope A₂ a₂ γ n)) :
    Reaches
      (freeze
        (Phase2LadderTarget
          (n := n) (B := B) (z := z) J)
        (phase2ReferenceStep h3))
      (phase2RawDyadicLadderHorizon n J)
      (Phase2DyadicCheckpoint
        (n := n) (B := B) (z := z) 0)
      (Phase2LadderTarget
        (n := n) (B := B) (z := z) J)
      (phase2RawDyadicLadderError A₂ a₂ γ n J) := by
  apply phase2_reference_raw_dyadic_ladder_of_productive
    (n := n) (B := B) (z := z)
    h3 γ J A₂ a₂
  · intro j hj q hq
    exact phase2DyadicRawStop_live h3 j q hq
  · intro j hj q hq
    exact phase2DyadicProductiveMass_ge_rawStop h3 j q hq
  · exact hproductive

end

end Tri.Byzantine

#print axioms Tri.Byzantine.phase2DyadicRawStop_live
#print axioms Tri.Byzantine.phase2DyadicProductiveMass_ge_rawStop
#print axioms Tri.Byzantine.phase2_reference_raw_dyadic_ladder_of_productive_canonical

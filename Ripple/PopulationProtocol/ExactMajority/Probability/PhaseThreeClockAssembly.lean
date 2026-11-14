import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockTransfer
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProducer

/-!
# Assembly of the asynchronous clock producer (N12, steps 3–6 interface and §11)

The N12 headline is reduced (`PhaseThreeClockProducer.asynchronous_clock_estimate_of_local`)
to the local estimate at a finite first Phase-3 seed `s` with a `SeedProfile` state. This
file decomposes that local estimate into the two probabilistic inputs that the remaining
producers must supply, with the exact event types:

* `VirtualGoodAt init s ω`: an entry at `s` with a virtual clock core
  (`PhaseThreeClockCore.VirtualClockCore`) — the output of steps 3–4 (PHASE3 P2–P14,
  all rows of the §11 table except the two P15 rows);
* `ExitGoodAt init s ω`: the actual first Phase-4 seed by `cap + logWindow n 400`,
  the threshold spread by `s + logWindow n 20000` — the output of step 6 (P15).

`ClockProducerInputs init ε₁ ε₂` states the two fibre estimates; the deterministic
transfer `clockHistory_of_virtual` (step 5) closes the remaining case, and
`asynchronous_clock_estimate_of_inputs` is the headline with `ε₁ + ε₂ ≤ 8 / n ^ 5`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockAssembly

open TimeTheorem PairLog StageEventSpec PhaseThreeClockCore PhaseThreeClockTransfer
  PhaseThreeClockProducer

variable {n : ℕ} (init : InputCfg n)

/-- Steps 3–4 output: an entry at the first seed `s` within the early horizon with a
virtual clock core. -/
def VirtualGoodAt (s : ℕ) (ω : InputLog n) : Prop :=
  ∃ T : ℕ, ∃ w : ClockTimes init, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧
    VirtualClockCore init ω s T w

/-- Step 6 output (PHASE3 P15): the genuine first Phase-4 seed occurs by the exit
deadline after every virtual cap witness, within the final horizon, and the threshold
has spread by the final horizon. -/
def ExitGoodAt (s : ℕ) (ω : InputLog n) : Prop :=
  ∃ ρ : ℕ, firstPhaseSeed init 4 ρ ω ∧ ρ ≤ s + logWindow n 20000 ∧
    allGE 4 (trace init ω (s + logWindow n 20000)) ∧
    ∀ T (w : ClockTimes init), T ≤ earlyHorizon n → AsyncEntry init ω s T →
      VirtualClockCore init ω s T w → ρ ≤ w.cap + logWindow n 400

/-- Step 5: on both good events the reviewed clock history holds. -/
theorem reviewedClockGood_of_good (hn : 1 ≤ n) {s : ℕ} {ω : InputLog n}
    (hv : VirtualGoodAt init s ω) (he : ExitGoodAt init s ω) :
    ∃ T ρ, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧ reviewedClockGood init ω s T ρ := by
  obtain ⟨T, w, hT, hentry, hcore⟩ := hv
  obtain ⟨ρ, hexit, hdead, hspread, hafter⟩ := he
  exact ⟨T, ρ, hT, hentry, w,
    clockHistory_of_virtual init ω hn hentry hcore hexit hdead (hafter T w hT hentry hcore) hspread⟩

/-- The two probabilistic inputs of the producer, on the fibres of the first-seed
stopping time. `ε₁` collects every row of the PHASE3 §11 table except the two P15 rows;
`ε₂` collects the two P15 rows. -/
structure ClockProducerInputs (ε₁ ε₂ : ℝ≥0∞) : Prop where
  virtual_core_tail : ∀ s : ℕ,
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω} ≤
      ε₁ * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)}
  exit_tail : ∀ s : ℕ,
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      VirtualGoodAt init s ω ∧ ¬ ExitGoodAt init s ω} ≤
      ε₂ * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)}

theorem local_estimate_of_inputs (hn : 1 ≤ n) {ε₁ ε₂ : ℝ≥0∞}
    (h : ClockProducerInputs init ε₁ ε₂) (s : ℕ) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
        SeedProfile n init (trace init ω s) ∧ clockBadAfter init s ω} ≤
      (ε₁ + ε₂) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  have hsub : {ω : InputLog n | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧ clockBadAfter init s ω} ⊆
      {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧ SeedProfile n init (trace init ω s) ∧
        (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω} ∪
      {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
        VirtualGoodAt init s ω ∧ ¬ ExitGoodAt init s ω} := by
    rintro ω ⟨hs, hsp, hbad⟩
    by_cases hv : VirtualGoodAt init s ω
    · by_cases he : ExitGoodAt init s ω
      · exact absurd (reviewedClockGood_of_good init hn hv he) hbad.2
      · exact Or.inr ⟨hs, hv, he⟩
    · exact Or.inl ⟨hs, hsp, hbad.1, hv⟩
  calc law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
        SeedProfile n init (trace init ω s) ∧ clockBadAfter init s ω}
      ≤ law init _ := measure_mono hsub
    _ ≤ law init _ + law init _ := measure_union_le _ _
    _ ≤ ε₁ * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} +
        ε₂ * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} :=
        add_le_add (h.virtual_core_tail s) (h.exit_tail s)
    _ = (ε₁ + ε₂) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := (add_mul _ _ _).symm

/-- The N12 headline from the two producer inputs and the §11 budget. -/
theorem asynchronous_clock_estimate_of_inputs (hn : 1 ≤ n) {ε₁ ε₂ : ℝ≥0∞}
    (h : ClockProducerInputs init ε₁ ε₂)
    (hbudget : ε₁ + ε₂ ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 5)) :
    law init (phaseClockFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 5) :=
  asynchronous_clock_estimate_of_local init fun s =>
    (local_estimate_of_inputs init hn h s).trans (mul_le_mul_right' hbudget _)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockAssembly

end

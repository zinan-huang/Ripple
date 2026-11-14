-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseNineContinuation.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseNineContinuationBits
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseNineContinuationCleanup

/-!
The final Phase-9 endpoint has the original-law budget seven over n to
the fifth power.  The cleanup starts at its observed deterministic prefix;
the successful opinion-spread event is not used to change the future law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseNineContinuation

open TimeTheorem StageEventSpec UniformRecovery StrongContinuationComposition
  PhaseNineContinuationBits PhaseNineContinuationCleanup PhaseOneDrainStopping
  TraceDrain

theorem phase_nine_prefix_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (s : ℕ)
    (A : Set ((k : Finset.Iic s) →
      Draw (PhaseThreeModel.Numeric.hourIndex n) 256))
    (hA : ∀ a ∈ A, (prefixCfg init s a).card = n ∧
      PurePhase 9 (prefixCfg init s a)) :
    law init {ω | frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
      ¬ StableOrSeed init 10
        (trace init ω (s + (logWindow n 12 + logWindow n 3)))} ≤
        ENNReal.ofReal (7 / (n : ℝ) ^ 5) *
          law init {ω | frestrictLe (π := fun _ : ℕ =>
            Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} := by
  classical
  have hn : 2 ≤ n := by
    have := (time_population_bounds hinput.1).2
    omega
  let t := s + logWindow n 12
  let B : Set ((k : Finset.Iic t) →
      Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
    {a | restrictPrefix (by dsimp [t]; omega : s ≤ t) a ∈ A ∧
      PurePhase 9 (prefixCfg init t a) ∧
        UniformOpinions (prefixCfg init t a)}
  have hmass :
      law init {ω | frestrictLe (π := fun _ : ℕ =>
          Draw (PhaseThreeModel.Numeric.hourIndex n) 256) t ω ∈ B} ≤
        law init {ω | frestrictLe (π := fun _ : ℕ =>
          Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} :=
    measure_mono fun ω hω => hω.1
  have hfirst := phase_nine_uniform_prefix_tail init hn s A hA
  have hsecond := (cleanup_prefix_tail init hinput t B
    (fun a ha => ha.2)).trans (mul_le_mul_left' hmass _)
  have hsub :
      {ω | frestrictLe (π := fun _ : ℕ =>
          Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
        ¬ StableOrSeed init 10
          (trace init ω (s + (logWindow n 12 + logWindow n 3)))} ⊆
      {ω | frestrictLe (π := fun _ : ℕ =>
          Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
        ¬ someGE 10 (trace init ω (s + logWindow n 12)) ∧
        ¬ UniformOpinions (trace init ω (s + logWindow n 12))} ∪
      {ω | frestrictLe (π := fun _ : ℕ =>
          Draw (PhaseThreeModel.Numeric.hourIndex n) 256) t ω ∈ B ∧
        ¬ StableOrSeed init 10 (trace init ω (t + logWindow n 3))} := by
    rintro ω ⟨ha, hbad⟩
    have hnoseed : ¬ someGE 10 (trace init ω t) := by
      intro hs
      exact hbad (Or.inr (seed_persists init ω 10 t
        (s + (logWindow n 12 + logWindow n 3))
        (by decide) (by dsimp [t]; omega) hs))
    by_cases hu : UniformOpinions (trace init ω t)
    · have hstart := (hA (frestrictLe s ω) ha).2
      have hlow : ∀ a ∈ trace init ω t, 9 ≤ a.phase.val :=
        phase_lower_reachable 9 _ _
          (trace_reachable init ω (by dsimp [t]; omega))
          (fun a ha' => (hstart a ha').ge)
      have hpure : PurePhase 9 (trace init ω t) := by
        intro a ha'
        have hlo := hlow a ha'
        have hhi : ¬ 10 ≤ a.phase.val := fun h => hnoseed ⟨a, ha', h⟩
        omega
      exact Or.inr ⟨⟨ha, hpure, hu⟩, by
        simpa only [t, Nat.add_assoc] using hbad⟩
    · exact Or.inl ⟨ha, hnoseed, hu⟩
  calc
    _ ≤ law init _ := measure_mono hsub
    _ ≤ law init _ + law init _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (6 / (n : ℝ) ^ 5) *
          law init {ω | frestrictLe (π := fun _ : ℕ =>
            Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} +
        ENNReal.ofReal (1 / (n : ℝ) ^ 5) *
          law init {ω | frestrictLe (π := fun _ : ℕ =>
            Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} :=
      add_le_add hfirst hsecond
    _ = _ := by
      rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 2
      ring

end Ripple.PopulationProtocol.ExactMajority.PhaseNineContinuation

end

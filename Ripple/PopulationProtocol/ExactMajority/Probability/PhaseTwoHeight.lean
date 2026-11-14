import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoHeightDrift
import Ripple.PopulationProtocol.ExactMajority.Probability.TraceGrowthOn

/-!
# Activation height on the original recorded law

At an observed SeedProfile, the probability of an active Clock reaching
16(H) by the activation deadline before backup is at most n^-8. The event
records any such earlier hit: a later backup cannot erase it. The prefix
bound retains the original prefix mass, and the final theorem splices over
an arbitrary PairLogPastTime.

All probabilistic drift inputs are proved for the concrete transition in
PhaseTwoHeightDrift.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

open TimeTheorem PairLog PairLogAuxiliary

theorem activation_height_tail_from_prefix {n : ℕ}
    (init : InputCfg n) (hn : 4 ≤ n) (s : ℕ)
    (A : Set ((k : Finset.Iic s) → Draw (PhaseThreeModel.Numeric.hourIndex n) 256))
    (hA : ∀ p ∈ A, StageEventSpec.SeedProfile n init (prefixCfg init s p)) :
    law init {ω |
        frestrictLe (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
        ∃ u, s ≤ u ∧ u ≤ s + StageEventSpec.activationHorizon n ∧
          HeightBeforeBackup (trace init ω u)} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) *
        law init {ω |
          frestrictLe (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} := by
  have hnTwo : 2 ≤ n := by omega
  have hsize : n ≤ 2 ^ PhaseThreeModel.Numeric.hourIndex n := by
    exact Nat.le_pow_clog (by decide) n
  have hraw := TraceDrain.growth_exit_tail_from_on init
    (HeightDomain n) HeightBeforeBackup killedPotential
    (heightRate n) (one_le_heightRate n)
    (fun c hc => by rw [hc.card_eq]; exact hnTwo)
    (fun c hc hw p => height_domain_step n c hc hw p.1 p.2)
    (fun c hc hw => killedPotential_drift hnTwo c hc hw)
    (heightThreshold (PhaseThreeModel.Numeric.hourIndex n))
    (fun c _ h => height_threshold_le c h)
    s (StageEventSpec.activationHorizon n) A (n : ℝ≥0∞)
    (fun p hp => ⟨seed_height_domain init _ (hA p hp),
      seed_clockPotential_le init _ (hA p hp)⟩)
  have hscalar := activation_height_scalar hn hsize
  have hbound :
      heightThreshold (PhaseThreeModel.Numeric.hourIndex n) *
        law init {ω |
          frestrictLe (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
          ∃ u, s ≤ u ∧ u ≤ s + StageEventSpec.activationHorizon n ∧
            HeightBeforeBackup (trace init ω u)} ≤
      heightThreshold (PhaseThreeModel.Numeric.hourIndex n) *
        (ENNReal.ofReal (1 / (n : ℝ) ^ 8) *
          law init {ω |
            frestrictLe (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A}) := by
    refine hraw.trans ?_
    have h2 := mul_le_mul_right' hscalar (law init {ω |
      frestrictLe (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A})
    simpa only [mul_assoc] using h2
  have hzero : heightThreshold (PhaseThreeModel.Numeric.hourIndex n) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have htop : heightThreshold (PhaseThreeModel.Numeric.hourIndex n) ≠ ⊤ :=
    (ENNReal.pow_lt_top (by norm_num : (2 : ℝ≥0∞) < ⊤)).ne
  have hcancel := mul_le_mul_left' hbound
    (heightThreshold (PhaseThreeModel.Numeric.hourIndex n))⁻¹
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hzero htop, one_mul] using hcancel

def heightWindow {n : ℕ} (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | ∃ u, s ≤ u ∧ u ≤ s + StageEventSpec.activationHorizon n ∧
    HeightBeforeBackup (trace init ω u)}

theorem heightWindow_measurable {n : ℕ} (init : InputCfg n) (s : ℕ) :
    MeasurableSet (heightWindow init s) := by
  have heq : heightWindow init s =
      ⋃ u : {u : ℕ // s ≤ u ∧ u ≤ s + StageEventSpec.activationHorizon n},
        {ω | HeightBeforeBackup (trace init ω u.val)} := by
    ext ω
    simp only [heightWindow, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨u, hsu, hu, hheight⟩
      exact ⟨⟨u, hsu, hu⟩, hheight⟩
    · rintro ⟨u, hheight⟩
      exact ⟨u.val, u.property.1, u.property.2, hheight⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro u
  exact (Set.to_countable {c : InputCfg n | HeightBeforeBackup c}).measurableSet.preimage
    ((measurable_pi_apply u.val).comp (measurable_trace init))

def heightFailureAt {n : ℕ} (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) : Set (InputLog n) :=
  {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
    StageEventSpec.SeedProfile n init (trace init ω s) ∧
    ∃ u, s ≤ u ∧ u ≤ s + StageEventSpec.activationHorizon n ∧
      HeightBeforeBackup (trace init ω u)}

theorem heightFailureAt_measurable {n : ℕ} (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) (hσ : PhaseOneDrain.PairLogPastTime σ) :
    MeasurableSet (heightFailureAt init σ) := by
  have heq : heightFailureAt init σ =
      ⋃ s : ℕ, {ω | σ ω = (s : WithTop ℕ)} ∩
        {ω | StageEventSpec.SeedProfile n init (trace init ω s)} ∩
        heightWindow init s := by
    ext ω
    simp only [heightFailureAt, heightWindow, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨s, hs, hseed, hheight⟩
      exact ⟨s, ⟨⟨hs, hseed⟩, hheight⟩⟩
    · rintro ⟨s, ⟨⟨hs, hseed⟩, hheight⟩⟩
      exact ⟨s, hs, hseed, hheight⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro s
  have htime : MeasurableSet {ω | σ ω = (s : WithTop ℕ)} :=
    (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).le s _ (hσ s)
  have hseed : MeasurableSet
      {ω | StageEventSpec.SeedProfile n init (trace init ω s)} :=
    (Set.to_countable {c : InputCfg n | StageEventSpec.SeedProfile n init c}).measurableSet.preimage
      ((measurable_pi_apply s).comp (measurable_trace init))
  exact (htime.inter hseed).inter (heightWindow_measurable init s)

/-- The historical height-before-backup tail at any genuinely observed
SeedProfile time, on the original pair-log law. -/
theorem activation_height_tail_at_past_time {n : ℕ}
    (init : InputCfg n) (hn : 4 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PhaseOneDrain.PairLogPastTime σ) :
    law init (heightFailureAt init σ) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
  refine genuine_seed_splice (law init) σ (heightFailureAt init σ)
    (ENNReal.ofReal (1 / (n : ℝ) ^ 8))
    (heightFailureAt_measurable init σ hσ)
    (fun s => (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).le s _ (hσ s)) ?_ ?_
  · rintro ω ⟨s, hs, _⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hσs := hσ s
    rw [pairLogFiltration_eq_comap] at hσs
    obtain ⟨Aσ, _, hAσ⟩ := hσs
    let A : Set ((k : Finset.Iic s) → Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
      {p | p ∈ Aσ ∧ StageEventSpec.SeedProfile n init (prefixCfg init s p)}
    have hmem (ω : InputLog n) :
        frestrictLe (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ Aσ ↔
          σ ω = (s : WithTop ℕ) := by
      change ω ∈
        (frestrictLe (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s) ⁻¹' Aσ ↔
        ω ∈ {ω | σ ω = (s : WithTop ℕ)}
      rw [hAσ]
    have htail := activation_height_tail_from_prefix init hn s A (fun p hp => hp.2)
    calc law init (heightFailureAt init σ ∩ {ω | σ ω = (s : WithTop ℕ)}) ≤
        law init {ω |
          frestrictLe (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
          ∃ u, s ≤ u ∧ u ≤ s + StageEventSpec.activationHorizon n ∧
            HeightBeforeBackup (trace init ω u)} := by
          apply measure_mono
          rintro ω ⟨⟨r, hr, hseed, hheight⟩, hs⟩
          have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
          subst r
          exact ⟨⟨(hmem ω).mpr hs, hseed⟩, hheight⟩
      _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 8) *
          law init {ω |
            frestrictLe (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} := htail
      _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 8) *
          law init {ω | σ ω = (s : WithTop ℕ)} :=
        mul_le_mul_left' (measure_mono fun ω hω => (hmem ω).mp hω.1) _

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

end

-- Ripple/PopulationProtocol/ExactMajority/Probability/LateTwoLevelBlock.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTwoLevelService

/-!
# Composing the real warmup and nonlinear service windows

The second window starts after the fixed physical warmup offset. Its
lower-hour debt gate is transported by the proved mixed debt monotonicity.
The warmup failure and service failure are joined under one original-law
prefix event, then spliced over disjoint stopping-time fibres.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open PhaseThreeClockProducer

open TimeTheorem PairLog PhaseOneDrain StageEventSpec
open AveragingMixedLedgers AveragingPotentialService AveragingTerminalDebtDeadlines AveragingHourStops
open AveragingNumerics

variable {L : ℕ}

def twoLevelBlockFailure (init : Cfg L 256) (s : ℕ)
    (σ : Sign) (j : Fin (L + 1)) (n C M : ℕ) : Set (Ω L 256) :=
  {ω | (∀ u, u ≤ clockWarmup n C + twoLevelTrials n M →
      TwoLevelWarmupGate σ j.val n C M (trace init ω (s + u))) ∧
    (∀ u, u ≤ twoLevelTrials n M →
      augmentedPhi j.val (trace init ω (s + clockWarmup n C + u)) ≤
        (1 / 1000 : ℚ) * M) ∧
    twoLevelTarget M <
      twoLevelIndex σ j.val M (trace init ω (s + clockWarmup n C + twoLevelTrials n M))}

theorem twoLevelBlock_failure_subset (init : Cfg L 256) (s : ℕ)
    (σ : Sign) (j : Fin (L + 1)) (n C M : ℕ) :
    twoLevelBlockFailure init s σ j n C M ⊆
      twoLevelWarmupFailure init s σ j.val n C M ∪
        twoLevelServiceFailure init (s + clockWarmup n C) σ j n M := by
  rintro ω ⟨hwindow, hpotential, hbad⟩
  have hgate (v : ℕ) (hsv : s ≤ v)
      (hv : v ≤ s + (clockWarmup n C + twoLevelTrials n M)) :
      TwoLevelWarmupGate σ j.val n C M (trace init ω v) := by
    have h := hwindow (v - s) (by omega)
    have he : s + (v - s) = v := by omega
    simpa only [he] using h
  by_cases hwarm :
      lowerHourDebt σ j.val (trace init ω (s + clockWarmup n C)) ≤
        (9 / 500 : ℚ) * M
  · apply Or.inr
    refine ⟨?_, hbad⟩
    intro u hu
    have hnow := hgate (s + clockWarmup n C + u) (by omega) (by omega)
    refine ⟨hnow.population, hnow.domain, hnow.main_count, hpotential u hu, ?_⟩
    apply lowerHourDebt_after_warmup init ω σ j.val n C M s
      (s + clockWarmup n C + u) (by omega) ?_ hwarm
    intro v hsv hv
    exact (hgate v (by omega) (by omega)).domain
  · apply Or.inl
    exact ⟨fun u hu => hwindow u (by omega), lt_of_not_ge hwarm⟩

/-- One prefix event is retained across the actual physical offset. -/
theorem twoLevelBlock_tail_from (init : Cfg L 256) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L 256))
    (σ : Sign) (j : Fin (L + 1)) (hj : 1 ≤ j.val) (hk : j.val + 1 ≤ L)
    (n C M : ℕ) (hn : 3 ≤ n) (hC : 0 < C) (hM : 0 < M)
    (hroles : C + M ≤ n) (hrole : 25 * M ≤ 13 * n) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ twoLevelBlockFailure init s σ j n C M} ≤
      (ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) +
        ENNReal.ofReal (Real.exp (-(twoLevelTarget M : ℝ) / 6))) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} := by
  let u := s + clockWarmup n C
  let Bnext : Set ((i : Finset.Iic u) → Draw L 256) :=
    {p | TraceDrain.restrictPrefix (by dsimp [u]; omega : s ≤ u) p ∈ B}
  let Efirst : Set (Ω L 256) :=
    {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
      ω ∈ twoLevelWarmupFailure init s σ j.val n C M}
  let Esecond : Set (Ω L 256) :=
    {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) u ω ∈ Bnext ∧
      ω ∈ twoLevelServiceFailure init u σ j n M}
  have hprefix :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) u ω ∈ Bnext} =
        {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} := by
    ext ω
    rfl
  have hfirst := twoLevelWarmup_tail_from init s B σ j.val hk
    n C M (by omega) hC hroles
  have hsecond := twoLevelService_tail_from init u Bnext σ j hj n M hn hM hrole
  rw [hprefix] at hsecond
  have hsubset :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ twoLevelBlockFailure init s σ j n C M} ⊆ Efirst ∪ Esecond := by
    rintro ω ⟨hp, hblock⟩
    rcases twoLevelBlock_failure_subset init s σ j n C M hblock with hfirst | hsecond
    · exact Or.inl ⟨hp, hfirst⟩
    · apply Or.inr
      refine ⟨?_, hsecond⟩
      change TraceDrain.restrictPrefix _
        (frestrictLe (π := fun _ : ℕ => Draw L 256) u ω) ∈ B
      rw [TraceDrain.restrictPrefix_frestrictLe]
      exact hp
  calc
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ twoLevelBlockFailure init s σ j n C M} ≤
        law init Efirst + law init Esecond :=
      (measure_mono hsubset).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} +
        ENNReal.ofReal (Real.exp (-(twoLevelTarget M : ℝ) / 6)) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} :=
      add_le_add hfirst hsecond
    _ = _ := by rw [add_mul]

/-- The starting time is a genuine pair-log past time. The full future gate
window remains an intersection inside the failure event. -/
theorem twoLevelBlock_tail_at_pastTime (init : Cfg L 256)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ)
    (σ : Sign) (j : Fin (L + 1)) (hj : 1 ≤ j.val) (hk : j.val + 1 ≤ L)
    (n C M : ℕ) (hn : 3 ≤ n) (hC : 0 < C) (hM : 0 < M)
    (hroles : C + M ≤ n) (hrole : 25 * M ≤ 13 * n) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ twoLevelBlockFailure init s σ j n C M} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) +
        ENNReal.ofReal (Real.exp (-(twoLevelTarget M : ℝ) / 6)) := by
  let E : Set (Ω L 256) :=
    {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧ ω ∈ twoLevelBlockFailure init s σ j n C M}
  apply PhaseThreeClockProducer.splice_of_local (law init) τ E _
    (fun s => (pairLogFiltration L 256).le s _ (hτ s))
  · rintro ω ⟨s, hs, _⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hτs := hτ s
    rw [pairLogFiltration_eq_comap] at hτs
    obtain ⟨A, hA, hEq⟩ := hτs
    have hmem (ω : Ω L 256) :
        frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A ↔
          τ ω = (s : WithTop ℕ) := by
      change ω ∈ (frestrictLe (π := fun _ : ℕ => Draw L 256) s) ⁻¹' A ↔
        ω ∈ {ω | τ ω = (s : WithTop ℕ)}
      rw [hEq]
    have hevent :
        E ∩ {ω | τ ω = (s : WithTop ℕ)} =
          {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A ∧
            ω ∈ twoLevelBlockFailure init s σ j n C M} := by
      ext ω
      constructor
      · rintro ⟨⟨r, hr, hb⟩, hs⟩
        have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
        subst r
        exact ⟨(hmem ω).mpr hs, hb⟩
      · rintro ⟨ha, hb⟩
        have hs := (hmem ω).mp ha
        exact ⟨⟨s, hs, hb⟩, hs⟩
    rw [hevent]
    have hbound := twoLevelBlock_tail_from init s A σ j hj hk n C M
      hn hC hM hroles hrole
    simpa only [show {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} =
      {ω | τ ω = (s : WithTop ℕ)} from Set.ext hmem] using hbound

theorem twoLevelBlock_error_le_inverse_power {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) :
    ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) +
        ENNReal.ofReal (Real.exp (-(twoLevelTarget M : ℝ) / 6)) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 20) := by
  have hfirst : Real.exp (-(M : ℝ) / 500) ≤ 1 / (n : ℝ) ^ 20 := by
    calc
      Real.exp (-(M : ℝ) / 500) ≤ Real.exp (-(M : ℝ) / 1000) :=
        Real.exp_le_exp.mpr (by have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith)
      _ ≤ 1 / (n : ℝ) ^ 20 := mass_tail_le_inverse_power hn hmain
  have hsecond := two_level_service_tail_le_inverse_power hn hmain
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have e2 : (2 : ℝ) / (n : ℝ) ^ 20 = 1 / (n : ℝ) ^ 20 + 1 / (n : ℝ) ^ 20 := by ring
  linarith [e2]

theorem twoLevelBlock_tail_calibrated (init : Cfg L 256)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ)
    (σ : Sign) (j : Fin (L + 1)) (hj : 1 ≤ j.val) (hk : j.val + 1 ≤ L)
    (n C M : ℕ) (hn : timePopulationThreshold ≤ n) (hC : 0 < C)
    (hroles : C + M ≤ n) (hlower : 12 * n ≤ 25 * M)
    (hupper : 25 * M ≤ 13 * n) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ twoLevelBlockFailure init s σ j n C M} ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 20) := by
  have hnforty : 40 ≤ n := (time_population_bounds hn).2
  exact (twoLevelBlock_tail_at_pastTime init τ hτ σ j hj hk n C M
    (by omega) hC (by omega) hroles hupper).trans
      (twoLevelBlock_error_le_inverse_power hn hlower)

theorem twoLevelBlock_tail_at_phaseThreeSeed {n : ℕ} (init : InputCfg n)
    (σ : Sign) (j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hj : 1 ≤ j.val) (hk : j.val + 1 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (C M : ℕ) (hn : 3 ≤ n) (hC : 0 < C) (hM : 0 < M)
    (hroles : C + M ≤ n) (hrole : 25 * M ≤ 13 * n) :
    law init {ω | ∃ s : ℕ,
        hourStart init (seedTime init 3) (j.val + 1) ω = (s : WithTop ℕ) ∧
        ω ∈ twoLevelBlockFailure init s σ j n C M} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) +
        ENNReal.ofReal (Real.exp (-(twoLevelTarget M : ℝ) / 6)) :=
  twoLevelBlock_tail_at_pastTime init (hourStart init (seedTime init 3) (j.val + 1))
    (hourStart_phaseThreeSeed_pastTime init (j.val + 1)) σ j hj hk
    n C M hn hC hM hroles hrole

/-- A successful history identifies the independently defined start time.
It is intersected with the failure, never used as a conditional law. -/
theorem twoLevelBlock_tail_on_clockHistory {n : ℕ} (init : InputCfg n)
    (σ : Sign) (j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hj : 1 ≤ j.val) (hk : j.val + 1 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (C M : ℕ) (hn : 3 ≤ n) (hC : 0 < C) (hM : 0 < M)
    (hroles : C + M ≤ n) (hrole : 25 * M ≤ 13 * n) :
    law init {ω | ∃ (S T ρ : ℕ) (w : ClockTimes init),
        ClockHistory init ω S T ρ w ∧
        ω ∈ twoLevelBlockFailure init (w.start (j.val + 1)) σ j n C M} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) +
        ENNReal.ofReal (Real.exp (-(twoLevelTarget M : ℝ) / 6)) := by
  refine (measure_mono ?_).trans
    (twoLevelBlock_tail_at_phaseThreeSeed init σ j hj hk C M hn hC hM hroles hrole)
  rintro ω ⟨S, T, ρ, w, hc, hf⟩
  exact ⟨w.start (j.val + 1),
    hourStart_phaseThreeSeed_clockHistory hc (j.val + 1) hk, hf⟩

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end

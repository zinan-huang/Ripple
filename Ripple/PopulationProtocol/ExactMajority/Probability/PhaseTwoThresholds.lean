import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrain
import Ripple.PopulationProtocol.ExactMajority.Probability.TraceDrain
import Ripple.PopulationProtocol.ExactMajority.Probability.StageEventSpec
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Phase thresholds from recorded stopping-time prefixes

The endpoint tower retains the complete pair-log prefix. Threshold completion
is one component of asynchronous entry; the separate clock-height and
Main-index fields of AdvancedProfile are not asserted here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoThresholds

open TimeTheorem PairLog TraceDrain PhaseOneDrain

variable {L K : ℕ}

theorem lintegral_recorded_future
    (init : Cfg L K) (s N : ℕ)
    (F : ((k : Finset.Iic s) → Draw L K) → Cfg L K → ℝ≥0∞) :
    (∫⁻ ω, F (frestrictLe (π := fun _ : ℕ => Draw L K) s ω)
        (trace init ω (s + N)) ∂law init) =
      ∫⁻ ω, (∫⁻ c', F (frestrictLe (π := fun _ : ℕ => Draw L K) s ω) c'
        ∂((NonuniformMajority L K).transitionKernel ^ N) (trace init ω s))
        ∂law init := by
  induction N generalizing F with
  | zero =>
      simp only [Nat.add_zero, pow_zero]
      apply lintegral_congr
      intro ω
      rw [show (1 : Kernel (Cfg L K) (Cfg L K)) = Kernel.id from rfl, Kernel.id_apply,
        lintegral_dirac' _ (measurable_of_countable _)]
  | succ N ih =>
      let G : ((k : Finset.Iic (s + N)) → Draw L K) → Draw L K → ℝ≥0∞ :=
        fun p d => F (restrictPrefix (Nat.le_add_right s N) p)
          (applyDraw (prefixCfg init (s + N) p) d)
      let H : ((k : Finset.Iic s) → Draw L K) → Cfg L K → ℝ≥0∞ :=
        fun p c => ∫⁻ c', F p c' ∂(NonuniformMajority L K).transitionKernel c
      calc
        (∫⁻ ω, F (frestrictLe (π := fun _ : ℕ => Draw L K) s ω)
            (trace init ω (s + (N + 1))) ∂law init) =
            ∫⁻ ω, G (frestrictLe (π := fun _ : ℕ => Draw L K) (s + N) ω)
              (ω (s + N + 1)) ∂law init := by
          apply lintegral_congr
          intro ω
          change F (frestrictLe (π := fun _ : ℕ => Draw L K) s ω)
              (trace init ω (s + (N + 1))) =
            F (frestrictLe (π := fun _ : ℕ => Draw L K) s ω)
              (applyDraw (trace init ω (s + N)) (ω (s + N + 1)))
          rw [show s + (N + 1) = s + N + 1 by omega, TimeTheorem.trace_succ]
        _ = ∫⁻ ω, (∫⁻ d, G (frestrictLe (π := fun _ : ℕ => Draw L K) (s + N) ω) d
              ∂pairKernel init (s + N)
                (frestrictLe (π := fun _ : ℕ => Draw L K) (s + N) ω)) ∂law init :=
          lintegral_prefix_next init (s + N) G
        _ = ∫⁻ ω, H (frestrictLe (π := fun _ : ℕ => Draw L K) s ω)
              (trace init ω (s + N)) ∂law init := by
          apply lintegral_congr
          intro ω
          dsimp only [G, H]
          rw [restrictPrefix_frestrictLe]
          exact lintegral_pairKernel_applyDraw init (s + N) _
            (F (frestrictLe (π := fun _ : ℕ => Draw L K) s ω))
        _ = ∫⁻ ω, (∫⁻ c', H (frestrictLe (π := fun _ : ℕ => Draw L K) s ω) c'
              ∂((NonuniformMajority L K).transitionKernel ^ N) (trace init ω s))
              ∂law init := ih H
        _ = ∫⁻ ω, (∫⁻ c', F (frestrictLe (π := fun _ : ℕ => Draw L K) s ω) c'
              ∂((NonuniformMajority L K).transitionKernel ^ (N + 1))
                (trace init ω s)) ∂law init := by
          apply lintegral_congr
          intro ω
          dsimp only [H]
          first
            | rw [pow_succ' (NonuniformMajority L K).transitionKernel N, Kernel.mul_def,
                Kernel.lintegral_comp _ _ _ (measurable_of_countable _)]
            | rw [pow_succ' (NonuniformMajority L K).transitionKernel N,
                show (NonuniformMajority L K).transitionKernel *
                    (NonuniformMajority L K).transitionKernel ^ N =
                  (NonuniformMajority L K).transitionKernel ∘ₖ
                    ((NonuniformMajority L K).transitionKernel ^ N) from rfl,
                Kernel.lintegral_comp _ _ _ (measurable_of_countable _)]
            | rw [pow_succ (NonuniformMajority L K).transitionKernel N,
                show (NonuniformMajority L K).transitionKernel ^ N *
                    (NonuniformMajority L K).transitionKernel =
                  (NonuniformMajority L K).transitionKernel ∘ₖ
                    ((NonuniformMajority L K).transitionKernel ^ N) from rfl,
                Kernel.lintegral_comp _ _ _ (measurable_of_countable _)]

open Classical in
theorem recorded_prefix_endpoint_bound
    (init : Cfg L K) (s N : ℕ)
    (A : Set ((k : Finset.Iic s) → Draw L K))
    (B : Set (Cfg L K)) (ε : ℝ≥0∞)
    (hbound : ∀ p ∈ A,
      ((NonuniformMajority L K).transitionKernel ^ N) (prefixCfg init s p) B ≤ ε) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        trace init ω (s + N) ∈ B} ≤
      ε * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  let E : Set (Ω L K) :=
    {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}
  let D : Set (Ω L K) := {ω | trace init ω (s + N) ∈ B}
  let F : ((k : Finset.Iic s) → Draw L K) → Cfg L K → ℝ≥0∞ :=
    fun p c => if p ∈ A then B.indicator (fun _ => 1) c else 0
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  have hE : MeasurableSet E :=
    hA.preimage (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) s)
  have hD : MeasurableSet D :=
    hB.preimage ((measurable_pi_apply (s + N)).comp (measurable_trace init))
  have hleft :
      (fun ω => F (frestrictLe (π := fun _ : ℕ => Draw L K) s ω)
        (trace init ω (s + N))) =
      (E ∩ D).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A <;>
      by_cases hb : trace init ω (s + N) ∈ B <;>
      simp [F, E, D, ha, hb]
  have hpoint (ω : Ω L K) :
      (∫⁻ c', F (frestrictLe (π := fun _ : ℕ => Draw L K) s ω) c'
        ∂((NonuniformMajority L K).transitionKernel ^ N) (trace init ω s)) ≤
      E.indicator (fun _ => ε) ω := by
    by_cases ha : frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A
    · rw [Set.indicator_of_mem (show ω ∈ E from ha)]
      simp only [F, if_pos ha]
      rw [lintegral_indicator_const hB 1, one_mul]
      exact hbound _ ha
    · rw [Set.indicator_of_notMem (show ω ∉ E from ha)]
      simp only [F, if_neg ha, lintegral_zero, le_refl]
  change law init (E ∩ D) ≤ ε * law init E
  calc
    law init (E ∩ D) =
        ∫⁻ ω, F (frestrictLe (π := fun _ : ℕ => Draw L K) s ω)
          (trace init ω (s + N)) ∂law init := by
      rw [hleft, lintegral_indicator_const (hE.inter hD) 1, one_mul]
    _ = ∫⁻ ω, (∫⁻ c', F (frestrictLe (π := fun _ : ℕ => Draw L K) s ω) c'
          ∂((NonuniformMajority L K).transitionKernel ^ N) (trace init ω s))
          ∂law init := lintegral_recorded_future init s N F
    _ ≤ ∫⁻ ω, E.indicator (fun _ => ε) ω ∂law init := lintegral_mono hpoint
    _ = ε * law init E := lintegral_indicator_const hE ε

noncomputable def thresholdBudget (n N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-(N : ℝ) / (n : ℝ)) * (Real.exp 3 * (n : ℝ)))

theorem threshold_spread_from_prefix
    (init : Cfg L K) {n : ℕ} (hn : 2 ≤ n)
    (q : ℕ) (hq : 1 ≤ q) (s N : ℕ)
    (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A, (prefixCfg init s p).card = n ∧
      ∃ a ∈ prefixCfg init s p, q ≤ a.phase.val) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ¬ ∀ a ∈ trace init ω (s + N), q ≤ a.phase.val} ≤
      thresholdBudget n N *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  exact recorded_prefix_endpoint_bound init s N A
    {c | ¬ ∀ a ∈ c, q ≤ a.phase.val} (thresholdBudget n N)
    (fun p hp => ThresholdEpidemic.threshold_kernel_sharp_tail
      hn q hq _ (hA p hp).1 (hA p hp).2 N)

def thresholdFailureAt (init : Cfg L K) (n q N : ℕ)
    (σ : Ω L K → WithTop ℕ) : Set (Ω L K) :=
  {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
    (trace init ω s).card = n ∧
    (∃ a ∈ trace init ω s, q ≤ a.phase.val) ∧
    ¬ ∀ a ∈ trace init ω (s + N), q ≤ a.phase.val}

theorem thresholdFailureAt_measurable
    (init : Cfg L K) (n q N : ℕ)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ) :
    MeasurableSet (thresholdFailureAt init n q N σ) := by
  have heq : thresholdFailureAt init n q N σ =
      ⋃ s : ℕ, {ω | σ ω = (s : WithTop ℕ)} ∩
        {ω | (trace init ω s).card = n ∧
          ∃ a ∈ trace init ω s, q ≤ a.phase.val} ∩
        {ω | ¬ ∀ a ∈ trace init ω (s + N), q ≤ a.phase.val} := by
    ext ω
    simp only [thresholdFailureAt, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨s, hs, hc, ha, hb⟩
      exact ⟨s, ⟨⟨hs, hc, ha⟩, hb⟩⟩
    · rintro ⟨s, ⟨⟨hs, hc, ha⟩, hb⟩⟩
      exact ⟨s, hs, hc, ha, hb⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro s
  have htime : MeasurableSet {ω | σ ω = (s : WithTop ℕ)} :=
    (pairLogFiltration L K).le s _ (hσ s)
  have hseed : MeasurableSet
      {ω | (trace init ω s).card = n ∧
        ∃ a ∈ trace init ω s, q ≤ a.phase.val} :=
    (Set.to_countable {c : Cfg L K | c.card = n ∧
      ∃ a ∈ c, q ≤ a.phase.val}).measurableSet.preimage
        ((measurable_pi_apply s).comp (measurable_trace init))
  have hbad : MeasurableSet
      {ω | ¬ ∀ a ∈ trace init ω (s + N), q ≤ a.phase.val} :=
    (Set.to_countable {c : Cfg L K | ¬ ∀ a ∈ c, q ≤ a.phase.val}).measurableSet.preimage
      ((measurable_pi_apply (s + N)).comp (measurable_trace init))
  exact (htime.inter hseed).inter hbad

theorem threshold_spread_at_past_time
    (init : Cfg L K) {n : ℕ} (hn : 2 ≤ n)
    (q : ℕ) (hq : 1 ≤ q) (N : ℕ)
    (σ : Ω L K → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init (thresholdFailureAt init n q N σ) ≤ thresholdBudget n N := by
  refine genuine_seed_splice (law init) σ
    (thresholdFailureAt init n q N σ) (thresholdBudget n N)
    (thresholdFailureAt_measurable init n q N σ hσ)
    (fun s => (pairLogFiltration L K).le s _ (hσ s)) ?_ ?_
  · rintro ω ⟨s, hs, _⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hσs := hσ s
    rw [pairLogFiltration_eq_comap] at hσs
    obtain ⟨Aσ, _, hAσ⟩ := hσs
    let A : Set ((k : Finset.Iic s) → Draw L K) :=
      {p | p ∈ Aσ ∧ (prefixCfg init s p).card = n ∧
        ∃ a ∈ prefixCfg init s p, q ≤ a.phase.val}
    have hmem (ω : Ω L K) :
        frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ Aσ ↔
          σ ω = (s : WithTop ℕ) := by
      change ω ∈ (frestrictLe (π := fun _ : ℕ => Draw L K) s) ⁻¹' Aσ ↔
        ω ∈ {ω | σ ω = (s : WithTop ℕ)}
      rw [hAσ]
    have htail := threshold_spread_from_prefix init hn q hq s N A
      (fun p hp => hp.2)
    calc
      law init (thresholdFailureAt init n q N σ ∩ {ω | σ ω = (s : WithTop ℕ)}) ≤
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
            ¬ ∀ a ∈ trace init ω (s + N), q ≤ a.phase.val} := by
        apply measure_mono
        rintro ω ⟨⟨r, hr, hc, ha, hb⟩, hs⟩
        have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
        subst r
        exact ⟨⟨(hmem ω).mpr hs, hc, ha⟩, hb⟩
      _ ≤ thresholdBudget n N *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := htail
      _ ≤ thresholdBudget n N * law init {ω | σ ω = (s : WithTop ℕ)} :=
        mul_le_mul_left' (measure_mono fun ω hω => (hmem ω).mp hω.1) _

theorem threshold_spread_logWindow_at_past_time
    {n : ℕ} (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (q : ℕ) (hq : 1 ≤ q) (u : ℕ)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init (thresholdFailureAt init n q (logWindow n u) σ) ≤
      ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (1 - (u : ℝ))) := by
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  exact (threshold_spread_at_past_time init (by omega) q hq
    (logWindow n u) σ hσ).trans
      (ENNReal.ofReal_le_ofReal (ThresholdEpidemic.epidemic_logWindow_bound (by omega) u))

theorem thresholdBudget_le_of_horizon {n N : ℕ} (hn : 0 < n)
    (u : ℝ) (hN : u * (n : ℝ) * Real.log (n : ℝ) ≤ (N : ℝ)) :
    thresholdBudget n N ≤
      ENNReal.ofReal (Real.exp 3 * (n : ℝ) ^ (1 - u)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hquot : u * Real.log (n : ℝ) ≤ (N : ℝ) / (n : ℝ) := by
    apply (le_div_iff₀ hnpos).2
    nlinarith only [hN]
  have hneg : -(N : ℝ) / (n : ℝ) ≤ -u * Real.log (n : ℝ) := by
    simpa only [neg_div, neg_mul] using neg_le_neg hquot
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.exp (-(N : ℝ) / (n : ℝ)) * (Real.exp 3 * (n : ℝ)) ≤
        Real.exp (-u * Real.log (n : ℝ)) * (Real.exp 3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hneg) (by positivity)
    _ = Real.exp 3 *
        (Real.exp (Real.log (n : ℝ)) * Real.exp (-u * Real.log (n : ℝ))) := by
      rw [Real.exp_log hnpos]
      ring
    _ = Real.exp 3 *
        Real.exp (Real.log (n : ℝ) + (-u * Real.log (n : ℝ))) := by
      rw [Real.exp_add]
    _ = Real.exp 3 * Real.exp (Real.log (n : ℝ) * (1 - u)) := by
      congr 2
      ring
    _ = Real.exp 3 * (n : ℝ) ^ (1 - u) := by
      rw [Real.rpow_def_of_pos hnpos]

/-- Threshold activation only; the separate height failure is not included. -/
theorem activation_thresholdBudget_le {n : ℕ} (hn : 2 ≤ n) :
    thresholdBudget n (StageEventSpec.activationHorizon n) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 5) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hceil : (6 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤ (logWindow n 6 : ℝ) := by
    unfold logWindow
    exact Nat.le_ceil _
  have htime : (12 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤
      (StageEventSpec.activationHorizon n : ℝ) := by
    unfold StageEventSpec.activationHorizon
    push_cast
    nlinarith only [hceil]
  have hsharp := thresholdBudget_le_of_horizon (by omega : 0 < n) (12 : ℝ) htime
  have hexp : Real.exp (3 : ℝ) ≤ 27 := by
    calc
      Real.exp (3 : ℝ) = (Real.exp 1) ^ 3 := by
        rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
        ring
      _ ≤ (3 : ℝ) ^ 3 := by
        gcongr
        exact Real.exp_one_lt_three.le
      _ = 27 := by norm_num
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (64 : ℝ) ≤ (n : ℝ) ^ 6 := by
    calc
      (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (n : ℝ) ^ 6 := by gcongr
  have hmul : Real.exp 3 * (n : ℝ) ^ 5 ≤ 2 * (n : ℝ) ^ 11 := by
    have hfactor : Real.exp 3 ≤ 2 * (n : ℝ) ^ 6 := by linarith
    have h := mul_le_mul_of_nonneg_right hfactor (pow_nonneg hnpos.le 5)
    nlinarith only [h]
  have hratio : Real.exp 3 / (n : ℝ) ^ 11 ≤ 2 / (n : ℝ) ^ 5 :=
    (div_le_div_iff₀ (pow_pos hnpos 11) (pow_pos hnpos 5)).2 hmul
  refine hsharp.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [show (1 : ℝ) - 12 = -(11 : ℝ) by norm_num,
    Real.rpow_neg hnpos.le (11 : ℝ),
    show (n : ℝ) ^ (11 : ℝ) = (n : ℝ) ^ (11 : ℕ) by exact_mod_cast Real.rpow_natCast (n : ℝ) 11]
  simpa only [div_eq_mul_inv] using hratio

theorem seed_profile_activation_threshold_tail
    {n : ℕ} (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
        firstPhaseSeed init 3 s ω ∧
        StageEventSpec.SeedProfile n init (trace init ω s) ∧
        ¬ StageEventSpec.allGE 3
          (trace init ω (s + StageEventSpec.activationHorizon n))} ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 5) := by
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  have hsub : {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
        firstPhaseSeed init 3 s ω ∧
        StageEventSpec.SeedProfile n init (trace init ω s) ∧
        ¬ StageEventSpec.allGE 3
          (trace init ω (s + StageEventSpec.activationHorizon n))} ⊆
      thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n) σ := by
    rintro ω ⟨s, hs, hfirst, hp, hbad⟩
    obtain ⟨a, ha, hpa⟩ := hfirst.1
    exact ⟨s, hs, hp.card_eq, ⟨a, ha, hpa.ge⟩, hbad⟩
  exact (measure_mono hsub).trans
    ((threshold_spread_at_past_time init (by omega) 3 (by decide)
      (StageEventSpec.activationHorizon n) σ hσ).trans
        (activation_thresholdBudget_le (by omega)))

/-- A completed threshold epidemic after a genuine seed has a genuine global
first all-threshold time in the same interval. -/
theorem exists_first_all_after_first_seed
    (init : Cfg L K) (ω : Ω L K) (n q s N : ℕ)
    (hn : 0 < n) (hcard : (trace init ω s).card = n)
    (hfirst : firstPhaseSeed init q s ω)
    (hend : ∀ a ∈ trace init ω (s + N), q ≤ a.phase.val) :
    ∃ t : ℕ,
      StageEventSpec.firstHit (fun c : Cfg L K => ∀ a ∈ c, q ≤ a.phase.val)
        (trace init ω) t ∧ s ≤ t ∧ t ≤ s + N := by
  classical
  have hex : ∃ t : ℕ, ∀ a ∈ trace init ω t, q ≤ a.phase.val := ⟨s + N, hend⟩
  let t : ℕ := Nat.find hex
  have ht : StageEventSpec.firstHit
      (fun c : Cfg L K => ∀ a ∈ c, q ≤ a.phase.val) (trace init ω) t :=
    ⟨Nat.find_spec hex, fun u hu => Nat.find_min hex hu⟩
  have hst : s ≤ t := by
    by_contra h
    have hlt : t < s := Nat.lt_of_not_ge h
    have hct : (trace init ω t).card = n :=
      (Protocol.reachable_card_eq (trace_reachable init ω hlt.le)).symm.trans hcard
    have hpos : 0 < (trace init ω t).card := by rw [hct]; exact hn
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
    exact (Nat.not_le_of_gt (hfirst.2 t hlt a ha)) (ht.1 a ha)
  exact ⟨t, ht, hst, Nat.find_min' hex hend⟩

/-- The first all-threshold time is a stopping time for the pair-log past. -/
theorem first_all_threshold_isStoppingTime (init : Cfg L K) (q : ℕ) :
    IsStoppingTime (pairLogFiltration L K)
      (TraceDrain.exitTime init (fun c => ∀ a ∈ c, q ≤ a.phase.val)) :=
  TraceDrain.exitTime_isStoppingTime init (fun c => ∀ a ∈ c, q ≤ a.phase.val)

/-- This produces the genuine first all-threshold endpoint. It still does not
assert AdvancedProfile, since threshold infection may also include backup. -/
theorem seed_profile_first_activation_threshold_tail
    {n : ℕ} (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
        firstPhaseSeed init 3 s ω ∧
        StageEventSpec.SeedProfile n init (trace init ω s) ∧
        ¬ ∃ t : ℕ,
          StageEventSpec.firstHit (StageEventSpec.allGE (n := n) 3)
            (trace init ω) t ∧
          s ≤ t ∧ t ≤ s + StageEventSpec.activationHorizon n} ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 5) := by
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  refine (measure_mono ?_).trans
    (seed_profile_activation_threshold_tail init hinput σ hσ)
  rintro ω ⟨s, hs, hfirst, hp, hmiss⟩
  refine ⟨s, hs, hfirst, hp, ?_⟩
  intro hend
  exact hmiss (exists_first_all_after_first_seed init ω n 3 s
    (StageEventSpec.activationHorizon n) (by omega) hp.card_eq hfirst hend)

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoThresholds

end

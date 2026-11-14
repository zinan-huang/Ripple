import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Model
import Ripple.PopulationProtocol.ExactMajority.Probability.FastExpectedTime
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Real

/-!
# Assembly of the reviewed Doty stabilization-time estimates

The sample space records occurrence-pair draws, including interactions invisible
in the configuration trace. Coordinate zero is a dummy; coordinate t + 1 drives
the transition from configuration t to configuration t + 1.

This file proves the execution/hitting-time scaffolding, numerical budgets, and
conditional assembly. It does not assert the missing protocol producers. The
concrete instantiation of StageEvents and the named phase estimates are explicit
inputs to dotyTimeClaim_of_estimates.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.TimeTheorem

open PhaseThreeModel.OccurrenceScheduler

attribute [local instance] Classical.propDecidable

abbrev Cfg (L K : ℕ) := Config (AgentState L K)

abbrev Draw (L K : ℕ) :=
  Option (OccurrencePair (AgentState L K))

noncomputable instance drawMeasurableSpace (L K : ℕ) :
    MeasurableSpace (Draw L K) := ⊤

noncomputable instance drawMeasurableSingletonClass (L K : ℕ) :
    MeasurableSingletonClass (Draw L K) :=
  ⟨fun _ => trivial⟩

abbrev Ω (L K : ℕ) := ℕ → Draw L K

variable {L K : ℕ}

noncomputable def drawLaw (c : Cfg L K) : PMF (Draw L K) :=
  if hc : 2 ≤ c.card then
    (occurrencePairLaw c hc).map some
  else
    PMF.pure none

noncomputable def applyDraw (c : Cfg L K) : Draw L K → Cfg L K
  | none => c
  | some p =>
      Protocol.scheduledStep (NonuniformMajority L K) c
        (occurrenceStatePair p)

noncomputable def prefixCfg (init : Cfg L K) :
    (t : ℕ) → ((i : Finset.Iic t) → Draw L K) → Cfg L K
  | 0, _ => init
  | t + 1, p =>
      let prev := prefixCfg init t (fun k =>
        p ⟨k.val, Finset.mem_Iic.mpr
          (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ t))⟩)
      applyDraw prev (p ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩)

noncomputable def trace (init : Cfg L K) (ω : Ω L K) :
    Phase3GoodClock.Trace L K :=
  fun t => prefixCfg init t (frestrictLe t ω)

noncomputable def pairKernel (init : Cfg L K) (t : ℕ) :
    Kernel ((i : Finset.Iic t) → Draw L K) (Draw L K) :=
  Kernel.ofFunOfCountable
    (fun p => (drawLaw (prefixCfg init t p)).toMeasure)

instance pairKernel_isMarkov (init : Cfg L K) (t : ℕ) :
    IsMarkovKernel (pairKernel init t) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure
      ((drawLaw (prefixCfg init t p)).toMeasure)
    infer_instance

noncomputable def law (init : Cfg L K) : Measure (Ω L K) :=
  Kernel.trajFun (X := fun _ => Draw L K)
    (fun t => pairKernel init t) 0 (fun _ => none)

instance law_isProbability (init : Cfg L K) :
    IsProbabilityMeasure (law init) :=
  Kernel.isProbabilityMeasure_trajFun (X := fun _ => Draw L K)
    (fun t => pairKernel init t) 0 (fun _ => none)

theorem measurable_prefixCfg (init : Cfg L K) (t : ℕ) :
    Measurable (prefixCfg init t) := by
  intro A hA
  exact (Set.to_countable _).measurableSet

theorem measurable_trace (init : Cfg L K) :
    Measurable (trace init) := by
  apply measurable_pi_lambda
  intro t
  exact (measurable_prefixCfg init t).comp (measurable_frestrictLe t)

@[simp] theorem trace_zero (init : Cfg L K) (ω : Ω L K) :
    trace init ω 0 = init := rfl

@[simp] theorem trace_succ (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    trace init ω (t + 1) =
      applyDraw (trace init ω t) (ω (t + 1)) := by
  rfl

theorem drawLaw_projects (c : Cfg L K) :
    (drawLaw c).map (applyDraw c) =
      (NonuniformMajority L K).stepDistOrSelf c := by
  classical
  by_cases hc : 2 ≤ c.card
  · simp only [drawLaw, Protocol.stepDistOrSelf, dif_pos hc]
    calc
      ((occurrencePairLaw c hc).map some).map (applyDraw c) =
          ((occurrencePairLaw c hc).map occurrenceStatePair).map
            (Protocol.scheduledStep (NonuniformMajority L K) c) := by
        simp only [PMF.map_comp, Function.comp_def, applyDraw]
      _ = (NonuniformMajority L K).stepDist c hc := by
        simp only [occurrence_pair_state_law, Protocol.stepDist]
  · simp [drawLaw, Protocol.stepDistOrSelf, hc, PMF.pure_map, applyDraw]

theorem law_prefix (init : Cfg L K) (T : ℕ)
    (A : Set ((i : Finset.Iic T) → Draw L K)) :
    law init {ω | frestrictLe T ω ∈ A} =
      Kernel.partialTraj (X := fun _ => Draw L K)
        (fun t => pairKernel init t) 0 T (fun _ => none) A := by
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  change law init (frestrictLe T ⁻¹' A) = _
  rw [← Measure.map_apply (measurable_frestrictLe T) hA]
  have hLawTraj :
      law init =
        Kernel.traj (X := fun _ => Draw L K)
          (fun t => pairKernel init t) 0 (fun _ => none) := rfl
  rw [hLawTraj, Kernel.traj_map_frestrictLe_apply]

/-! ## The actual first hitting time -/

def hitBy (init : Cfg L K) (T : ℕ) : Set (Ω L K) :=
  {ω | ∃ t ≤ T, trace init ω t ∈ StableDone L K init}

noncomputable def τ_D (init : Cfg L K) (ω : Ω L K) : ℝ≥0∞ :=
  if h : ∃ t : ℕ, trace init ω t ∈ StableDone L K init then
    (Nat.find h : ℝ≥0∞)
  else ⊤

theorem hitBy_mono (init : Cfg L K) {s t : ℕ} (hst : s ≤ t) :
    hitBy init s ⊆ hitBy init t := by
  rintro ω ⟨u, hu, hd⟩
  exact ⟨u, hu.trans hst, hd⟩

theorem τ_D_le_iff (init : Cfg L K) (ω : Ω L K) (T : ℕ) :
    τ_D init ω ≤ (T : ℝ≥0∞) ↔ ω ∈ hitBy init T := by
  classical
  by_cases h : ∃ t : ℕ, trace init ω t ∈ StableDone L K init
  · rw [τ_D, dif_pos h]
    constructor
    · intro hT
      refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
      exact_mod_cast hT
    · rintro ⟨t, ht, hdone⟩
      exact_mod_cast (Nat.find_min' h hdone).trans ht
  · rw [τ_D, dif_neg h]
    constructor
    · intro hT
      exact False.elim
        ((ENNReal.natCast_ne_top T) (top_le_iff.mp hT))
    · rintro ⟨t, _, hdone⟩
      exact False.elim (h ⟨t, hdone⟩)

theorem τ_D_tail_set (init : Cfg L K) (T : ℕ) :
    {ω | (T : ℝ≥0∞) < τ_D init ω} = (hitBy init T)ᶜ := by
  ext ω
  change ((T : ℝ≥0∞) < τ_D init ω) ↔ ¬ ω ∈ hitBy init T
  rw [← τ_D_le_iff]
  exact lt_iff_not_ge

theorem measurableSet_hitBy (init : Cfg L K) (T : ℕ) :
    MeasurableSet (hitBy init T) := by
  have heq :
      hitBy init T =
        ⋃ t : ℕ,
          {ω | t ≤ T ∧ trace init ω t ∈ StableDone L K init} := by
    ext ω
    simp [hitBy]
  rw [heq]
  apply MeasurableSet.iUnion
  intro t
  by_cases ht : t ≤ T
  · simpa only [ht, true_and] using
      (measurableSet_StableDone L K init).preimage
        ((measurable_pi_apply t).comp (measurable_trace init))
  · simp only [ht, false_and, Set.setOf_false]
    exact MeasurableSet.empty

theorem τ_D_eq_iInf (init : Cfg L K) (ω : Ω L K) :
    τ_D init ω =
      ⨅ t : ℕ,
        if trace init ω t ∈ StableDone L K init
        then (t : ℝ≥0∞) else ⊤ := by
  classical
  by_cases h : ∃ t : ℕ, trace init ω t ∈ StableDone L K init
  · rw [τ_D, dif_pos h]
    apply le_antisymm
    · apply le_iInf
      intro t
      by_cases ht : trace init ω t ∈ StableDone L K init
      · rw [if_pos ht]
        exact_mod_cast (Nat.find_min' h ht)
      · rw [if_neg ht]
        exact le_top
    · apply iInf_le_of_le (Nat.find h)
      rw [if_pos (Nat.find_spec h)]
  · rw [τ_D, dif_neg h]
    apply le_antisymm
    · apply le_iInf
      intro t
      have ht : trace init ω t ∉ StableDone L K init :=
        fun ht => h ⟨t, ht⟩
      rw [if_neg ht]
    · exact le_top

theorem measurable_τ_D (init : Cfg L K) :
    Measurable (τ_D init) := by
  classical
  have heq : τ_D init = fun ω =>
      ⨅ t : ℕ,
        if trace init ω t ∈ StableDone L K init
        then (t : ℝ≥0∞) else ⊤ :=
    funext (τ_D_eq_iInf init)
  rw [heq]
  change Measurable (fun ω =>
    ⨆ t : ℕ, (show OrderDual ℝ≥0∞ from
      if trace init ω t ∈ StableDone L K init
      then (t : ℝ≥0∞) else (⊤ : ℝ≥0∞)))
  apply Measurable.iSup
  intro t
  exact Measurable.ite
    ((measurableSet_StableDone L K init).preimage
      ((measurable_pi_apply t).comp (measurable_trace init)))
    measurable_const measurable_const

theorem applyDraw_reachable (c : Cfg L K) (o : Draw L K) :
    (NonuniformMajority L K).Reachable c (applyDraw c o) := by
  cases o with
  | none => exact Relation.ReflTransGen.refl
  | some p =>
      exact Protocol.reachable_stepOrSelf c p.1.1 p.2.1

theorem trace_reachable (init : Cfg L K) (ω : Ω L K)
    {s t : ℕ} (hst : s ≤ t) :
    (NonuniformMajority L K).Reachable
      (trace init ω s) (trace init ω t) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  clear hst
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
      rw [show s + (k + 1) = (s + k) + 1 by omega, trace_succ]
      exact Relation.ReflTransGen.trans ih
        (applyDraw_reachable (trace init ω (s + k)) (ω (s + k + 1)))

theorem hitBy_iff_endpoint (init : Cfg L K) (ω : Ω L K) (T : ℕ) :
    ω ∈ hitBy init T ↔ trace init ω T ∈ StableDone L K init := by
  constructor
  · rintro ⟨t, ht, hd⟩
    exact majorityStableEndpoint_preserved_by_reachable
      init (trace init ω t) (trace init ω T) hd
      (trace_reachable init ω ht)
  · intro hd
    exact ⟨T, le_rfl, hd⟩

theorem τ_D_eq_tsum (init : Cfg L K) (ω : Ω L K) :
    τ_D init ω = ∑' t : ℕ,
      if ω ∈ hitBy init t then (0 : ℝ≥0∞) else 1 := by
  classical
  by_cases h : ∃ t : ℕ, trace init ω t ∈ StableDone L K init
  · have hhit (t : ℕ) :
        ω ∈ hitBy init t ↔ Nat.find h ≤ t := by
      rw [← τ_D_le_iff, τ_D, dif_pos h]
      constructor <;> intro ht <;> exact_mod_cast ht
    rw [τ_D, dif_pos h]
    symm
    calc
      (∑' t : ℕ, if ω ∈ hitBy init t then (0 : ℝ≥0∞) else 1) =
          ∑' t : ℕ, if t < Nat.find h then (1 : ℝ≥0∞) else 0 := by
        apply tsum_congr
        intro t
        by_cases ht : Nat.find h ≤ t
        · have hm := (hhit t).2 ht
          simp [hm, Nat.not_lt.mpr ht]
        · have hm : ω ∉ hitBy init t :=
            fun hh => ht ((hhit t).1 hh)
          have hlt : t < Nat.find h := Nat.lt_of_not_ge ht
          simp [hm, hlt]
      _ = ∑ t ∈ Finset.range (Nat.find h),
          if t < Nat.find h then (1 : ℝ≥0∞) else 0 := by
        exact tsum_eq_sum fun t ht => by
          have ht' : ¬ t < Nat.find h := by
            simpa only [Finset.mem_range] using ht
          simp [ht']
      _ = ∑ _t ∈ Finset.range (Nat.find h), (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact if_pos (Finset.mem_range.mp ht)
      _ = (Nat.find h : ℝ≥0∞) := by simp
  · have hnot (t : ℕ) : ω ∉ hitBy init t := by
      rintro ⟨s, _, hs⟩
      exact h ⟨s, hs⟩
    rw [τ_D, dif_neg h]
    symm
    have heq :
        (fun t : ℕ =>
          if ω ∈ hitBy init t then (0 : ℝ≥0∞) else 1) =
        (fun _ : ℕ => (1 : ℝ≥0∞)) := by
      funext t
      exact if_neg (hnot t)
    rw [heq]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)

theorem lintegral_τ_D_eq_tsum
    (init : Cfg L K) (ν : Measure (Ω L K)) :
    (∫⁻ ω, τ_D init ω ∂ν) =
      ∑' t : ℕ, ν (hitBy init t)ᶜ := by
  classical
  calc
    (∫⁻ ω, τ_D init ω ∂ν) =
        ∫⁻ ω, ∑' t : ℕ,
          if ω ∈ hitBy init t then (0 : ℝ≥0∞) else 1 ∂ν := by
      apply lintegral_congr
      intro ω
      exact τ_D_eq_tsum init ω
    _ = ∑' t : ℕ,
        ∫⁻ ω, (if ω ∈ hitBy init t then (0 : ℝ≥0∞) else 1) ∂ν :=
      lintegral_tsum fun t =>
        (Measurable.ite (measurableSet_hitBy init t)
          measurable_const measurable_const).aemeasurable
    _ = ∑' t : ℕ, ν (hitBy init t)ᶜ := by
      apply tsum_congr
      intro t
      have hfun :
          (fun ω : Ω L K =>
            if ω ∈ hitBy init t then (0 : ℝ≥0∞) else 1) =
          ((hitBy init t)ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext ω
        by_cases hω : ω ∈ hitBy init t <;> simp [hω]
      rw [hfun]
      exact lintegral_indicator_one (measurableSet_hitBy init t).compl

/-- The new full projection theorem may supply these endpoint marginals.
It is not inferred here merely from the one-step projection. -/
def EndpointProjection (init : Cfg L K) : Prop :=
  ∀ T : ℕ,
    Measure.map (fun ω => trace init ω T) (law init) =
      ((NonuniformMajority L K).transitionKernel ^ T) init

theorem endpointProjection_of_traceProjection (init : Cfg L K)
    (hproj : Measure.map (trace init) (law init) = ProtocolTraceLaw.μ init) :
    EndpointProjection init := by
  intro T
  calc
    Measure.map (fun ω => trace init ω T) (law init) =
        Measure.map (fun tr : Phase3GoodClock.Trace L K => tr T)
          (Measure.map (trace init) (law init)) := by
      rw [Measure.map_map (measurable_pi_apply T) (measurable_trace init)]
      rfl
    _ = Measure.map (fun tr : Phase3GoodClock.Trace L K => tr T)
        (ProtocolTraceLaw.μ init) := by rw [hproj]
    _ = ((NonuniformMajority L K).transitionKernel ^ T) init :=
      (ProtocolTraceLaw.traceLawAt init T).endpoint_law

theorem noHit_eq_kernel (init : Cfg L K) (T : ℕ)
    (hproj : EndpointProjection init) :
    law init (hitBy init T)ᶜ =
      ((NonuniformMajority L K).transitionKernel ^ T) init
        (StableDone L K init)ᶜ := by
  have heq :
      (hitBy init T)ᶜ =
        (fun ω => trace init ω T) ⁻¹' (StableDone L K init)ᶜ := by
    ext ω
    change (¬ ω ∈ hitBy init T) ↔
      (¬ trace init ω T ∈ StableDone L K init)
    exact not_congr (hitBy_iff_endpoint init ω T)
  rw [heq, ← Measure.map_apply (f := fun ω => trace init ω T)
    ((measurable_pi_apply T).comp (measurable_trace init))
    (measurableSet_StableDone L K init).compl, hproj T]

theorem expectation_eq_expectedHitting (init : Cfg L K)
    (hproj : EndpointProjection init) :
    (∫⁻ ω, τ_D init ω ∂law init) =
      expectedHitting (NonuniformMajority L K).transitionKernel
        init (StableDone L K init) := by
  rw [lintegral_τ_D_eq_tsum, expectedHitting_eq_tsum]
  apply tsum_congr
  intro T
  exact noHit_eq_kernel init T hproj

/-- The paper's split-geometric expectation formula, with the recovery
hypothesis quantified over every reachable unfinished configuration. -/
def PathwiseRecoverySplit (init : Cfg L K) : Prop :=
  ∀ (T B : ℕ) (δ : ℝ), 0 ≤ δ → 0 < B →
    (∀ b : Cfg L K,
      ReachableFrom L K init b →
      b ∈ (StableDone L K init)ᶜ →
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ (B : ℝ≥0∞)) →
    law init (hitBy init T)ᶜ ≤ ENNReal.ofReal δ →
    (∫⁻ ω, τ_D init ω ∂law init) ≤
      ENNReal.ofReal ((T : ℝ) + 4 * δ * (B : ℝ))

theorem time_recovery_normalization (T B : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (T : ℝ≥0∞) + ENNReal.ofReal δ * ((2 * B : ℕ) : ℝ≥0∞) *
      (1 - (1 / 2 : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal ((T : ℝ) + 4 * δ * (B : ℝ)) := by
  have hhalf : (1 - (1 / 2 : ℝ≥0∞))⁻¹ = 2 := by
    rw [one_div, ENNReal.one_sub_inv_two, inv_inv]
  rw [hhalf]
  rw [ENNReal.ofReal_add (Nat.cast_nonneg T)
      (show 0 ≤ 4 * δ * (B : ℝ) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ 4 * δ by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  simp only [Nat.cast_mul, Nat.cast_ofNat,
    ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  ring

theorem pathwiseRecoverySplit_of_endpointProjection (init : Cfg L K)
    (hproj : EndpointProjection init) :
    PathwiseRecoverySplit init := by
  intro T B δ hδ hB hRecover hFast
  have hFastKernel :
      ((NonuniformMajority L K).transitionKernel ^ T) init
        (StableDone L K init)ᶜ ≤ ENNReal.ofReal δ := by
    rw [← noHit_eq_kernel init T hproj]
    exact hFast
  have hsplit :=
    FastExpectedTime.expected_time_from_fast_tail_on_reachable
      (Brecover := B) init init Relation.ReflTransGen.refl
      T (ENNReal.ofReal δ) hFastKernel hB hRecover
  rw [expectation_eq_expectedHitting init hproj]
  simpa only [time_recovery_normalization T B hδ] using hsplit


/-! ## Scalar calibration; the population threshold remains symbolic -/

private def timeThresholdAt (e : ℕ) : ℕ := 5 * 2 ^ e

/-- The population threshold `5 * 2 ^ (2 ^ 41)`, kept symbolic (never evaluated). -/
def timePopulationThreshold : ℕ := timeThresholdAt (2 ^ 41)

private theorem time_population_threshold_eq :
    timePopulationThreshold = timeThresholdAt (2 ^ 41) := by rfl

/-- The Phase 3 threshold `5 * 2 ^ (2 ^ 30)` as an exponent-parametric wrapper. -/
private def oldThresholdAt (e : ℕ) : ℕ := 5 * 2 ^ e

private theorem old_threshold_eq :
    PhaseThreeModel.Numeric.populationThreshold = oldThresholdAt (2 ^ 30) := by
  rfl

/-- Monotonicity at variable exponents, so no large power is ever reduced. -/
private theorem oldThresholdAt_le {a e : ℕ} (h : a ≤ e) :
    oldThresholdAt a ≤ timeThresholdAt e := by
  unfold oldThresholdAt timeThresholdAt
  exact Nat.mul_le_mul_left 5 (Nat.pow_le_pow_right (by norm_num) h)

private theorem time_population_at_bounds {n e : ℕ}
    (he : 2 ^ 30 ≤ e) (hn : timeThresholdAt e ≤ n) :
    PhaseThreeModel.Numeric.populationThreshold ≤ n ∧ 40 ≤ n := by
  change 5 * 2 ^ e ≤ n at hn
  have hOld :
      PhaseThreeModel.Numeric.populationThreshold ≤ 5 * 2 ^ e := by
    rw [old_threshold_eq]
    exact oldThresholdAt_le he
  have heSmall : 3 ≤ e :=
    (by norm_num : (3 : ℕ) ≤ 2 ^ 30).trans he
  have hpow : (2 : ℕ) ^ 3 ≤ 2 ^ e :=
    Nat.pow_le_pow_right (by norm_num) heSmall
  have hsmall : 40 ≤ 5 * 2 ^ e := by
    have hm := Nat.mul_le_mul_left 5 hpow
    norm_num only [show (2 : ℕ) ^ 3 = 8 by norm_num] at hm
    exact hm
  exact ⟨hOld.trans hn, hsmall.trans hn⟩

theorem time_population_bounds {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    PhaseThreeModel.Numeric.populationThreshold ≤ n ∧ 40 ≤ n := by
  have hnAt : timeThresholdAt (2 ^ 41) ≤ n :=
    (congrArg (fun q : ℕ => q ≤ n) time_population_threshold_eq).mp hn
  exact time_population_at_bounds
    (Nat.pow_le_pow_right (by norm_num) (by norm_num : 30 ≤ 41)) hnAt

theorem time_hour_calibration {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    40 ≤ n ∧ 0 < (n : ℝ) ∧ 6 ≤ Real.log (n : ℝ) ∧
      Real.log (n : ℝ) ≤ (PhaseThreeModel.Numeric.clockHours n : ℝ) ∧
      (PhaseThreeModel.Numeric.clockHours n : ℝ) ≤
        (11 / 6 : ℝ) * Real.log (n : ℝ) ∧
      PhaseThreeModel.Numeric.clockHours n ≤ n := by
  obtain ⟨hOld, hnlarge⟩ := time_population_bounds hn
  have hdensity : (6 / 25 : ℝ) * (n : ℝ) ≤ (n : ℝ) := by
    nlinarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨hnp, hlog, _, _, _⟩ :=
    PhaseThreeModel.Numeric.logarithmic_inputs
      (n := n) (C := n) hOld hdensity le_rfl
  have hy : 6 ≤ Real.log (n : ℝ) := by linarith only [hlog]
  obtain ⟨hHlo, hHhi, hHn⟩ :=
    PhaseThreeModel.Numeric.hour_bounds hnp hy
  exact ⟨hnlarge, hnp, hy, hHlo, hHhi, hHn⟩

theorem time_exp_three_lt : Real.exp (3 : ℝ) < 21 := by
  have he : Real.exp 1 ≤ (11 / 4 : ℝ) := by
    have h := Real.exp_bound' (x := (1 : ℝ))
      (by norm_num) (by norm_num) (n := 5) (by norm_num)
    refine h.trans ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc
    Real.exp (3 : ℝ) = (Real.exp 1) ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ ≤ (11 / 4 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he 3
    _ < 21 := by norm_num

theorem time_error_budget_le {x : ℝ} (hx : 8 ≤ x) :
    2 / x ^ 2 + 8 / x ^ 5 + 3 / x ^ 2 + 100 / x ^ 2 +
      6 / x ^ 3 + 21 / x ^ 3 ≤ 110 / x ^ 2 := by
  have hxp : 0 < x := by linarith only [hx]
  have hcube : (8 : ℝ) ^ 3 ≤ x ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hx 3
  have hlarge : (8 : ℝ) ≤ x ^ 3 := by
    norm_num at hcube
    linarith only [hcube]
  have hsmall : 8 / x ^ 5 ≤ 1 / x ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hxp 5) (pow_pos hxp 2)]
    have hm := mul_le_mul_of_nonneg_right hlarge (sq_nonneg x)
    nlinarith only [hm]
  have hrest : 27 / x ^ 3 ≤ 4 / x ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hxp 3) (pow_pos hxp 2)]
    have hb : (27 : ℝ) ≤ 4 * x := by linarith only [hx]
    have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg x)
    nlinarith only [hm]
  calc
    2 / x ^ 2 + 8 / x ^ 5 + 3 / x ^ 2 + 100 / x ^ 2 +
        6 / x ^ 3 + 21 / x ^ 3 =
        105 / x ^ 2 + 8 / x ^ 5 + 27 / x ^ 3 := by ring
    _ ≤ 105 / x ^ 2 + 1 / x ^ 2 + 4 / x ^ 2 :=
      add_le_add (add_le_add le_rfl hsmall) hrest
    _ = 110 / x ^ 2 := by ring

theorem time_error_budget_ennreal {x : ℝ} (hx : 8 ≤ x) :
    ENNReal.ofReal (2 / x ^ 2) + ENNReal.ofReal (8 / x ^ 5) +
      ENNReal.ofReal (3 / x ^ 2) + ENNReal.ofReal (100 / x ^ 2) +
      ENNReal.ofReal (6 / x ^ 3) + ENNReal.ofReal (21 / x ^ 3) ≤
      ENNReal.ofReal (110 / x ^ 2) := by
  have hxp : 0 < x := by linarith only [hx]
  calc
    _ = ENNReal.ofReal
        (2 / x ^ 2 + 8 / x ^ 5 + 3 / x ^ 2 + 100 / x ^ 2 +
          6 / x ^ 3 + 21 / x ^ 3) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (110 / x ^ 2) :=
      ENNReal.ofReal_le_ofReal (time_error_budget_le hx)

theorem time_inverse_square_budget_lt_half {x : ℝ} (hx : 40 ≤ x) :
    110 / x ^ 2 < (1 / 2 : ℝ) := by
  have hxp : 0 < x := by linarith only [hx]
  have hs : (40 : ℝ) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hx 2
  rw [div_lt_iff₀ (pow_pos hxp 2)]
  nlinarith only [hs]

theorem time_horizon_le {n H : ℕ}
    (hn : 1 ≤ n) (hH : 1 ≤ H)
    (hlog : 0 ≤ Real.log (n : ℝ))
    (hlogH : Real.log (n : ℝ) ≤ (H : ℝ)) :
    1150 * n * H +
      Nat.ceil (20000 * (n : ℝ) * Real.log (n : ℝ)) +
      Nat.ceil (1800 * (n : ℝ) * Real.log (n : ℝ)) ≤
      23000 * n * H := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hprod : (1 : ℝ) ≤ (n : ℝ) * (H : ℝ) := by
    simpa using mul_le_mul hnR hHR
      (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg n)
  have hlogprod :=
    mul_le_mul_of_nonneg_left hlogH (Nat.cast_nonneg n)
  have hwide :
      (Nat.ceil (20000 * (n : ℝ) * Real.log (n : ℝ)) : ℝ) <
        20000 * (n : ℝ) * Real.log (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hnarrow :
      (Nat.ceil (1800 * (n : ℝ) * Real.log (n : ℝ)) : ℝ) <
        1800 * (n : ℝ) * Real.log (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hreal :
      (1150 : ℝ) * n * H +
        (Nat.ceil (20000 * (n : ℝ) * Real.log (n : ℝ)) : ℝ) +
        (Nat.ceil (1800 * (n : ℝ) * Real.log (n : ℝ)) : ℝ) ≤
        23000 * n * H := by
    nlinarith only [hwide, hnarrow, hlogprod, hprod]
  exact_mod_cast hreal

theorem time_expectation_budget_le {x H L T δ : ℝ}
    (hx : 0 < x) (hH : 0 ≤ H)
    (hHL : H ≤ (11 / 6 : ℝ) * L)
    (hT : T ≤ 23000 * x * H) (hδ : δ ≤ 110 / x ^ 2) :
    T + 4 * δ * (30700 * x ^ 3 * H) ≤
      24807000 * x * L := by
  have hL : 0 ≤ L := by linarith only [hH, hHL]
  have hXL : 0 ≤ x * L := mul_nonneg hx.le hL
  have hcoefficient : 0 ≤ 30700 * x ^ 3 * H := by positivity
  have htail :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hδ (by norm_num : (0 : ℝ) ≤ 4))
      hcoefficient
  have hcancel :
      4 * (110 / x ^ 2) * (30700 * x ^ 3 * H) =
        13508000 * x * H := by
    field_simp [ne_of_gt hx] <;> ring
  rw [hcancel] at htail
  calc
    T + 4 * δ * (30700 * x ^ 3 * H) ≤
        23000 * x * H + 13508000 * x * H := add_le_add hT htail
    _ = 13531000 * x * H := by ring
    _ ≤ 13531000 * x * ((11 / 6 : ℝ) * L) :=
      mul_le_mul_of_nonneg_left hHL (by positivity)
    _ ≤ 24807000 * x * L := by nlinarith only [hXL]

theorem time_expectation_budget_ennreal {x H L T δ : ℝ}
    (hx : 0 < x) (hH : 0 ≤ H)
    (hHL : H ≤ (11 / 6 : ℝ) * L)
    (hT : T ≤ 23000 * x * H) (hδ : δ ≤ 110 / x ^ 2) :
    ENNReal.ofReal (T + 4 * δ * (30700 * x ^ 3 * H)) ≤
      ENNReal.ofReal (24807000 * x * L) :=
  ENNReal.ofReal_le_ofReal
    (time_expectation_budget_le hx hH hHL hT hδ)


/-! ## Transparent interfaces for the reviewed original-input events -/

abbrev InputCfg (n : ℕ) :=
  Cfg (PhaseThreeModel.Numeric.hourIndex n) 256

abbrev InputLog (n : ℕ) :=
  Ω (PhaseThreeModel.Numeric.hourIndex n) 256

def earlyHorizon (n : ℕ) : ℕ :=
  1150 * n * PhaseThreeModel.Numeric.clockHours n

noncomputable def logWindow (n c : ℕ) : ℕ :=
  Nat.ceil ((c : ℝ) * (n : ℝ) * Real.log (n : ℝ))

def fastHorizon (n : ℕ) : ℕ :=
  23000 * n * PhaseThreeModel.Numeric.clockHours n

def recoveryBudget (n : ℕ) : ℕ :=
  30700 * n ^ 3 * PhaseThreeModel.Numeric.clockHours n

def gapMagnitude (init : Cfg L K) : ℕ :=
  (initialGap init).natAbs

noncomputable def timeMainCount (c : Cfg L K) : ℕ :=
  Multiset.countP (fun a => a.role = .main) c

/-- The first genuine seed, not a profile chosen at an arbitrary later time. -/
def firstPhaseSeed (init : Cfg L K) (p t : ℕ) (ω : Ω L K) : Prop :=
  (∃ a ∈ trace init ω t, a.phase.val = p) ∧
    ∀ u < t, ∀ a ∈ trace init ω u, a.phase.val < p

/--
The assembler is parametric in the three reviewed history predicates.
A protocol producer must instantiate these predicates with the definitions in
the reviewed papers. In particular, clockGood is G'_3 on a genuine retained
past, not a conditioning event for the future scheduler.

The fields below are deterministic links, not probabilistic estimates.
The full predicates must retain the other paper clauses for their consumers.
-/
structure StageEvents (n : ℕ) (init : InputCfg n) where
  entry : InputLog n → ℕ → ℕ → Prop
  clockGood : InputLog n → ℕ → ℕ → ℕ → Prop
  averageGood : InputLog n → ℕ → ℕ → Prop
  entry_seed : ∀ {ω S T}, entry ω S T → firstPhaseSeed init 3 S ω
  entry_order : ∀ {ω S T}, entry ω S T → S ≤ T
  clock_seed : ∀ {ω S T ρ},
    clockGood ω S T ρ → firstPhaseSeed init 4 ρ ω
  clock_deadline : ∀ {ω S T ρ},
    clockGood ω S T ρ → ρ ≤ S + logWindow n 20000
  clock_mass : ∀ {ω S T ρ},
    clockGood ω S T ρ →
      gapMagnitude init ≤ timeMainCount (trace init ω S)

variable {n : ℕ} {init : InputCfg n}

def entryBy (E : StageEvents n init) : Set (InputLog n) :=
  {ω | ∃ S T, T ≤ earlyHorizon n ∧ E.entry ω S T}

def clockBy (E : StageEvents n init) : Set (InputLog n) :=
  {ω | ∃ S T ρ,
    T ≤ earlyHorizon n ∧ E.entry ω S T ∧ E.clockGood ω S T ρ}

def successfulHistory (E : StageEvents n init)
    (ω : InputLog n) (S T ρ : ℕ) : Prop :=
  T ≤ earlyHorizon n ∧ E.entry ω S T ∧
    E.clockGood ω S T ρ ∧ E.averageGood ω S ρ

def averageBy (E : StageEvents n init) : Set (InputLog n) :=
  {ω | ∃ S T ρ, successfulHistory E ω S T ρ}

def phaseEntryFailure (E : StageEvents n init) : Set (InputLog n) :=
  {ω | ω ∉ hitBy init (earlyHorizon n) ∧ ω ∉ entryBy E}

def phaseClockFailure (E : StageEvents n init) : Set (InputLog n) :=
  entryBy E \ clockBy E

def phaseAveragingFailure (E : StageEvents n init) : Set (InputLog n) :=
  clockBy E \ averageBy E

def smallGapLateFailure (E : StageEvents n init) : Set (InputLog n) :=
  {ω | ∃ S T ρ,
    successfulHistory E ω S T ρ ∧
      0 < gapMagnitude init ∧
      40 * gapMagnitude init < timeMainCount (trace init ω S) ∧
      ω ∉ hitBy init (ρ + logWindow n 300)}

def strongGapLateFailure (E : StageEvents n init) : Set (InputLog n) :=
  {ω | ∃ S T ρ,
    successfulHistory E ω S T ρ ∧
      0 < gapMagnitude init ∧
      timeMainCount (trace init ω S) ≤ 40 * gapMagnitude init ∧
      gapMagnitude init ≤ timeMainCount (trace init ω S) ∧
      ω ∉ hitBy init (ρ + logWindow n 1800)}

def tieLateFailure (E : StageEvents n init) : Set (InputLog n) :=
  {ω | ∃ S T ρ,
    successfulHistory E ω S T ρ ∧
      gapMagnitude init = 0 ∧
      ω ∉ hitBy init (ρ + logWindow n 4)}

def badCover (E : StageEvents n init) : Set (InputLog n) :=
  phaseEntryFailure E ∪
    (phaseClockFailure E ∪
      (phaseAveragingFailure E ∪
        (smallGapLateFailure E ∪
          (strongGapLateFailure E ∪ tieLateFailure E))))

theorem logWindow_mono {n a b : ℕ}
    (hlog : 0 ≤ Real.log (n : ℝ)) (hab : a ≤ b) :
    logWindow n a ≤ logWindow n b := by
  apply Nat.ceil_mono
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right habR (Nat.cast_nonneg n)) hlog

theorem time_common_horizon {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    earlyHorizon n + logWindow n 20000 + logWindow n 1800 ≤
      fastHorizon n := by
  obtain ⟨hnlarge, _, hlog, hlogH, _, _⟩ :=
    time_hour_calibration hn
  clear hn
  have hH : 1 ≤ PhaseThreeModel.Numeric.clockHours n := by
    unfold PhaseThreeModel.Numeric.clockHours
    omega
  exact time_horizon_le (by omega) hH (by linarith) hlogH

/-- Deterministic branch cover. The random Main count is read from the same
genuine first-seed history in every branch; equality belongs to strong gap. -/
theorem time_bad_cover (hn : timePopulationThreshold ≤ n)
    (E : StageEvents n init) :
    (hitBy init (fastHorizon n))ᶜ ⊆ badCover E := by
  intro ω hnotFast
  have hcommon := time_common_horizon hn
  have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
    le_trans (by norm_num : (0 : ℝ) ≤ 6) (time_hour_calibration hn).2.2.1
  clear hn
  have hEarly : earlyHorizon n ≤ fastHorizon n := by omega
  have hnotEarly : ω ∉ hitBy init (earlyHorizon n) :=
    fun h => hnotFast (hitBy_mono init hEarly h)
  change ω ∈ phaseEntryFailure E ∪
    (phaseClockFailure E ∪
      (phaseAveragingFailure E ∪
        (smallGapLateFailure E ∪
          (strongGapLateFailure E ∪ tieLateFailure E))))
  by_cases he : ω ∈ entryBy E
  · by_cases hc : ω ∈ clockBy E
    · by_cases ha : ω ∈ averageBy E
      · obtain ⟨S, T, ρ, hh⟩ := ha
        obtain ⟨hT, hentry, hclock, havg⟩ := hh
        have hhistory : successfulHistory E ω S T ρ :=
          ⟨hT, hentry, hclock, havg⟩
        have hST := E.entry_order hentry
        have hρ := E.clock_deadline hclock
        have hM := E.clock_mass hclock
        have hdeadline : ρ + logWindow n 1800 ≤ fastHorizon n := by
          omega
        have hnotStrong : ω ∉ hitBy init (ρ + logWindow n 1800) :=
          fun h => hnotFast (hitBy_mono init hdeadline h)
        by_cases hz : gapMagnitude init = 0
        · have hshort := logWindow_mono (n := n) hlognonneg
            (by norm_num : 4 ≤ 1800)
          have hdeadlineTie :
              ρ + logWindow n 4 ≤ fastHorizon n := by omega
          have hnotTie : ω ∉ hitBy init (ρ + logWindow n 4) :=
            fun h => hnotFast (hitBy_mono init hdeadlineTie h)
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨S, T, ρ, hhistory, hz, hnotTie⟩))))
        · have hpos : 0 < gapMagnitude init := Nat.pos_of_ne_zero hz
          by_cases hs :
              40 * gapMagnitude init < timeMainCount (trace init ω S)
          · have hshort := logWindow_mono (n := n) hlognonneg
              (by norm_num : 300 ≤ 1800)
            have hdeadlineSmall :
                ρ + logWindow n 300 ≤ fastHorizon n := by omega
            have hnotSmall : ω ∉ hitBy init (ρ + logWindow n 300) :=
              fun h => hnotFast (hitBy_mono init hdeadlineSmall h)
            exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨S, T, ρ, hhistory, hpos, hs, hnotSmall⟩)))
          · have hs' :
                timeMainCount (trace init ω S) ≤ 40 * gapMagnitude init :=
              Nat.le_of_not_gt hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨S, T, ρ, hhistory, hpos, hs', hM, hnotStrong⟩))))
      · exact Or.inr (Or.inr (Or.inl ⟨hc, ha⟩))
    · exact Or.inr (Or.inl ⟨he, hc⟩)
  · exact Or.inl ⟨hnotEarly, he⟩

theorem measure_badCover_le (E : StageEvents n init) :
    law init (badCover E) ≤
      law init (phaseEntryFailure E) +
        law init (phaseClockFailure E) +
        law init (phaseAveragingFailure E) +
        law init (smallGapLateFailure E) +
        law init (strongGapLateFailure E) +
        law init (tieLateFailure E) := by
  let μ := law init
  let A := phaseEntryFailure E
  let B := phaseClockFailure E
  let C := phaseAveragingFailure E
  let D := smallGapLateFailure E
  let F := strongGapLateFailure E
  let G := tieLateFailure E
  change μ (A ∪ (B ∪ (C ∪ (D ∪ (F ∪ G))))) ≤
    μ A + μ B + μ C + μ D + μ F + μ G
  calc
    μ (A ∪ (B ∪ (C ∪ (D ∪ (F ∪ G))))) ≤
        μ A + μ (B ∪ (C ∪ (D ∪ (F ∪ G)))) := measure_union_le _ _
    _ ≤ μ A + (μ B + μ (C ∪ (D ∪ (F ∪ G)))) :=
      add_le_add le_rfl (measure_union_le _ _)
    _ ≤ μ A + (μ B + (μ C + μ (D ∪ (F ∪ G)))) :=
      add_le_add le_rfl (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ μ A + (μ B + (μ C + (μ D + μ (F ∪ G)))) :=
      add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl (measure_union_le _ _)))
    _ ≤ μ A + (μ B + (μ C + (μ D + (μ F + μ G)))) :=
      add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
        (add_le_add le_rfl (measure_union_le _ _))))
    _ = μ A + μ B + μ C + μ D + μ F + μ G := by ac_rfl

/-- This uses joint probabilities under law init, never conditional
probabilities given eventual success of clockGood or averageGood. -/
theorem time_fast_tail_of_phase_estimates
    (hn : timePopulationThreshold ≤ n) (E : StageEvents n init)
    (phaseZeroTwo_entry :
      law init (phaseEntryFailure E) ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2))
    (phaseThree_clock :
      law init (phaseClockFailure E) ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 5))
    (phaseThree_averaging :
      law init (phaseAveragingFailure E) ≤ ENNReal.ofReal (3 / (n : ℝ) ^ 2))
    (strictSmallGap_late :
      law init (smallGapLateFailure E) ≤ ENNReal.ofReal (100 / (n : ℝ) ^ 2))
    (strongGap_continuation :
      law init (strongGapLateFailure E) ≤ ENNReal.ofReal (6 / (n : ℝ) ^ 3))
    (tie_settling :
      law init (tieLateFailure E) ≤
        ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3)) :
    law init {ω | (fastHorizon n : ℝ≥0∞) < τ_D init ω} ≤
      ENNReal.ofReal (110 / (n : ℝ) ^ 2) := by
  have hnlarge := (time_population_bounds hn).2
  have hcover := time_bad_cover hn E
  clear hn
  have hnR : 8 ≤ (n : ℝ) := by
    exact_mod_cast (show 8 ≤ n by omega)
  have hTie :
      law init (tieLateFailure E) ≤ ENNReal.ofReal (21 / (n : ℝ) ^ 3) :=
    tie_settling.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right time_exp_three_lt.le (by positivity)))
  rw [τ_D_tail_set]
  calc
    law init (hitBy init (fastHorizon n))ᶜ ≤ law init (badCover E) :=
      measure_mono hcover
    _ ≤ law init (phaseEntryFailure E) +
        law init (phaseClockFailure E) +
        law init (phaseAveragingFailure E) +
        law init (smallGapLateFailure E) +
        law init (strongGapLateFailure E) +
        law init (tieLateFailure E) := measure_badCover_le E
    _ ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) +
        ENNReal.ofReal (8 / (n : ℝ) ^ 5) +
        ENNReal.ofReal (3 / (n : ℝ) ^ 2) +
        ENNReal.ofReal (100 / (n : ℝ) ^ 2) +
        ENNReal.ofReal (6 / (n : ℝ) ^ 3) +
        ENNReal.ofReal (21 / (n : ℝ) ^ 3) :=
      add_le_add
        (add_le_add
          (add_le_add
            (add_le_add
              (add_le_add phaseZeroTwo_entry phaseThree_clock)
              phaseThree_averaging)
            strictSmallGap_late)
          strongGap_continuation)
        hTie
    _ ≤ ENNReal.ofReal (110 / (n : ℝ) ^ 2) :=
      time_error_budget_ennreal hnR

def InputTimeClaim (n : ℕ) (init : InputCfg n) : Prop :=
  law init {ω | (fastHorizon n : ℝ≥0∞) < τ_D init ω} ≤
      ENNReal.ofReal (110 / (n : ℝ) ^ 2) ∧
    (∫⁻ ω, τ_D init ω ∂law init) ≤
      ENNReal.ofReal (24807000 * (n : ℝ) * Real.log (n : ℝ))

/-- The universal headline, in raw interactions, for the actual protocol
parameters L = clog 2 n and K = 256. -/
def DotyTimeClaim : Prop :=
  ∀ n : ℕ, timePopulationThreshold ≤ n →
    ∀ init : InputCfg n,
      validInitial init → init.card = n → InputTimeClaim n init

theorem inputTimeClaim_of_estimates
    (hn : timePopulationThreshold ≤ n) (E : StageEvents n init)
    (phaseZeroTwo_entry :
      law init (phaseEntryFailure E) ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2))
    (phaseThree_clock :
      law init (phaseClockFailure E) ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 5))
    (phaseThree_averaging :
      law init (phaseAveragingFailure E) ≤ ENNReal.ofReal (3 / (n : ℝ) ^ 2))
    (strictSmallGap_late :
      law init (smallGapLateFailure E) ≤ ENNReal.ofReal (100 / (n : ℝ) ^ 2))
    (strongGap_continuation :
      law init (strongGapLateFailure E) ≤ ENNReal.ofReal (6 / (n : ℝ) ^ 3))
    (tie_settling :
      law init (tieLateFailure E) ≤
        ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3))
    (reachable_recovery :
      ∀ b : InputCfg n,
        ReachableFrom (PhaseThreeModel.Numeric.hourIndex n) 256 init b →
        b ∈ (StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init)ᶜ →
        expectedHitting
          (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel
          b (StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init) ≤
          (recoveryBudget n : ℝ≥0∞))
    (expectation_formula : PathwiseRecoverySplit init) :
    InputTimeClaim n init := by
  have hFast := time_fast_tail_of_phase_estimates hn E
    phaseZeroTwo_entry phaseThree_clock phaseThree_averaging
    strictSmallGap_late strongGap_continuation tie_settling
  refine ⟨hFast, ?_⟩
  obtain ⟨hnlarge, hnp, _, _, hHlog, _⟩ := time_hour_calibration hn
  clear hn
  have hH : 0 < PhaseThreeModel.Numeric.clockHours n := by
    unfold PhaseThreeModel.Numeric.clockHours
    omega
  have hRecoverPos : 0 < recoveryBudget n := by
    unfold recoveryBudget
    have hnpos : 0 < n := by omega
    positivity
  have hFastSet :
      law init (hitBy init (fastHorizon n))ᶜ ≤
        ENNReal.ofReal (110 / (n : ℝ) ^ 2) := by
    simpa only [τ_D_tail_set] using hFast
  have hsplit := expectation_formula
    (fastHorizon n) (recoveryBudget n) (110 / (n : ℝ) ^ 2)
    (by positivity) hRecoverPos reachable_recovery hFastSet
  refine hsplit.trans ?_
  have hT :
      (fastHorizon n : ℝ) =
        23000 * (n : ℝ) * (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
    simp only [fastHorizon, Nat.cast_mul, Nat.cast_ofNat]
  have hB :
      (recoveryBudget n : ℝ) =
        30700 * (n : ℝ) ^ 3 * (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
    simp only [recoveryBudget, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hT, hB]
  exact time_expectation_budget_ennreal hnp
    (Nat.cast_nonneg (PhaseThreeModel.Numeric.clockHours n))
    hHlog le_rfl le_rfl

/--
The final assembly surface. Each probabilistic input is a joint event under
the original pair-log law. No reset law, independence between phase failures,
conditional law given G'_3, or arbitrary-entry quantifier is assumed.
-/
theorem dotyTimeClaim_of_estimates
    (events : ∀ n : ℕ, ∀ init : InputCfg n, StageEvents n init)
    (phaseZeroTwo_entry :
      ∀ n : ℕ, timePopulationThreshold ≤ n →
      ∀ init : InputCfg n, validInitial init → init.card = n →
        law init (phaseEntryFailure (events n init)) ≤
          ENNReal.ofReal (2 / (n : ℝ) ^ 2))
    (phaseThree_clock :
      ∀ n : ℕ, timePopulationThreshold ≤ n →
      ∀ init : InputCfg n, validInitial init → init.card = n →
        law init (phaseClockFailure (events n init)) ≤
          ENNReal.ofReal (8 / (n : ℝ) ^ 5))
    (phaseThree_averaging :
      ∀ n : ℕ, timePopulationThreshold ≤ n →
      ∀ init : InputCfg n, validInitial init → init.card = n →
        law init (phaseAveragingFailure (events n init)) ≤
          ENNReal.ofReal (3 / (n : ℝ) ^ 2))
    (strictSmallGap_late :
      ∀ n : ℕ, timePopulationThreshold ≤ n →
      ∀ init : InputCfg n, validInitial init → init.card = n →
        law init (smallGapLateFailure (events n init)) ≤
          ENNReal.ofReal (100 / (n : ℝ) ^ 2))
    (strongGap_continuation :
      ∀ n : ℕ, timePopulationThreshold ≤ n →
      ∀ init : InputCfg n, validInitial init → init.card = n →
        law init (strongGapLateFailure (events n init)) ≤
          ENNReal.ofReal (6 / (n : ℝ) ^ 3))
    (tie_settling :
      ∀ n : ℕ, timePopulationThreshold ≤ n →
      ∀ init : InputCfg n, validInitial init → init.card = n →
        law init (tieLateFailure (events n init)) ≤
          ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3))
    (reachable_recovery :
      ∀ n : ℕ, timePopulationThreshold ≤ n →
      ∀ init : InputCfg n, validInitial init → init.card = n →
      ∀ b : InputCfg n,
        ReachableFrom (PhaseThreeModel.Numeric.hourIndex n) 256 init b →
        b ∈ (StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init)ᶜ →
        expectedHitting
          (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel
          b (StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init) ≤
          (recoveryBudget n : ℝ≥0∞))
    (expectation_formula :
      ∀ n : ℕ, timePopulationThreshold ≤ n →
      ∀ init : InputCfg n, validInitial init → init.card = n →
        PathwiseRecoverySplit init) :
    DotyTimeClaim := by
  intro n hn init hvalid hcard
  exact inputTimeClaim_of_estimates hn (events n init)
    (phaseZeroTwo_entry n hn init hvalid hcard)
    (phaseThree_clock n hn init hvalid hcard)
    (phaseThree_averaging n hn init hvalid hcard)
    (strictSmallGap_late n hn init hvalid hcard)
    (strongGap_continuation n hn init hvalid hcard)
    (tie_settling n hn init hvalid hcard)
    (reachable_recovery n hn init hvalid hcard)
    (expectation_formula n hn init hvalid hcard)

end Ripple.PopulationProtocol.ExactMajority.TimeTheorem

import Ripple.PopulationProtocol.ExactMajority.Probability.PairLogAuxiliary
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Scalar

/-!
# Potential drain tails for the actual trace

A natural-number potential that never increases while the configuration stays in a
window, and that strictly decreases with one-step probability at least `r` while the
configuration is in the window and off a target, reaches the target or leaves the
window within `N` steps except with probability at most
`exp ((ψ₀ + 1) log 2 - N r / 2)`.

The exit time is a genuine stopping time of the pair-log filtration, so no argument
conditions on a future event. This is the scalar form of the stage estimates (21)
and (25) of the Phase-1 drain (Doty et al., exact majority). `potential_drift_tail` is the stopped multiplicative-drift form used for
(23), built on the one-step Markov identity `lintegral_prefix_next`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.TraceDrain

open TimeTheorem PairLog PairLogAuxiliary

attribute [local instance] Classical.propDecidable

variable {L K : ℕ}

theorem trace_zero (init : Cfg L K) (ω : Ω L K) : trace init ω 0 = init := rfl

theorem trace_succ (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    trace init ω (t + 1) = applyDraw (trace init ω t) (ω (t + 1)) := rfl

/-- The first time the trace satisfies `B`, or `⊤` if it never does. -/
noncomputable def exitTime (init : Cfg L K) (B : Cfg L K → Prop) (ω : Ω L K) :
    WithTop ℕ :=
  if h : ∃ t, B (trace init ω t) then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem exitTime_le_iff (init : Cfg L K) (B : Cfg L K → Prop) (ω : Ω L K) (i : ℕ) :
    exitTime init B ω ≤ (i : WithTop ℕ) ↔ ∃ s ≤ i, B (trace init ω s) := by
  unfold exitTime
  split_ifs with h
  · constructor
    · intro hle
      have h' : Nat.find h ≤ i := by exact_mod_cast hle
      exact ⟨Nat.find h, h', Nat.find_spec h⟩
    · rintro ⟨s, hs, hB⟩
      have h' : Nat.find h ≤ i := (Nat.find_min' h hB).trans hs
      exact_mod_cast h'
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨s, _, hs⟩
      exact absurd ⟨s, hs⟩ h

theorem not_of_lt_exitTime (init : Cfg L K) (B : Cfg L K → Prop) (ω : Ω L K) (N : ℕ)
    (hN : (N : WithTop ℕ) < exitTime init B ω) :
    ∀ t ≤ N, ¬ B (trace init ω t) := by
  intro t ht hB
  have hle : exitTime init B ω ≤ (N : WithTop ℕ) :=
    (exitTime_le_iff init B ω N).2 ⟨t, ht, hB⟩
  exact absurd hN (not_lt.mpr hle)

theorem exitTime_isStoppingTime (init : Cfg L K) (B : Cfg L K → Prop) :
    IsStoppingTime (pairLogFiltration L K) (exitTime init B) := by
  intro i
  have hm : MeasurableSet[pairLogFiltration L K i]
      (⋃ s, {ω | s ≤ i ∧ B (trace init ω s)}) := by
    refine MeasurableSet.iUnion fun s => ?_
    by_cases hs : s ≤ i
    · have hB : MeasurableSet[pairLogFiltration L K i] {ω | B (trace init ω s)} :=
        measurable_trace_at_of_le init hs
          (Set.to_countable {c : Cfg L K | B c}).measurableSet
      simpa only [hs, true_and] using hB
    · simp only [hs, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact exitTime_le_iff init B ω i

/-- Potential drain tail with the decrease set given abstractly. -/
theorem potential_drain_tail_of_mem (init : Cfg L K) (ψ : Cfg L K → ℕ)
    (W target : Cfg L K → Prop)
    (S : Cfg L K → Set (Cfg L K))
    (hS : ∀ c c', c' ∈ S c ↔ ψ c' + 1 ≤ ψ c)
    (hmono : ∀ c, W c → ∀ d, ψ (applyDraw c d) ≤ ψ c)
    (r : ℝ≥0∞) (hr : r ≠ ⊤) (hr1 : r.toReal ≤ 1)
    (hfloor : ∀ c, W c → ¬ target c →
      r ≤ (NonuniformMajority L K).transitionKernel c (S c))
    (N : ℕ) :
    (law init).real
        {ω | (N : WithTop ℕ) < exitTime init (fun c => ¬ W c ∨ target c) ω} ≤
      Real.exp (((ψ init : ℝ) + 1) * Real.log 2 - (N : ℝ) * r.toReal / 2) := by
  have hI : ∀ t, StronglyMeasurable[pairLogFiltration L K (t + 1)] (fun ω =>
      if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0) :=
    fun t => stronglyMeasurable_trace_step_indicator init S t
  have hzeroOne : ∀ t, ∀ᵐ ω ∂law init,
      (if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0) = 0 ∨
      (if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0) = 1 :=
    fun t => ae_of_all _ fun ω => trace_step_indicator_zero_or_one init S t ω
  have hτ := exitTime_isStoppingTime init (fun c => ¬ W c ∨ target c)
  have hcond : ∀ t : ℕ, ∀ᵐ ω ∂law init,
      (t : WithTop ℕ) < exitTime init (fun c => ¬ W c ∨ target c) ω →
      r.toReal ≤ ((law init)[fun ω =>
        if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0
        | pairLogFiltration L K t]) ω := by
    intro t
    filter_upwards [trace_step_conditional_floor init S (fun c => W c ∧ ¬ target c) r hr
      (fun c hc => hfloor c hc.1 hc.2) t] with ω hω ht
    apply hω
    have hnot := not_of_lt_exitTime init _ ω t ht t le_rfl
    simp only [not_or, not_not] at hnot
    exact hnot
  have hfail : ∀ ω, (N : WithTop ℕ) < exitTime init (fun c => ¬ W c ∨ target c) ω →
      PhaseThreeScalar.bernoulliCount (fun t ω =>
        if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0) N ω <
        (ψ init : ℝ) + 1 := by
    intro ω hN
    have hW : ∀ t ≤ N, W (trace init ω t) := by
      intro t ht
      have h := not_of_lt_exitTime init _ ω N hN t ht
      simp only [not_or, not_not] at h
      exact h.1
    have key : ∀ m ≤ N, PhaseThreeScalar.bernoulliCount (fun t ω =>
        if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0) m ω +
        (ψ (trace init ω m) : ℝ) ≤ (ψ init : ℝ) := by
      intro m
      induction m with
      | zero =>
          intro _
          simp [PhaseThreeScalar.bernoulliCount, trace_zero]
      | succ m ih =>
          intro hm
          have h1 := ih (by omega)
          have hmon : ψ (trace init ω (m + 1)) ≤ ψ (trace init ω m) := by
            rw [trace_succ]
            exact hmono _ (hW m (by omega)) _
          have hstep : (if trace init ω (m + 1) ∈ S (trace init ω m) then (1 : ℝ) else 0) +
              (ψ (trace init ω (m + 1)) : ℝ) ≤ (ψ (trace init ω m) : ℝ) := by
            split_ifs with hs
            · have hs' := (hS _ _).1 hs
              have : ((ψ (trace init ω (m + 1)) + 1 : ℕ) : ℝ) ≤
                  (ψ (trace init ω m) : ℝ) := by exact_mod_cast hs'
              push_cast at this
              linarith
            · rw [zero_add]
              exact_mod_cast hmon
          have hsum : PhaseThreeScalar.bernoulliCount (fun t ω =>
                if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0) (m + 1) ω =
              PhaseThreeScalar.bernoulliCount (fun t ω =>
                if trace init ω (t + 1) ∈ S (trace init ω t) then (1 : ℝ) else 0) m ω +
              (if trace init ω (m + 1) ∈ S (trace init ω m) then (1 : ℝ) else 0) := by
            simp only [PhaseThreeScalar.bernoulliCount, Finset.sum_range_succ]
          rw [hsum]
          linarith
    have hk := key N le_rfl
    have hpos : (0 : ℝ) ≤ (ψ (trace init ω N) : ℝ) := Nat.cast_nonneg _
    linarith
  exact PhaseThreeScalar.adapted_success_hitting_tail (μ := law init)
    (ℱ := pairLogFiltration L K) hI hzeroOne hτ hr1 hcond N ((ψ init : ℝ) + 1) hfail

/-- Potential drain tail. If `ψ` never increases on the window `W`, and on `W` off the
target its strict decrease has kernel probability at least `r`, then the trace stays
in `W` and off the target through time `N` with probability at most
`exp ((ψ init + 1) log 2 - N r / 2)`. -/
theorem potential_drain_tail (init : Cfg L K) (ψ : Cfg L K → ℕ)
    (W target : Cfg L K → Prop)
    (hmono : ∀ c, W c → ∀ d, ψ (applyDraw c d) ≤ ψ c)
    (r : ℝ≥0∞) (hr : r ≠ ⊤) (hr1 : r.toReal ≤ 1)
    (hfloor : ∀ c, W c → ¬ target c →
      r ≤ (NonuniformMajority L K).transitionKernel c {c' | ψ c' + 1 ≤ ψ c})
    (N : ℕ) :
    (law init).real
        {ω | (N : WithTop ℕ) < exitTime init (fun c => ¬ W c ∨ target c) ω} ≤
      Real.exp (((ψ init : ℝ) + 1) * Real.log 2 - (N : ℝ) * r.toReal / 2) := by
  exact potential_drain_tail_of_mem init ψ W target (fun c => {c' | ψ c' + 1 ≤ ψ c})
    (fun _ _ => Iff.rfl) hmono r hr hr1 hfloor N

/-! ## The one-step Markov identity in lintegral form and stopped drift -/

/-- One-step Markov identity on the pair log: integrating a function of the recorded
prefix through `t` and the next draw equals integrating its one-step kernel average. -/
theorem lintegral_prefix_next (init : Cfg L K) (t : ℕ)
    (F : ((k : Finset.Iic t) → Draw L K) → Draw L K → ℝ≥0∞) :
    ∫⁻ ω, F (frestrictLe t ω) (ω (t + 1)) ∂law init =
      ∫⁻ ω, (∫⁻ d, F (frestrictLe t ω) d ∂pairKernel init t (frestrictLe t ω))
        ∂law init := by
  let κ := fun s => pairKernel init s
  have hlaw : law init =
      Kernel.traj (X := fun _ => Draw L K) κ 0 (fun _ => none) :=
    (Kernel.traj_apply _ _).symm
  have hcomp : Kernel.traj (X := fun _ => Draw L K) κ 0 =
      (Kernel.traj (X := fun _ => Draw L K) κ t) ∘ₖ
        (Kernel.partialTraj (X := fun _ => Draw L K) κ 0 t) :=
    (Kernel.traj_comp_partialTraj (X := fun _ => Draw L K) (Nat.zero_le t)).symm
  have hpair : Measurable (fun ω : Ω L K =>
      (frestrictLe (π := fun _ : ℕ => Draw L K) t ω, ω (t + 1))) :=
    (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) t).prodMk
      (measurable_pi_apply (t + 1))
  have hF : Measurable (fun ω : Ω L K => F (frestrictLe t ω) (ω (t + 1))) :=
    (measurable_of_countable (Function.uncurry F)).comp hpair
  let H : ((k : Finset.Iic t) → Draw L K) → ℝ≥0∞ :=
    fun p => ∫⁻ d, F p d ∂pairKernel init t p
  have hH : Measurable (fun ω : Ω L K => H (frestrictLe t ω)) :=
    (measurable_of_countable H).comp (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) t)
  have hfreezeF (p : (k : Finset.Iic t) → Draw L K) :
      ∫⁻ ω, F (frestrictLe t ω) (ω (t + 1))
          ∂Kernel.traj (X := fun _ => Draw L K) κ t p = H p := by
    rw [Kernel.lintegral_traj (X := fun _ => Draw L K) p hF]
    have hfreeze : (fun y : Ω L K =>
        F (frestrictLe t (Function.updateFinset y (Finset.Iic t) p))
          ((Function.updateFinset y (Finset.Iic t) p) (t + 1))) =
        (fun y => F p (y (t + 1))) := by
      funext y
      rw [frestrictLe_updateFinset]
      simp [Function.updateFinset, Finset.mem_Iic, Nat.not_succ_le_self]
    rw [hfreeze]
    have hmap :
        Measure.map (fun y : Ω L K => y (t + 1))
          (Kernel.traj (X := fun _ => Draw L K) κ t p) = pairKernel init t p := by
      change (Kernel.traj (X := fun _ => Draw L K) κ t p).map
        (fun y : Ω L K => y (t + 1)) = κ t p
      rw [← Kernel.map_apply _ (measurable_pi_apply (t + 1)),
        Kernel.map_traj_succ_self]
    change _ = ∫⁻ d, F p d ∂pairKernel init t p
    rw [← hmap, lintegral_map (measurable_of_countable (F p)) (measurable_pi_apply (t + 1))]
  have hfreezeH (p : (k : Finset.Iic t) → Draw L K) :
      ∫⁻ ω, H (frestrictLe t ω) ∂Kernel.traj (X := fun _ => Draw L K) κ t p = H p := by
    rw [Kernel.lintegral_traj (X := fun _ => Draw L K) p hH]
    have hfreeze : (fun y : Ω L K =>
        H (frestrictLe t (Function.updateFinset y (Finset.Iic t) p))) =
        (fun _ => H p) := by
      funext y
      rw [frestrictLe_updateFinset]
    rw [hfreeze, lintegral_const, measure_univ, mul_one]
  rw [hlaw, hcomp, Kernel.lintegral_comp _ _ _ hF, Kernel.lintegral_comp _ _ _ hH]
  exact lintegral_congr fun p => (hfreezeF p).trans (hfreezeH p).symm

/-- The kernel average of a function of the next configuration. -/
theorem lintegral_pairKernel_applyDraw (init : Cfg L K) (t : ℕ)
    (p : (k : Finset.Iic t) → Draw L K) (g : Cfg L K → ℝ≥0∞) :
    ∫⁻ d, g (applyDraw (prefixCfg init t p) d) ∂pairKernel init t p =
      ∫⁻ c', g c' ∂(NonuniformMajority L K).transitionKernel (prefixCfg init t p) := by
  have hm : Measurable (applyDraw (prefixCfg init t p)) := by
    intro A _
    exact (Set.to_countable _).measurableSet
  change ∫⁻ d, g (applyDraw (prefixCfg init t p) d)
      ∂(drawLaw (prefixCfg init t p)).toMeasure = _
  rw [← drawLaw_map_toMeasure, lintegral_map (measurable_of_countable g) hm]

/-- Whether the trace has avoided `B` through time `t`, as a function of the prefix. -/
def AliveThrough (init : Cfg L K) (B : Cfg L K → Prop) (t : ℕ)
    (q : (k : Finset.Iic t) → Draw L K) : Prop :=
  ∀ s (hs : s ≤ t), ¬ B (prefixCfg init s (fun k => q ⟨k.val, Finset.mem_Iic.mpr
    (le_trans (Finset.mem_Iic.mp k.property) hs)⟩))

theorem aliveThrough_iff (init : Cfg L K) (B : Cfg L K → Prop) (t : ℕ) (ω : Ω L K) :
    AliveThrough init B t (frestrictLe t ω) ↔ (t : WithTop ℕ) < exitTime init B ω := by
  rw [← not_le, exitTime_le_iff]
  push_neg
  rfl

/-- Stopped multiplicative drift: if the kernel mean of `ψ` is at most `(1 - ρ) ψ` on
the window `W`, the trace stays in `W` through `N` with `ψ ≥ 1` at time `N` with
probability at most `(1 - ρ) ^ N ψ init`. -/
theorem potential_drift_tail (init : Cfg L K) (ψ : Cfg L K → ℕ) (W : Cfg L K → Prop)
    (ρ : ℝ≥0∞)
    (hdrift : ∀ c, W c →
      ∫⁻ c', (ψ c' : ℝ≥0∞) ∂(NonuniformMajority L K).transitionKernel c ≤
        (1 - ρ) * ψ c)
    (N : ℕ) :
    law init {ω | (N : WithTop ℕ) < exitTime init (fun c => ¬ W c) ω ∧
        1 ≤ ψ (trace init ω N)} ≤
      (1 - ρ) ^ N * ψ init := by
  let B : Cfg L K → Prop := fun c => ¬ W c
  let G : (t : ℕ) → ((k : Finset.Iic t) → Draw L K) → ℝ≥0∞ := fun t q =>
    if AliveThrough init B t q then (ψ (prefixCfg init t q) : ℝ≥0∞) else 0
  let Y : ℕ → Ω L K → ℝ≥0∞ := fun t ω => G t (frestrictLe t ω)
  have hY (t : ℕ) : Measurable (Y t) :=
    (measurable_of_countable (G t)).comp (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) t)
  have hYval (t : ℕ) (ω : Ω L K) :
      Y t ω = if (t : WithTop ℕ) < exitTime init B ω
        then (ψ (trace init ω t) : ℝ≥0∞) else 0 := by
    change (if AliveThrough init B t (frestrictLe t ω) then _ else _) = _
    rw [if_congr (aliveThrough_iff init B t ω) rfl rfl]
    rfl
  have hstep (t : ℕ) : ∫⁻ ω, Y (t + 1) ω ∂law init ≤ (1 - ρ) * ∫⁻ ω, Y t ω ∂law init := by
    let F : ((k : Finset.Iic t) → Draw L K) → Draw L K → ℝ≥0∞ := fun q d =>
      if AliveThrough init B t q then (ψ (applyDraw (prefixCfg init t q) d) : ℝ≥0∞) else 0
    have hle : ∀ ω, Y (t + 1) ω ≤ F (frestrictLe t ω) (ω (t + 1)) := by
      intro ω
      rw [hYval]
      split_ifs with h1
      · have h0 : (t : WithTop ℕ) < exitTime init B ω :=
          lt_of_le_of_lt (by exact_mod_cast Nat.le_succ t) h1
        have ha := (aliveThrough_iff init B t ω).2 h0
        change _ ≤ (if AliveThrough init B t (frestrictLe t ω) then _ else _)
        rw [if_pos ha]
        exact le_rfl
      · exact zero_le
    have hinner : ∀ ω, ∫⁻ d, F (frestrictLe t ω) d ∂pairKernel init t (frestrictLe t ω) ≤
        (1 - ρ) * Y t ω := by
      intro ω
      change _ ≤ (1 - ρ) * (if AliveThrough init B t (frestrictLe t ω) then _ else _)
      by_cases ha : AliveThrough init B t (frestrictLe t ω)
      · simp only [F, if_pos ha]
        rw [lintegral_pairKernel_applyDraw init t _ (fun c => (ψ c : ℝ≥0∞))]
        have hW : W (prefixCfg init t (frestrictLe t ω)) := by
          have := ha t le_rfl
          simpa [B] using this
        exact hdrift _ hW
      · simp only [F, if_neg ha, lintegral_zero, mul_zero, le_refl]
    calc ∫⁻ ω, Y (t + 1) ω ∂law init
        ≤ ∫⁻ ω, F (frestrictLe t ω) (ω (t + 1)) ∂law init := lintegral_mono hle
      _ = ∫⁻ ω, (∫⁻ d, F (frestrictLe t ω) d ∂pairKernel init t (frestrictLe t ω))
            ∂law init := lintegral_prefix_next init t F
      _ ≤ ∫⁻ ω, (1 - ρ) * Y t ω ∂law init := lintegral_mono hinner
      _ = (1 - ρ) * ∫⁻ ω, Y t ω ∂law init := lintegral_const_mul _ (hY t)
  have hexp : ∀ t, ∫⁻ ω, Y t ω ∂law init ≤ (1 - ρ) ^ t * ψ init := by
    intro t
    induction t with
    | zero =>
        have h0 : ∀ ω, Y 0 ω ≤ (ψ init : ℝ≥0∞) := by
          intro ω
          rw [hYval]
          split_ifs
          · exact le_rfl
          · exact zero_le
        calc ∫⁻ ω, Y 0 ω ∂law init ≤ ∫⁻ _ω, (ψ init : ℝ≥0∞) ∂law init := lintegral_mono h0
          _ = (1 - ρ) ^ 0 * ψ init := by
            rw [lintegral_const, measure_univ, mul_one, pow_zero, one_mul]
    | succ t ih =>
        calc ∫⁻ ω, Y (t + 1) ω ∂law init ≤ (1 - ρ) * ∫⁻ ω, Y t ω ∂law init := hstep t
          _ ≤ (1 - ρ) * ((1 - ρ) ^ t * ψ init) := by gcongr
          _ = (1 - ρ) ^ (t + 1) * ψ init := by ring
  have hsub : {ω | (N : WithTop ℕ) < exitTime init B ω ∧ 1 ≤ ψ (trace init ω N)} ⊆
      {ω | 1 ≤ Y N ω} := by
    rintro ω ⟨h1, h2⟩
    change 1 ≤ Y N ω
    rw [hYval, if_pos h1]
    exact_mod_cast h2
  calc law init {ω | (N : WithTop ℕ) < exitTime init B ω ∧ 1 ≤ ψ (trace init ω N)}
      ≤ law init {ω | 1 ≤ Y N ω} := measure_mono hsub
    _ = 1 * law init {ω | 1 ≤ Y N ω} := (one_mul _).symm
    _ ≤ ∫⁻ ω, Y N ω ∂law init := mul_meas_ge_le_lintegral₀ (hY N).aemeasurable 1
    _ ≤ (1 - ρ) ^ N * ψ init := hexp N

/-! ## Drift from a past-measurable start -/

/-- Restrict a recorded prefix to an earlier horizon. -/
def restrictPrefix {a b : ℕ} (h : a ≤ b) (q : (k : Finset.Iic b) → Draw L K) :
    (k : Finset.Iic a) → Draw L K :=
  fun k => q ⟨k.val, Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp k.property) h)⟩

theorem restrictPrefix_frestrictLe {a b : ℕ} (h : a ≤ b) (ω : Ω L K) :
    restrictPrefix h (frestrictLe (π := fun _ : ℕ => Draw L K) b ω) =
      frestrictLe (π := fun _ : ℕ => Draw L K) a ω := rfl

/-- Stopped multiplicative drift from a start time `s`, on a recorded-past event `A`
at `s`: if the kernel mean of `ψ` is at most `(1 - ρ) ψ` on `W` and `ψ ≤ Ψ` at time
`s` on `A`, then the trace stays in `W` on `[s, s + N)` with `ψ ≥ 1` at `s + N` on `A`
with probability at most `(1 - ρ) ^ N Ψ P(A)`. -/
theorem potential_drift_tail_from (init : Cfg L K) (ψ : Cfg L K → ℕ)
    (W : Cfg L K → Prop) (ρ : ℝ≥0∞)
    (hdrift : ∀ c, W c →
      ∫⁻ c', (ψ c' : ℝ≥0∞) ∂(NonuniformMajority L K).transitionKernel c ≤
        (1 - ρ) * ψ c)
    (s N : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K)) (Ψ : ℕ)
    (hΨ : ∀ p ∈ A, ψ (prefixCfg init s p) ≤ Ψ) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        (∀ u, s ≤ u → u < s + N → W (trace init ω u)) ∧
        1 ≤ ψ (trace init ω (s + N))} ≤
      (1 - ρ) ^ N * Ψ * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  let Cond : (t : ℕ) → ((k : Finset.Iic (s + t)) → Draw L K) → Prop := fun t q =>
    restrictPrefix (Nat.le_add_right s t) q ∈ A ∧
      ∀ u (hu : s ≤ u) (hu' : u < s + t),
        W (prefixCfg init u (restrictPrefix (by omega : u ≤ s + t) q))
  have hCond (t : ℕ) (ω : Ω L K) :
      Cond t (frestrictLe (s + t) ω) ↔ frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ∀ u, s ≤ u → u < s + t → W (trace init ω u) := Iff.rfl
  let G : (t : ℕ) → ((k : Finset.Iic (s + t)) → Draw L K) → ℝ≥0∞ := fun t q =>
    if Cond t q then (ψ (prefixCfg init (s + t) q) : ℝ≥0∞) else 0
  let Y : ℕ → Ω L K → ℝ≥0∞ := fun t ω => G t (frestrictLe (s + t) ω)
  have hY (t : ℕ) : Measurable (Y t) :=
    (measurable_of_countable (G t)).comp
      (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) (s + t))
  have hYval (t : ℕ) (ω : Ω L K) :
      Y t ω = if (frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧ ∀ u, s ≤ u → u < s + t → W (trace init ω u))
        then (ψ (trace init ω (s + t)) : ℝ≥0∞) else 0 := by
    change (if Cond t (frestrictLe (s + t) ω) then _ else _) = _
    rw [if_congr (hCond t ω) rfl rfl]
    rfl
  have hstep (t : ℕ) : ∫⁻ ω, Y (t + 1) ω ∂law init ≤ (1 - ρ) * ∫⁻ ω, Y t ω ∂law init := by
    let F : ((k : Finset.Iic (s + t)) → Draw L K) → Draw L K → ℝ≥0∞ := fun q d =>
      if Cond t q ∧ W (prefixCfg init (s + t) q)
      then (ψ (applyDraw (prefixCfg init (s + t) q) d) : ℝ≥0∞) else 0
    have hle : ∀ ω, Y (t + 1) ω ≤ F (frestrictLe (s + t) ω) (ω (s + t + 1)) := by
      intro ω
      rw [hYval]
      split_ifs with h1
      · have hc : Cond t (frestrictLe (s + t) ω) ∧
            W (prefixCfg init (s + t) (frestrictLe (s + t) ω)) := by
          refine ⟨(hCond t ω).2 ⟨h1.1, fun u hu hu' => h1.2 u hu (by omega)⟩, ?_⟩
          exact h1.2 (s + t) (by omega) (by omega)
        change _ ≤ (if Cond t (frestrictLe (s + t) ω) ∧
          W (prefixCfg init (s + t) (frestrictLe (s + t) ω)) then _ else _)
        rw [if_pos hc]
        exact le_rfl
      · exact zero_le
    have hinner : ∀ ω, ∫⁻ d, F (frestrictLe (s + t) ω) d
          ∂pairKernel init (s + t) (frestrictLe (s + t) ω) ≤ (1 - ρ) * Y t ω := by
      intro ω
      change _ ≤ (1 - ρ) * (if Cond t (frestrictLe (s + t) ω) then _ else _)
      by_cases hc : Cond t (frestrictLe (s + t) ω) ∧
          W (prefixCfg init (s + t) (frestrictLe (s + t) ω))
      · simp only [F, if_pos hc, if_pos hc.1]
        rw [lintegral_pairKernel_applyDraw init (s + t) _ (fun c => (ψ c : ℝ≥0∞))]
        exact hdrift _ hc.2
      · simp only [F, if_neg hc, lintegral_zero]
        exact zero_le
    calc ∫⁻ ω, Y (t + 1) ω ∂law init
        ≤ ∫⁻ ω, F (frestrictLe (s + t) ω) (ω (s + t + 1)) ∂law init := lintegral_mono hle
      _ = ∫⁻ ω, (∫⁻ d, F (frestrictLe (s + t) ω) d
            ∂pairKernel init (s + t) (frestrictLe (s + t) ω)) ∂law init :=
          lintegral_prefix_next init (s + t) F
      _ ≤ ∫⁻ ω, (1 - ρ) * Y t ω ∂law init := lintegral_mono hinner
      _ = (1 - ρ) * ∫⁻ ω, Y t ω ∂law init := lintegral_const_mul _ (hY t)
  have hA : MeasurableSet {ω : Ω L K | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} :=
    (Set.to_countable A).measurableSet.preimage
      (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) s)
  have hexp : ∀ t, ∫⁻ ω, Y t ω ∂law init ≤
      (1 - ρ) ^ t * Ψ * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
    intro t
    induction t with
    | zero =>
        have h0 : ∀ ω, Y 0 ω ≤ {ω : Ω L K | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}.indicator
            (fun _ => (Ψ : ℝ≥0∞)) ω := by
          intro ω
          rw [hYval]
          split_ifs with h
          · rw [Set.indicator_of_mem (show ω ∈ {ω : Ω L K | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} from h.1)]
            exact_mod_cast hΨ _ h.1
          · exact zero_le
        calc ∫⁻ ω, Y 0 ω ∂law init
            ≤ ∫⁻ ω, {ω : Ω L K | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}.indicator
                (fun _ => (Ψ : ℝ≥0∞)) ω ∂law init := lintegral_mono h0
          _ = (1 - ρ) ^ 0 * Ψ * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
            rw [lintegral_indicator_const hA, pow_zero, one_mul]
    | succ t ih =>
        calc ∫⁻ ω, Y (t + 1) ω ∂law init ≤ (1 - ρ) * ∫⁻ ω, Y t ω ∂law init := hstep t
          _ ≤ (1 - ρ) * ((1 - ρ) ^ t * Ψ * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}) := by
            gcongr
          _ = (1 - ρ) ^ (t + 1) * Ψ * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by ring
  have hsub : {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        (∀ u, s ≤ u → u < s + N → W (trace init ω u)) ∧
        1 ≤ ψ (trace init ω (s + N))} ⊆ {ω | 1 ≤ Y N ω} := by
    rintro ω ⟨h1, h2, h3⟩
    change 1 ≤ Y N ω
    rw [hYval, if_pos ⟨h1, h2⟩]
    exact_mod_cast h3
  calc law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        (∀ u, s ≤ u → u < s + N → W (trace init ω u)) ∧
        1 ≤ ψ (trace init ω (s + N))}
      ≤ law init {ω | 1 ≤ Y N ω} := measure_mono hsub
    _ = 1 * law init {ω | 1 ≤ Y N ω} := (one_mul _).symm
    _ ≤ ∫⁻ ω, Y N ω ∂law init := mul_meas_ge_le_lintegral₀ (hY N).aemeasurable 1
    _ ≤ _ := hexp N

/-- A strict one-step drop of probability at least `r`, with `ψ` never increasing,
makes `2 ^ ψ` contract by the factor `1 - r / 2` in kernel mean. -/
theorem exp_drift_of_drop (ψ : Cfg L K → ℕ) (c : Cfg L K)
    (hmono : ∀ d, ψ (applyDraw c d) ≤ ψ c) (r : ℝ≥0∞)
    (hr : r ≤ (NonuniformMajority L K).transitionKernel c {c' | ψ c' + 1 ≤ ψ c}) :
    ∫⁻ c', ((2 ^ ψ c' : ℕ) : ℝ≥0∞) ∂(NonuniformMajority L K).transitionKernel c ≤
      (1 - r / 2) * ((2 ^ ψ c : ℕ) : ℝ≥0∞) := by
  set μ := (drawLaw c).toMeasure
  have hm : Measurable (applyDraw c) := by
    intro B _
    exact (Set.to_countable _).measurableSet
  let D : Set (Draw L K) := {d | ψ (applyDraw c d) + 1 ≤ ψ c}
  have hD : MeasurableSet D := (Set.to_countable D).measurableSet
  have hμD : (NonuniformMajority L K).transitionKernel c {c' | ψ c' + 1 ≤ ψ c} = μ D := by
    rw [← drawLaw_map_toMeasure, Measure.map_apply hm (Set.to_countable _).measurableSet]
    rfl
  set a : ℝ≥0∞ := ((2 ^ ψ c : ℕ) : ℝ≥0∞)
  have ha : a ≠ ⊤ := ENNReal.natCast_ne_top _
  have hpt : ∀ d, ((2 ^ ψ (applyDraw c d) : ℕ) : ℝ≥0∞) ≤
      D.indicator (fun _ => a / 2) d + Dᶜ.indicator (fun _ => a) d := by
    intro d
    by_cases hd : d ∈ D
    · rw [Set.indicator_of_mem hd, Set.indicator_of_notMem (show d ∉ Dᶜ from fun h => h hd),
        add_zero]
      have h2 : 2 ^ ψ (applyDraw c d) * 2 ≤ 2 ^ ψ c := by
        rw [← pow_succ]
        exact Nat.pow_le_pow_right (by norm_num : 2 > 0) hd
      rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
      show ((2 ^ ψ (applyDraw c d) : ℕ) : ℝ≥0∞) * 2 ≤ ((2 ^ ψ c : ℕ) : ℝ≥0∞)
      exact_mod_cast h2
    · rw [Set.indicator_of_notMem hd, Set.indicator_of_mem (show d ∈ Dᶜ from hd), zero_add]
      show ((2 ^ ψ (applyDraw c d) : ℕ) : ℝ≥0∞) ≤ ((2 ^ ψ c : ℕ) : ℝ≥0∞)
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 2 > 0) (hmono d)
  have hmD : μ D ≤ 1 := prob_le_one
  calc ∫⁻ c', ((2 ^ ψ c' : ℕ) : ℝ≥0∞) ∂(NonuniformMajority L K).transitionKernel c
      = ∫⁻ d, ((2 ^ ψ (applyDraw c d) : ℕ) : ℝ≥0∞) ∂μ := by
        rw [← drawLaw_map_toMeasure, lintegral_map (measurable_of_countable _) hm]
    _ ≤ ∫⁻ d, (D.indicator (fun _ => a / 2) d + Dᶜ.indicator (fun _ => a) d) ∂μ :=
        lintegral_mono hpt
    _ = a / 2 * μ D + a * μ Dᶜ := by
        rw [lintegral_add_left ((measurable_const.indicator hD)),
          lintegral_indicator_const hD, lintegral_indicator_const hD.compl]
    _ = a * (1 - μ D / 2) := by
        rw [prob_compl_eq_one_sub hD]
        have hsum : (1 - μ D) + μ D / 2 + μ D / 2 = 1 := by
          rw [add_assoc, ENNReal.add_halves, tsub_add_cancel_of_le hmD]
        have hdiv : μ D / 2 ≠ ⊤ := ENNReal.div_ne_top (measure_ne_top _ _) two_ne_zero
        have hq : (1 - μ D) + μ D / 2 = 1 - μ D / 2 := ENNReal.eq_sub_of_add_eq hdiv hsum
        rw [← hq, mul_add]
        simp only [div_eq_mul_inv]
        ring
    _ ≤ (1 - r / 2) * a := by
        rw [mul_comm]
        gcongr
        rw [← hμD]
        exact hr

/-- Exit tail from a growth drift. If a potential `φ` grows by at most the factor
`κ ≥ 1` in kernel mean on the window `W`, and `φ ≥ thr` off `W`, then on a
recorded-past event `A` at `s` with `φ ≤ Ψ` at `s`, the probability that the trace
leaves `W` at some time in `[s, s + T]` is at most `κ ^ T Ψ P(A) / thr`. -/
theorem growth_exit_tail_from (init : Cfg L K) (φ : Cfg L K → ℝ≥0∞)
    (W : Cfg L K → Prop) (κ : ℝ≥0∞) (hκ : 1 ≤ κ)
    (hdrift : ∀ c, W c →
      ∫⁻ c', φ c' ∂(NonuniformMajority L K).transitionKernel c ≤ κ * φ c)
    (thr : ℝ≥0∞) (hthr : ∀ c, ¬ W c → thr ≤ φ c)
    (s T : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K)) (Ψ : ℝ≥0∞)
    (hΨ : ∀ p ∈ A, φ (prefixCfg init s p) ≤ Ψ) :
    thr * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ∃ u, s ≤ u ∧ u ≤ s + T ∧ ¬ W (trace init ω u)} ≤
      κ ^ T * Ψ * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  let Alive : (t : ℕ) → ((k : Finset.Iic (s + t)) → Draw L K) → Prop := fun t q =>
    ∀ u (hu : s ≤ u) (hu' : u ≤ s + t),
      W (prefixCfg init u (restrictPrefix (by omega : u ≤ s + t) q))
  let G : (t : ℕ) → ((k : Finset.Iic (s + t)) → Draw L K) → ℝ≥0∞ := fun t q =>
    if restrictPrefix (Nat.le_add_right s t) q ∈ A then
      (if Alive t q then φ (prefixCfg init (s + t) q) else thr) else 0
  let V : ℕ → Ω L K → ℝ≥0∞ := fun t ω => G t (frestrictLe (s + t) ω)
  have hV (t : ℕ) : Measurable (V t) :=
    (measurable_of_countable (G t)).comp
      (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) (s + t))
  have hVval (t : ℕ) (ω : Ω L K) :
      V t ω = if frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A then
        (if (∀ u, s ≤ u → u ≤ s + t → W (trace init ω u))
          then φ (trace init ω (s + t)) else thr) else 0 := by
    show G t (frestrictLe (s + t) ω) = _
    simp only [G, Alive, restrictPrefix_frestrictLe, trace]
    split_ifs <;> rfl
  have hstep (t : ℕ) : ∫⁻ ω, V (t + 1) ω ∂law init ≤ κ * ∫⁻ ω, V t ω ∂law init := by
    let F : ((k : Finset.Iic (s + t)) → Draw L K) → Draw L K → ℝ≥0∞ := fun q d =>
      if restrictPrefix (Nat.le_add_right s t) q ∈ A then
        (if Alive t q then φ (applyDraw (prefixCfg init (s + t) q) d) else thr) else 0
    have hle : ∀ ω, V (t + 1) ω ≤ F (frestrictLe (s + t) ω) (ω (s + t + 1)) := by
      intro ω
      rw [hVval]
      simp only [F, Alive, restrictPrefix_frestrictLe]
      split_ifs with hA h1 h2 h2
      · exact le_rfl
      · exact (h2 fun u hu hu' => h1 u hu (by omega)).elim
      · exact hthr _ (fun hw => h1 fun u hu hu' => by
          rcases Nat.lt_or_ge u (s + t + 1) with h | h
          · exact h2 u hu (by omega)
          · obtain rfl : u = s + t + 1 := by omega
            exact hw)
      · exact le_rfl
      · exact le_rfl
    have hinner : ∀ ω, ∫⁻ d, F (frestrictLe (s + t) ω) d
          ∂pairKernel init (s + t) (frestrictLe (s + t) ω) ≤ κ * V t ω := by
      intro ω
      change _ ≤ κ * (if restrictPrefix (Nat.le_add_right s t) (frestrictLe (s + t) ω) ∈ A then
        (if Alive t (frestrictLe (s + t) ω) then φ (prefixCfg init (s + t)
          (frestrictLe (s + t) ω)) else thr) else 0)
      by_cases hA : restrictPrefix (Nat.le_add_right s t) (frestrictLe (s + t) ω) ∈ A
      · by_cases hal : Alive t (frestrictLe (s + t) ω)
        · simp only [F, if_pos hA, if_pos hal]
          rw [lintegral_pairKernel_applyDraw init (s + t) _ φ]
          exact hdrift _ (hal (s + t) (by omega) le_rfl)
        · simp only [F, if_pos hA, if_neg hal, lintegral_const, measure_univ, mul_one]
          calc thr = 1 * thr := (one_mul _).symm
            _ ≤ κ * thr := by gcongr
      · simp only [F, if_neg hA, lintegral_zero, mul_zero, le_refl]
    calc ∫⁻ ω, V (t + 1) ω ∂law init
        ≤ ∫⁻ ω, F (frestrictLe (s + t) ω) (ω (s + t + 1)) ∂law init := lintegral_mono hle
      _ = ∫⁻ ω, (∫⁻ d, F (frestrictLe (s + t) ω) d
            ∂pairKernel init (s + t) (frestrictLe (s + t) ω)) ∂law init :=
          lintegral_prefix_next init (s + t) F
      _ ≤ ∫⁻ ω, κ * V t ω ∂law init := lintegral_mono hinner
      _ = κ * ∫⁻ ω, V t ω ∂law init := lintegral_const_mul _ (hV t)
  have hA : MeasurableSet {ω : Ω L K | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} :=
    (Set.to_countable A).measurableSet.preimage
      (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) s)
  have hexp : ∀ t, ∫⁻ ω, V t ω ∂law init ≤ κ ^ t * Ψ * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
    intro t
    induction t with
    | zero =>
        have h0 : ∀ ω, V 0 ω ≤ {ω : Ω L K | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}.indicator (fun _ => Ψ) ω := by
          intro ω
          rw [hVval]
          by_cases hA' : frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A
          · rw [if_pos hA', Set.indicator_of_mem (show ω ∈ {ω : Ω L K | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}
              from hA')]
            have hb : φ (trace init ω s) ≤ Ψ := hΨ _ hA'
            split_ifs with hal
            · exact hb
            · have hnot : ¬ W (trace init ω s) := fun hw =>
                hal fun u hu hu' => by
                  have : u = s := by omega
                  subst this
                  exact hw
              exact (hthr _ hnot).trans hb
          · rw [if_neg hA']
            exact zero_le
        calc ∫⁻ ω, V 0 ω ∂law init
            ≤ ∫⁻ ω, {ω : Ω L K | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}.indicator (fun _ => Ψ) ω ∂law init :=
              lintegral_mono h0
          _ = κ ^ 0 * Ψ * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
            rw [lintegral_indicator_const hA, pow_zero, one_mul]
    | succ t ih =>
        calc ∫⁻ ω, V (t + 1) ω ∂law init ≤ κ * ∫⁻ ω, V t ω ∂law init := hstep t
          _ ≤ κ * (κ ^ t * Ψ * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}) := by gcongr
          _ = κ ^ (t + 1) * Ψ * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by ring
  have hsub : {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ∃ u, s ≤ u ∧ u ≤ s + T ∧ ¬ W (trace init ω u)} ⊆ {ω | thr ≤ V T ω} := by
    rintro ω ⟨h1, u, hu, hu', hw⟩
    change thr ≤ V T ω
    rw [hVval, if_pos h1, if_neg (fun h => hw (h u hu hu'))]
  calc thr * law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ∃ u, s ≤ u ∧ u ≤ s + T ∧ ¬ W (trace init ω u)}
      ≤ thr * law init {ω | thr ≤ V T ω} := mul_le_mul_left' (measure_mono hsub) _
    _ ≤ ∫⁻ ω, V T ω ∂law init := mul_meas_ge_le_lintegral₀ (hV T).aemeasurable thr
    _ ≤ _ := hexp T

end Ripple.PopulationProtocol.ExactMajority.TraceDrain

end

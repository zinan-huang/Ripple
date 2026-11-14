-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingCompensatedLog.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingRecordedProcess
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCancellationAlgebra
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingIntegerPotential

/-!
# The sampled-exit compensated logarithmic process

The gate is checked on the actual sampled successor. A failed next gate gives
the entire compensated increment -b. Once any gate or target test fails, the
history predicate remains false and all subsequent increments are zero.

Clipping only makes the process bounded on arbitrary prefixes. On every live
step satisfying LogControl it is inactive. The conditional drift is proved
from the full next-state potential drift, including gate-exit draws.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingCompensatedLog

open TimeTheorem PairLog TraceDrain
open AveragingRecordedExpectation AveragingRecordedProcess
open AveragingCancellationAlgebra

variable {L K : ℕ}

def clip (b x : ℝ) : ℝ := max (-b) (min b x)

theorem clip_abs_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : |clip b x| ≤ b := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clip_eq {b x : ℝ} (hx : |x| ≤ b) : clip b x = x := by
  rw [clip, min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]

def edgeIncrement (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop)
    (r b : ℝ) (t : ℕ) (c : Cfg L K) (d : Draw L K) : ℝ := by
  classical
  exact if G (t + 1) (applyDraw c d) then
    clip b (Real.log (φ (applyDraw c d) : ℝ) - Real.log (φ c : ℝ) + r)
  else -b

theorem edgeIncrement_abs_le (φ : Cfg L K → ℕ)
    (G : ℕ → Cfg L K → Prop) (r b : ℝ) (hb : 0 ≤ b)
    (t : ℕ) (c : Cfg L K) (d : Draw L K) :
    |edgeIncrement φ G r b t c d| ≤ b := by
  classical
  unfold edgeIncrement
  split_ifs
  · exact clip_abs_le hb _
  · simp only [abs_neg, abs_of_nonneg hb, le_refl]

/-- These are one-step facts on current live configurations, not probability
estimates or assumptions of an already constructed supermartingale. -/
structure LogControl (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop)
    (θ r b D : ℝ) : Prop where
  threshold_pos : 0 < θ
  rate_nonneg : 0 ≤ r
  radius_nonneg : 0 ≤ b
  drop_nonneg : 0 ≤ D
  drop_small : D ≤ θ / 2
  radius_bound : 2 * D / θ + r ≤ b
  potential_mono : ∀ t c, G t c → ∀ d, φ (applyDraw c d) ≤ φ c
  drop_bound : ∀ t c, G t c → ∀ d,
    (φ c : ℝ) - (φ (applyDraw c d) : ℝ) ≤ D
  full_drift : ∀ t c, G t c →
    (∫ d, (φ (applyDraw c d) : ℝ) ∂(drawLaw c).toMeasure) ≤
      (1 - r) * (φ c : ℝ)

theorem live_log_step_bounds (φ : Cfg L K → ℕ)
    (G : ℕ → Cfg L K → Prop) (θ r b D : ℝ)
    (hc : LogControl φ G θ r b D)
    (t : ℕ) (c : Cfg L K) (hg : G t c) (hx : θ < (φ c : ℝ))
    (d : Draw L K) :
    0 < (φ (applyDraw c d) : ℝ) ∧
      |Real.log (φ (applyDraw c d) : ℝ) - Real.log (φ c : ℝ) + r| ≤ b := by
  have hxpos := hc.threshold_pos.trans hx
  have hmono : (φ (applyDraw c d) : ℝ) ≤ (φ c : ℝ) := by
    exact_mod_cast hc.potential_mono t c hg d
  have hlog := log_decrease_abs_le hxpos hmono
    (hc.drop_bound t c hg d) (by linarith [hc.drop_small])
  have hquot : 2 * D / (φ c : ℝ) ≤ 2 * D / θ := by
    apply (div_le_div_iff₀ hxpos hc.threshold_pos).2
    exact mul_le_mul_of_nonneg_left hx.le (mul_nonneg (by norm_num) hc.drop_nonneg)
  refine ⟨hlog.1, ?_⟩
  calc
    |Real.log (φ (applyDraw c d) : ℝ) - Real.log (φ c : ℝ) + r| ≤
        |Real.log (φ (applyDraw c d) : ℝ) - Real.log (φ c : ℝ)| + |r| :=
      abs_add_le _ _
    _ ≤ 2 * D / (φ c : ℝ) + r := by
      rw [abs_of_nonneg hc.rate_nonneg]
      exact add_le_add hlog.2 le_rfl
    _ ≤ 2 * D / θ + r := add_le_add hquot le_rfl
    _ ≤ b := hc.radius_bound

/-- The sampled -b replacement is below the valid compensated increment.
Thus the full drift remains an upper bound even on exit draws. -/
theorem edgeIncrement_mean_le_zero (φ : Cfg L K → ℕ)
    (G : ℕ → Cfg L K → Prop) (θ r b D : ℝ)
    (hc : LogControl φ G θ r b D)
    (t : ℕ) (c : Cfg L K) (hg : G t c) (hx : θ < (φ c : ℝ)) :
    (∫ d, edgeIncrement φ G r b t c d ∂(drawLaw c).toMeasure) ≤ 0 := by
  classical
  let μ := (drawLaw c).toMeasure
  have hxpos := hc.threshold_pos.trans hx
  have hφint : Integrable (fun d => (φ (applyDraw c d) : ℝ)) μ := by
    refine (integrable_const (φ c : ℝ)).mono'
      (measurable_of_countable _).aestronglyMeasurable ?_
    exact ae_of_all μ fun d => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast hc.potential_mono t c hg d
  have heint : Integrable (edgeIncrement φ G r b t c) μ := by
    refine (integrable_const b).mono'
      (measurable_of_countable _).aestronglyMeasurable ?_
    exact ae_of_all μ fun d => by
      rw [Real.norm_eq_abs]
      exact edgeIncrement_abs_le φ G r b hc.radius_nonneg t c d
  have hlinint : Integrable
      (fun d => (φ (applyDraw c d) : ℝ) / (φ c : ℝ) - 1 + r) μ :=
    ((hφint.div_const _).sub (integrable_const (1 : ℝ))).add (integrable_const r)
  have hpoint (d : Draw L K) :
      edgeIncrement φ G r b t c d ≤
        (φ (applyDraw c d) : ℝ) / (φ c : ℝ) - 1 + r := by
    have hstep := live_log_step_bounds φ G θ r b D hc t c hg hx d
    have hlog := Real.log_le_sub_one_of_pos (div_pos hstep.1 hxpos)
    rw [Real.log_div hstep.1.ne' hxpos.ne'] at hlog
    by_cases hnext : G (t + 1) (applyDraw c d)
    · rw [edgeIncrement, if_pos hnext, clip_eq hstep.2]
      linarith
    · rw [edgeIncrement, if_neg hnext]
      exact (abs_le.mp hstep.2).1.trans (by linarith)
  have hdiv :
      (∫ d, (φ (applyDraw c d) : ℝ) ∂μ) / (φ c : ℝ) ≤ 1 - r :=
    (div_le_iff₀ hxpos).2 (hc.full_drift t c hg)
  calc
    (∫ d, edgeIncrement φ G r b t c d ∂μ) ≤
        ∫ d, ((φ (applyDraw c d) : ℝ) / (φ c : ℝ) - 1 + r) ∂μ :=
      integral_mono heint hlinint hpoint
    _ = (∫ d, (φ (applyDraw c d) : ℝ) ∂μ) / (φ c : ℝ) - 1 + r := by
      have hdivint : Integrable
          (fun d => (φ (applyDraw c d) : ℝ) / (φ c : ℝ)) μ := hφint.div_const _
      have hsubint : Integrable
          (fun d => (φ (applyDraw c d) : ℝ) / (φ c : ℝ) - 1) μ :=
        hdivint.sub (integrable_const (1 : ℝ))
      rw [integral_add hsubint (integrable_const r),
        integral_sub hdivint (integrable_const (1 : ℝ)), integral_div]
      simp
    _ ≤ 0 := by linarith

def Alive (init : Cfg L K) (s : ℕ) (φ : Cfg L K → ℕ)
    (G : ℕ → Cfg L K → Prop) (θ : ℝ) (t : ℕ) (ω : Ω L K) : Prop :=
  ∀ u, u ≤ t →
    G (s + u) (trace init ω (s + u)) ∧ θ < (φ (trace init ω (s + u)) : ℝ)

def prefixAlive (init : Cfg L K) (s : ℕ) (φ : Cfg L K → ℕ)
    (G : ℕ → Cfg L K → Prop) (θ : ℝ) (t : ℕ)
    (p : (i : Finset.Iic (s + t)) → Draw L K) : Prop :=
  ∀ u (hu : u ≤ t),
    G (s + u) (prefixCfg init (s + u)
      (restrictPrefix (Nat.add_le_add_left hu s) p)) ∧
    θ < (φ (prefixCfg init (s + u)
      (restrictPrefix (Nat.add_le_add_left hu s) p)) : ℝ)

theorem prefixAlive_frestrict_iff (init : Cfg L K) (s : ℕ)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ : ℝ)
    (t : ℕ) (ω : Ω L K) :
    prefixAlive init s φ G θ t
      (frestrictLe (π := fun _ : ℕ => Draw L K) (s + t) ω) ↔
      Alive init s φ G θ t ω := by
  rfl

theorem alive_of_le (init : Cfg L K) (s : ℕ)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ : ℝ)
    (ω : Ω L K) {u v : ℕ} (huv : u ≤ v)
    (h : Alive init s φ G θ v ω) : Alive init s φ G θ u ω :=
  fun k hk => h k (hk.trans huv)

def stoppedFamily (init : Cfg L K) (s : ℕ) (φ : Cfg L K → ℕ)
    (G : ℕ → Cfg L K → Prop) (θ r b : ℝ) : IncrementFamily L K s := by
  classical
  exact fun t p d =>
    if prefixAlive init s φ G θ t p then
      edgeIncrement φ G r b (s + t) (prefixCfg init (s + t) p) d
    else 0

abbrev logProcess (init : Cfg L K) (s : ℕ) (φ : Cfg L K → ℕ)
    (G : ℕ → Cfg L K → Prop) (θ r b : ℝ) :=
  recordedSum s (stoppedFamily init s φ G θ r b)

theorem stoppedFamily_abs_le (init : Cfg L K) (s : ℕ)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b : ℝ)
    (hb : 0 ≤ b) (t : ℕ) (p : (i : Finset.Iic (s + t)) → Draw L K)
    (d : Draw L K) : |stoppedFamily init s φ G θ r b t p d| ≤ b := by
  classical
  unfold stoppedFamily
  split_ifs
  · exact edgeIncrement_abs_le φ G r b hb _ _ _
  · simpa only [abs_zero]

theorem stoppedFamily_mean_le_zero (init : Cfg L K) (s : ℕ)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b D : ℝ)
    (hc : LogControl φ G θ r b D)
    (t : ℕ) (p : (i : Finset.Iic (s + t)) → Draw L K) :
    (∫ d, stoppedFamily init s φ G θ r b t p d ∂pairKernel init (s + t) p) ≤ 0 := by
  classical
  by_cases hp : prefixAlive init s φ G θ t p
  · have hcur := hp t le_rfl
    change G (s + t) (prefixCfg init (s + t) p) ∧
      θ < (φ (prefixCfg init (s + t) p) : ℝ) at hcur
    simpa only [stoppedFamily, if_pos hp] using
      edgeIncrement_mean_le_zero φ G θ r b D hc (s + t)
        (prefixCfg init (s + t) p) hcur.1 hcur.2
  · simp only [stoppedFamily, if_neg hp, integral_zero, le_refl]

theorem stopped_log_conditional_drift (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b D : ℝ)
    (hc : LogControl φ G θ r b D) (t : ℕ) :
    (recordedFuture init s p)[recordedIncrement s (stoppedFamily init s φ G θ r b) t |
        shiftedPairLog L K s t] ≤ᵐ[recordedFuture init s p] (0 : Ω L K → ℝ) :=
  recordedIncrement_condExp_le init s p _ b
    (stoppedFamily_abs_le init s φ G θ r b hc.radius_nonneg)
    (stoppedFamily_mean_le_zero init s φ G θ r b D hc) t

theorem compensatedLog_stronglyAdapted (init : Cfg L K) (s : ℕ)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b : ℝ) :
    StronglyAdapted (shiftedPairLog L K s) (logProcess init s φ G θ r b) :=
  recordedSum_stronglyAdapted s _

theorem compensatedLog_integrable (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b : ℝ)
    (hb : 0 ≤ b) (t : ℕ) :
    Integrable (logProcess init s φ G θ r b t) (recordedFuture init s p) :=
  recordedSum_integrable _ s _ b
    (stoppedFamily_abs_le init s φ G θ r b hb) t

theorem compensatedLog_supermartingale (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b D : ℝ)
    (hc : LogControl φ G θ r b D) :
    Supermartingale (logProcess init s φ G θ r b) (shiftedPairLog L K s)
      (recordedFuture init s p) :=
  recordedSum_supermartingale init s p _ b
    (stoppedFamily_abs_le init s φ G θ r b hc.radius_nonneg)
    (stoppedFamily_mean_le_zero init s φ G θ r b D hc)

theorem increment_zero_after_failure (init : Cfg L K) (s : ℕ)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b : ℝ)
    (t : ℕ) (ω : Ω L K) (hdead : ¬ Alive init s φ G θ t ω) :
    recordedIncrement s (stoppedFamily init s φ G θ r b) t ω = 0 := by
  classical
  have hp : ¬ prefixAlive init s φ G θ t
      (frestrictLe (π := fun _ : ℕ => Draw L K) (s + t) ω) :=
    fun h => hdead ((prefixAlive_frestrict_iff init s φ G θ t ω).mp h)
  simp only [recordedIncrement, recordedNext, stoppedFamily, if_neg hp]

theorem sampled_gate_exit_decrement (init : Cfg L K) (s : ℕ)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b : ℝ)
    (t : ℕ) (ω : Ω L K) (halive : Alive init s φ G θ t ω)
    (hexit : ¬ G (s + t + 1) (trace init ω (s + t + 1))) :
    recordedIncrement s (stoppedFamily init s φ G θ r b) t ω = -b := by
  classical
  have hp := (prefixAlive_frestrict_iff init s φ G θ t ω).mpr halive
  simp only [recordedIncrement, recordedNext, stoppedFamily, if_pos hp]
  change edgeIncrement φ G r b (s + t) (trace init ω (s + t))
    (ω (s + t + 1)) = -b
  have hs : applyDraw (trace init ω (s + t)) (ω (s + t + 1)) =
      trace init ω (s + t + 1) := (TimeTheorem.trace_succ init ω (s + t)).symm
  simp only [edgeIncrement, hs, if_neg hexit]

theorem compensatedLog_frozen (init : Cfg L K) (s : ℕ)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b : ℝ)
    (ω : Ω L K) (u v : ℕ) (huv : u ≤ v)
    (hdead : ¬ Alive init s φ G θ u ω) :
    logProcess init s φ G θ r b v ω = logProcess init s φ G θ r b u ω := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
      have hv : ¬ Alive init s φ G θ v ω :=
        fun h => hdead (alive_of_le init s φ G θ ω huv h)
      change recordedSum s _ (v + 1) ω = _
      rw [recordedSum_succ]
      simp only [Pi.add_apply,
        increment_zero_after_failure init s φ G θ r b v ω hv, add_zero]
      exact ih

theorem increment_eq_log_on_survival (init : Cfg L K) (s : ℕ)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b D : ℝ)
    (hc : LogControl φ G θ r b D)
    (t : ℕ) (ω : Ω L K) (halive : Alive init s φ G θ t ω)
    (hnext : G (s + t + 1) (trace init ω (s + t + 1))) :
    recordedIncrement s (stoppedFamily init s φ G θ r b) t ω =
      Real.log (φ (trace init ω (s + t + 1)) : ℝ) -
        Real.log (φ (trace init ω (s + t)) : ℝ) + r := by
  classical
  have hp := (prefixAlive_frestrict_iff init s φ G θ t ω).mpr halive
  have hcur := halive t le_rfl
  have hb := (live_log_step_bounds φ G θ r b D hc (s + t)
    (trace init ω (s + t)) hcur.1 hcur.2 (ω (s + t + 1))).2
  have hs : applyDraw (trace init ω (s + t)) (ω (s + t + 1)) =
      trace init ω (s + t + 1) := (TimeTheorem.trace_succ init ω (s + t)).symm
  rw [hs] at hb
  simp only [recordedIncrement, recordedNext, stoppedFamily, if_pos hp]
  change edgeIncrement φ G r b (s + t) (trace init ω (s + t))
    (ω (s + t + 1)) = _
  rw [edgeIncrement, hs, if_pos hnext, clip_eq hb]

theorem compensatedLog_eq_on_survival (init : Cfg L K) (s : ℕ)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b D : ℝ)
    (hc : LogControl φ G θ r b D)
    (ω : Ω L K) (N : ℕ) (halive : Alive init s φ G θ N ω) :
    logProcess init s φ G θ r b N ω =
      Real.log (φ (trace init ω (s + N)) : ℝ) -
        Real.log (φ (trace init ω s) : ℝ) + r * N := by
  revert halive
  induction N with
  | zero =>
      intro _
      simp [logProcess, recordedSum]
  | succ N ih =>
      intro halive
      have hprev := alive_of_le init s φ G θ ω (Nat.le_succ N) halive
      have hnext : G (s + N + 1) (trace init ω (s + N + 1)) := by
        simpa only [Nat.add_assoc] using (halive (N + 1) le_rfl).1
      have hinc := increment_eq_log_on_survival init s φ G θ r b D hc N ω hprev hnext
      change recordedSum s _ (N + 1) ω = _
      rw [recordedSum_succ]
      simp only [Pi.add_apply]
      rw [show recordedSum s (stoppedFamily init s φ G θ r b) N ω =
        Real.log (φ (trace init ω (s + N)) : ℝ) -
          Real.log (φ (trace init ω s) : ℝ) + r * N from ih hprev, hinc]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc]
      ring

theorem compensatedLog_maximal_tail (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b D : ℝ)
    (hc : LogControl φ G θ r b D) (u : ℝ) (hu : 0 < u) (N : ℕ) :
    Ripple.Probability.prob (recordedFuture init s p)
      {ω | ∃ t, t ≤ N ∧
        u ≤ logProcess init s φ G θ r b t ω - logProcess init s φ G θ r b 0 ω} ≤
      Real.exp (-(u ^ 2) / (2 * ((N : ℝ) * b ^ 2 + 2 * b * u / 3))) :=
  recordedSum_maximal_tail init s p _ b hc.radius_nonneg
    (stoppedFamily_abs_le init s φ G θ r b hc.radius_nonneg)
    (stoppedFamily_mean_le_zero init s φ G θ r b D hc) u hu N

theorem logarithmic_survival_tail (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (φ : Cfg L K → ℕ) (G : ℕ → Cfg L K → Prop) (θ r b D : ℝ)
    (hc : LogControl φ G θ r b D)
    (R : ℝ) (hR : 0 < R) (u : ℝ) (hu : 0 < u) (N : ℕ)
    (hnum : u ≤ r * N - Real.log (R / θ)) :
    Ripple.Probability.prob (recordedFuture init s p)
      {ω | Alive init s φ G θ N ω ∧ (φ (trace init ω s) : ℝ) ≤ R} ≤
      Real.exp (-(u ^ 2) / (2 * ((N : ℝ) * b ^ 2 + 2 * b * u / 3))) := by
  have hsubset :
      {ω | Alive init s φ G θ N ω ∧ (φ (trace init ω s) : ℝ) ≤ R} ⊆
        {ω | ∃ t, t ≤ N ∧
          u ≤ logProcess init s φ G θ r b t ω -
            logProcess init s φ G θ r b 0 ω} := by
    rintro ω ⟨halive, hstart⟩
    have hstartpos : 0 < (φ (trace init ω s) : ℝ) := by
      have h := (halive 0 (Nat.zero_le N)).2
      simp only [Nat.add_zero] at h
      exact hc.threshold_pos.trans h
    have hlo := Real.log_le_log hc.threshold_pos (halive N le_rfl).2.le
    have hhi := Real.log_le_log hstartpos hstart
    have ht := compensatedLog_eq_on_survival init s φ G θ r b D hc ω N halive
    have hz : logProcess init s φ G θ r b 0 ω = 0 := by
      simp [logProcess, recordedSum]
    refine ⟨N, le_rfl, ?_⟩
    rw [ht, hz, sub_zero]
    have hlog := Real.log_div hR.ne' hc.threshold_pos.ne'
    rw [hlog] at hnum
    linarith
  have hprob :
      Ripple.Probability.prob (recordedFuture init s p)
          {ω | Alive init s φ G θ N ω ∧ (φ (trace init ω s) : ℝ) ≤ R} ≤
        Ripple.Probability.prob (recordedFuture init s p)
          {ω | ∃ t, t ≤ N ∧
            u ≤ logProcess init s φ G θ r b t ω -
              logProcess init s φ G θ r b 0 ω} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
  exact hprob.trans (compensatedLog_maximal_tail init s p φ G θ r b D hc u hu N)

end Ripple.PopulationProtocol.ExactMajority.AveragingCompensatedLog

end

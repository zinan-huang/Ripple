-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingWorkCounter.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingPotentialDrift
import Ripple.PopulationProtocol.ExactMajority.Probability.TraceDrain
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Multiplying actual potential contractions over observed work slots

The work bit at a raw interaction is a function of the recorded pair-log
past. It may describe several random work blocks separated by gaps.
The fixed integer potential is killed on the first failed current gate.
A factor (1-rho)^(-workCount) compensates only interactions marked as work.

The moment inequality below is proved from the implemented transition and
the physical-scheduler kernel. No martingale or conditional-drift property
is assumed. Selecting actual clock work blocks and proving that q-6 complete
blocks occur remains a separate deterministic clock-history obligation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingWorkCounter

open TimeTheorem PairLog TraceDrain AveragingPotentialService
open AveragingPotentialDrift AveragingIntegerPotential

variable {L : ℕ}

def WorkGate (h : ℕ) (ρ : ℝ≥0∞) (c : Cfg L 256) (b : Bool) : Prop :=
  2 ≤ c.card ∧ PotentialDomain c ∧ (b = true → ρ ≤ readyRate h c)

def workCount (work : ℕ → Ω L 256 → Bool) (t : ℕ) (ω : Ω L 256) : ℕ :=
  ∑ u ∈ Finset.range t, if work u ω then 1 else 0

theorem workCount_zero (work : ℕ → Ω L 256 → Bool) (ω : Ω L 256) :
    workCount work 0 ω = 0 := by simp [workCount]

theorem workCount_succ (work : ℕ → Ω L 256 → Bool) (t : ℕ) (ω : Ω L 256) :
    workCount work (t + 1) ω = workCount work t ω + if work t ω then 1 else 0 := by
  simp only [workCount, Finset.sum_range_succ]

theorem measurable_workCount_at (s : ℕ) (work : ℕ → Ω L 256 → Bool)
    (hwork : ∀ u, Measurable[pairLogFiltration L 256 (s + u)] (work u))
    (t v : ℕ) (htv : t ≤ v + 1) :
    Measurable[pairLogFiltration L 256 (s + v)] (workCount work t) := by
  unfold workCount
  apply Finset.measurable_sum
  intro u hu
  have huv : u ≤ v := by
    have hu' := Finset.mem_range.mp hu
    omega
  exact (measurable_of_countable (fun b : Bool => if b then (1 : ℕ) else 0)).comp
    ((hwork u).mono ((pairLogFiltration L 256).mono (Nat.add_le_add_left huv s)) le_rfl)

def WorkLive (init : Cfg L 256) (s h : ℕ) (ρ : ℝ≥0∞)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool) (t : ℕ) (ω : Ω L 256) : Prop :=
  frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A ∧
    augmentedPhiNat h (trace init ω s) ≤ Ψ ∧
    ∀ u, u ≤ t → WorkGate h ρ (trace init ω (s + u)) (work u ω)

theorem WorkLive.previous (init : Cfg L 256) (s h : ℕ) (ρ : ℝ≥0∞)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool) (t : ℕ) (ω : Ω L 256)
    (hlive : WorkLive init s h ρ A Ψ work (t + 1) ω) :
    WorkLive init s h ρ A Ψ work t ω :=
  ⟨hlive.1, hlive.2.1, fun u hu => hlive.2.2 u (by omega)⟩

theorem measurableSet_workLive (init : Cfg L 256) (s h : ℕ) (ρ : ℝ≥0∞)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool)
    (hwork : ∀ u, Measurable[pairLogFiltration L 256 (s + u)] (work u))
    (t : ℕ) :
    MeasurableSet[pairLogFiltration L 256 (s + t)]
      {ω | WorkLive init s h ρ A Ψ work t ω} := by
  have hp : MeasurableSet[pairLogFiltration L 256 (s + t)]
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
    exact (pairLogFiltration L 256).mono (by omega : s ≤ s + t) _
      ((Set.to_countable A).measurableSet.preimage
        (measurable_pairLog_prefix L 256 s))
  have hstart : MeasurableSet[pairLogFiltration L 256 (s + t)]
      {ω | augmentedPhiNat h (trace init ω s) ≤ Ψ} :=
    (Set.to_countable {c : Cfg L 256 | augmentedPhiNat h c ≤ Ψ}).measurableSet.preimage
      (measurable_trace_at_of_le init (by omega : s ≤ s + t))
  have hgates : MeasurableSet[pairLogFiltration L 256 (s + t)]
      {ω | ∀ u, u ≤ t → WorkGate h ρ (trace init ω (s + u)) (work u ω)} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu => ?_
    exact (Set.to_countable
      {p : Cfg L 256 × Bool | WorkGate h ρ p.1 p.2}).measurableSet.preimage
      ((measurable_trace_at_of_le init (Nat.add_le_add_left hu s)).prodMk
        ((hwork u).mono ((pairLogFiltration L 256).mono
          (Nat.add_le_add_left hu s)) le_rfl))
  exact hp.inter (hstart.inter hgates)

open Classical in
def compensatedWork (init : Cfg L 256) (s h : ℕ) (ρ : ℝ≥0∞)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool) (t : ℕ) (ω : Ω L 256) : ℝ≥0∞ :=
  ((1 - ρ)⁻¹) ^ workCount work t ω *
    if WorkLive init s h ρ A Ψ work t ω
      then (augmentedPhiNat h (trace init ω (s + t)) : ℝ≥0∞) else 0

theorem measurable_compensatedWork (init : Cfg L 256) (s h : ℕ) (ρ : ℝ≥0∞)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool)
    (hwork : ∀ u, Measurable[pairLogFiltration L 256 (s + u)] (work u))
    (t : ℕ) :
    Measurable[pairLogFiltration L 256 (s + t)]
      (compensatedWork init s h ρ A Ψ work t) := by
  classical
  have hcount := measurable_workCount_at s work hwork t t (Nat.le_succ t)
  have hscale := (measurable_of_countable
    (fun j : ℕ => ((1 - ρ)⁻¹) ^ j)).comp hcount
  have hphi := (measurable_of_countable
    (fun c : Cfg L 256 => (augmentedPhiNat h c : ℝ≥0∞))).comp
      (measurable_trace_at init (s + t))
  exact hscale.mul (Measurable.ite (measurableSet_workLive init s h ρ A Ψ work hwork t)
    hphi measurable_const)

open Classical in
def workStepCoefficient (init : Cfg L 256) (s h : ℕ) (ρ : ℝ≥0∞)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool) (t : ℕ) (ω : Ω L 256) : ℝ≥0∞ :=
  ((1 - ρ)⁻¹) ^ workCount work (t + 1) ω *
    if WorkLive init s h ρ A Ψ work t ω then 1 else 0

theorem measurable_workStepCoefficient (init : Cfg L 256) (s h : ℕ) (ρ : ℝ≥0∞)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool)
    (hwork : ∀ u, Measurable[pairLogFiltration L 256 (s + u)] (work u))
    (t : ℕ) :
    Measurable[pairLogFiltration L 256 (s + t)]
      (workStepCoefficient init s h ρ A Ψ work t) := by
  classical
  have hcount := measurable_workCount_at s work hwork (t + 1) t le_rfl
  have hscale := (measurable_of_countable
    (fun j : ℕ => ((1 - ρ)⁻¹) ^ j)).comp hcount
  exact hscale.mul (Measurable.ite (measurableSet_workLive init s h ρ A Ψ work hwork t)
    measurable_const measurable_const)

theorem compensatedWork_succ_le (init : Cfg L 256) (s h : ℕ) (ρ : ℝ≥0∞)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool) (t : ℕ) (ω : Ω L 256) :
    compensatedWork init s h ρ A Ψ work (t + 1) ω ≤
      workStepCoefficient init s h ρ A Ψ work t ω *
        (augmentedPhiNat h
          (applyDraw (trace init ω (s + t)) (ω (s + t + 1))) : ℝ≥0∞) := by
  classical
  by_cases hlive : WorkLive init s h ρ A Ψ work (t + 1) ω
  · have hprev := WorkLive.previous init s h ρ A Ψ work t ω hlive
    simp only [compensatedWork, workStepCoefficient, if_pos hlive, if_pos hprev,
      Nat.add_assoc, TimeTheorem.trace_succ, mul_one, le_refl]
    exact le_of_eq rfl
  · simp only [compensatedWork, if_neg hlive, mul_zero, zero_le]

/-- Actual kernel contraction on marked slots and actual monotonicity on
unmarked gaps. Killing a failed next gate only decreases the left side. -/
theorem compensatedWork_kernel_step (init : Cfg L 256) (s h : ℕ)
    (hh : 1 ≤ h) (ρ : ℝ≥0∞) (hρ : ρ < 1)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool) (t : ℕ) (ω : Ω L 256) :
    workStepCoefficient init s h ρ A Ψ work t ω *
        (∫⁻ c', (augmentedPhiNat h c' : ℝ≥0∞)
          ∂(NonuniformMajority L 256).transitionKernel (trace init ω (s + t))) ≤
      compensatedWork init s h ρ A Ψ work t ω := by
  classical
  have hzero : 1 - ρ ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hρ)
  have htop : 1 - ρ ≠ (⊤ : ℝ≥0∞) :=
    (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top).ne
  by_cases hlive : WorkLive init s h ρ A Ψ work t ω
  · have hgate := hlive.2.2 t le_rfl
    have hdrift := augmentedPhiNat_kernel_drift h hh
      (trace init ω (s + t)) hgate.1 hgate.2.1
    simp only [workStepCoefficient, compensatedWork, if_pos hlive, mul_one]
    by_cases hmark : work t ω = true
    · have hr : ρ ≤ readyRate h (trace init ω (s + t)) := hgate.2.2 hmark
      have hd :
          (∫⁻ c', (augmentedPhiNat h c' : ℝ≥0∞)
            ∂(NonuniformMajority L 256).transitionKernel (trace init ω (s + t))) ≤
          (1 - ρ) * augmentedPhiNat h (trace init ω (s + t)) := by
        exact hdrift.trans (mul_le_mul_right' (tsub_le_tsub_left hr 1) _)
      rw [workCount_succ, if_pos hmark, pow_succ]
      calc
        _ ≤ (((1 - ρ)⁻¹) ^ workCount work t ω * (1 - ρ)⁻¹) *
            ((1 - ρ) * augmentedPhiNat h (trace init ω (s + t))) :=
          mul_le_mul_left' hd _
        _ = _ := by
          rw [mul_assoc, ENNReal.inv_mul_cancel_left hzero htop]
    · have hd :
          (∫⁻ c', (augmentedPhiNat h c' : ℝ≥0∞)
            ∂(NonuniformMajority L 256).transitionKernel (trace init ω (s + t))) ≤
          (augmentedPhiNat h (trace init ω (s + t)) : ℝ≥0∞) :=
        hdrift.trans ((mul_le_mul_right' tsub_le_self _).trans_eq (one_mul _))
      rw [workCount_succ, if_neg hmark, Nat.add_zero]
      exact mul_le_mul_left' hd _
  · simp only [workStepCoefficient, compensatedWork, if_neg hlive, mul_zero, zero_mul,
      le_refl]

/-- This is an integral inequality proved from the recorded next-draw law,
rather than an assumed supermartingale property. -/
theorem compensatedWork_moment_step (init : Cfg L 256) (s h : ℕ)
    (hh : 1 ≤ h) (ρ : ℝ≥0∞) (hρ : ρ < 1)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool)
    (hwork : ∀ u, Measurable[pairLogFiltration L 256 (s + u)] (work u))
    (t : ℕ) :
    (∫⁻ ω, compensatedWork init s h ρ A Ψ work (t + 1) ω ∂law init) ≤
      ∫⁻ ω, compensatedWork init s h ρ A Ψ work t ω ∂law init := by
  have hcoef := measurable_workStepCoefficient init s h ρ A Ψ work hwork t
  rw [pairLogFiltration_eq_comap] at hcoef
  obtain ⟨f, -, hf⟩ := hcoef.exists_eq_measurable_comp
  let F : ((i : Finset.Iic (s + t)) → Draw L 256) → Draw L 256 → ℝ≥0∞ :=
    fun p d => f p * (augmentedPhiNat h (applyDraw (prefixCfg init (s + t) p) d) : ℝ≥0∞)
  have hpoint (ω : Ω L 256) :
      compensatedWork init s h ρ A Ψ work (t + 1) ω ≤
        F (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω) (ω (s + t + 1)) := by
    have he := congrFun hf ω
    dsimp only [Function.comp_apply] at he
    simpa only [F, ← he] using compensatedWork_succ_le init s h ρ A Ψ work t ω
  have hinner (ω : Ω L 256) :
      (∫⁻ d, F (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω) d
        ∂pairKernel init (s + t) (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω)) ≤
      compensatedWork init s h ρ A Ψ work t ω := by
    have he := congrFun hf ω
    dsimp only [Function.comp_apply] at he
    dsimp only [F]
    rw [lintegral_const_mul _ (measurable_of_countable _),
      lintegral_pairKernel_applyDraw init (s + t) _ (fun c => (augmentedPhiNat h c : ℝ≥0∞)),
      ← he]
    exact compensatedWork_kernel_step init s h hh ρ hρ A Ψ work t ω
  calc
    (∫⁻ ω, compensatedWork init s h ρ A Ψ work (t + 1) ω ∂law init) ≤
        ∫⁻ ω, F (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω)
          (ω (s + t + 1)) ∂law init := lintegral_mono hpoint
    _ = ∫⁻ ω, (∫⁻ d,
        F (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω) d
          ∂pairKernel init (s + t)
            (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω)) ∂law init :=
      lintegral_prefix_next init (s + t) F
    _ ≤ _ := lintegral_mono hinner

theorem compensatedWork_moment (init : Cfg L 256) (s h : ℕ)
    (hh : 1 ≤ h) (ρ : ℝ≥0∞) (hρ : ρ < 1)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool)
    (hwork : ∀ u, Measurable[pairLogFiltration L 256 (s + u)] (work u))
    (T : ℕ) :
    (∫⁻ ω, compensatedWork init s h ρ A Ψ work T ω ∂law init) ≤
      (Ψ : ℝ≥0∞) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
  induction T with
  | zero =>
      classical
      let P : Set (Ω L 256) :=
        {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A}
      have hP : MeasurableSet P :=
        (Set.to_countable A).measurableSet.preimage
          (measurable_frestrictLe (X := fun _ : ℕ => Draw L 256) s)
      have hpoint (ω : Ω L 256) :
          compensatedWork init s h ρ A Ψ work 0 ω ≤ P.indicator (fun _ => (Ψ : ℝ≥0∞)) ω := by
        by_cases hlive : WorkLive init s h ρ A Ψ work 0 ω
        · simp only [compensatedWork, workCount_zero, pow_zero, one_mul,
            if_pos hlive, Nat.add_zero]
          rw [Set.indicator_of_mem (show ω ∈ P from hlive.1)]
          exact_mod_cast hlive.2.1
        · simp only [compensatedWork, if_neg hlive, mul_zero, zero_le]
      exact (lintegral_mono hpoint).trans_eq (lintegral_indicator_const hP _)
  | succ T ih =>
      exact (compensatedWork_moment_step init s h hh ρ hρ A Ψ work hwork T).trans ih

/-- The product of K contractions depends on the number of exposed work
interactions, not on their deterministic positions in raw time. In particular,
gaps between random work blocks do not restart the potential or the law. -/
theorem work_count_extinction_tail (init : Cfg L 256) (s h : ℕ)
    (hh : 1 ≤ h) (ρ : ℝ≥0∞) (hρ : ρ < 1)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool)
    (hwork : ∀ u, Measurable[pairLogFiltration L 256 (s + u)] (work u))
    (T K : ℕ) :
    law init {ω | WorkLive init s h ρ A Ψ work T ω ∧
        K ≤ workCount work T ω ∧ 1 ≤ augmentedPhiNat h (trace init ω (s + T))} ≤
      (1 - ρ) ^ K * Ψ *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
  classical
  have hzero : 1 - ρ ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hρ)
  have htop : 1 - ρ ≠ (⊤ : ℝ≥0∞) :=
    (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top).ne
  have hinv : (1 : ℝ≥0∞) ≤ (1 - ρ)⁻¹ := by
    simpa only [inv_one] using (ENNReal.inv_le_inv).2
      (show 1 - ρ ≤ (1 : ℝ≥0∞) from tsub_le_self)
  let E : Set (Ω L 256) :=
    {ω | WorkLive init s h ρ A Ψ work T ω ∧
      K ≤ workCount work T ω ∧ 1 ≤ augmentedPhiNat h (trace init ω (s + T))}
  have hsub : E ⊆
      {ω | ((1 - ρ)⁻¹) ^ K ≤ compensatedWork init s h ρ A Ψ work T ω} := by
    rintro ω ⟨hlive, hcount, hphi⟩
    simp only [Set.mem_setOf_eq]
    rw [compensatedWork, if_pos hlive]
    calc
      ((1 - ρ)⁻¹) ^ K ≤ ((1 - ρ)⁻¹) ^ workCount work T ω :=
        pow_le_pow_right₀ hinv hcount
      _ = ((1 - ρ)⁻¹) ^ workCount work T ω * 1 := by rw [mul_one]
      _ ≤ _ := mul_le_mul_left' (by exact_mod_cast hphi) _
  have hm : Measurable (compensatedWork init s h ρ A Ψ work T) :=
    (measurable_compensatedWork init s h ρ A Ψ work hwork T).mono
      ((pairLogFiltration L 256).le (s + T)) le_rfl
  have hmarkov :
      ((1 - ρ)⁻¹) ^ K * law init E ≤
        (Ψ : ℝ≥0∞) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
    calc
      _ ≤ ((1 - ρ)⁻¹) ^ K *
          law init {ω | ((1 - ρ)⁻¹) ^ K ≤ compensatedWork init s h ρ A Ψ work T ω} :=
        mul_le_mul_left' (measure_mono hsub) _
      _ ≤ ∫⁻ ω, compensatedWork init s h ρ A Ψ work T ω ∂law init :=
        mul_meas_ge_le_lintegral₀ hm.aemeasurable _
      _ ≤ _ := compensatedWork_moment init s h hh ρ hρ A Ψ work hwork T
  change law init E ≤ _
  calc
    law init E =
        (1 - ρ) ^ K * (((1 - ρ)⁻¹) ^ K * law init E) := by
          rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hzero htop, one_pow, one_mul]
    _ ≤ (1 - ρ) ^ K *
        ((Ψ : ℝ≥0∞) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A}) :=
      mul_le_mul_left' hmarkov _
    _ = _ := by ring

end Ripple.PopulationProtocol.ExactMajority.AveragingWorkCounter

end

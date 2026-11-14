-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingFrozenWork.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingObservedBlocks
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Freezing actual compensated work at an observed random endpoint

The finite stopped process retains each endpoint fibre once and evolves only
before the endpoint. Its moment bound is proved by prefix-restricted actual
kernel steps. Passing to the nonnegative sum of frozen endpoint fibres yields
the same bound at any finite observed endpoint, without a union bound over
possible endpoint values.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingFrozenWork

open TimeTheorem PairLog PhaseOneDrain TraceDrain AveragingIntegerPotential
open AveragingWorkCounter AveragingObservedBlocks

variable {L : ℕ}

theorem pastTime_measurable_le (τ : Ω L 256 → WithTop ℕ)
    (hτ : PairLogPastTime τ) (t : ℕ) :
    MeasurableSet[pairLogFiltration L 256 t] {ω | τ ω ≤ (t : WithTop ℕ)} := by
  have heq : {ω | τ ω ≤ (t : WithTop ℕ)} =
      ⋃ u : Fin (t + 1), {ω | τ ω = (u.val : WithTop ℕ)} := by
    ext ω
    cases hval : τ ω with
    | top => simp [hval]
    | coe r =>
        simp only [hval, Nat.cast_withTop, WithTop.coe_le_coe, Set.mem_setOf_eq,
          Set.mem_iUnion, WithTop.coe_inj]
        constructor
        · intro hr
          exact ⟨⟨r, by omega⟩, rfl⟩
        · rintro ⟨u, hu⟩
          have := u.isLt
          omega
  rw [heq]
  apply MeasurableSet.iUnion
  intro u
  exact (pairLogFiltration L 256).mono (by have := u.isLt; omega) _ (hτ u.val)

theorem withTop_next_le_iff (t : ℕ) (x : WithTop ℕ) :
    ((t + 1 : ℕ) : WithTop ℕ) ≤ x ↔ (t : WithTop ℕ) < x := by
  cases x with
  | top => simp
  | coe r => simp only [Nat.cast_withTop, WithTop.coe_le_coe, WithTop.coe_lt_coe]; omega

theorem pastTime_measurable_next (τ : Ω L 256 → WithTop ℕ)
    (hτ : PairLogPastTime τ) (t : ℕ) :
    MeasurableSet[pairLogFiltration L 256 t]
      {ω | ((t + 1 : ℕ) : WithTop ℕ) ≤ τ ω} := by
  have heq : {ω | ((t + 1 : ℕ) : WithTop ℕ) ≤ τ ω} =
      {ω | τ ω ≤ (t : WithTop ℕ)}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, withTop_next_le_iff, not_le]
  rw [heq]
  exact (pastTime_measurable_le τ hτ t).compl

open Classical in
def endpointPiece (X : ℕ → Ω L 256 → ℝ≥0∞)
    (τ : Ω L 256 → WithTop ℕ) (s u : ℕ) : Ω L 256 → ℝ≥0∞ :=
  {ω | τ ω = ((s + u : ℕ) : WithTop ℕ)}.indicator (X u)

def frozenPartial (X : ℕ → Ω L 256 → ℝ≥0∞)
    (τ : Ω L 256 → WithTop ℕ) (s t : ℕ) (ω : Ω L 256) : ℝ≥0∞ :=
  ∑ u ∈ Finset.range t, endpointPiece X τ s u ω

open Classical in
def stoppedEndpoint (X : ℕ → Ω L 256 → ℝ≥0∞)
    (τ : Ω L 256 → WithTop ℕ) (s t : ℕ) (ω : Ω L 256) : ℝ≥0∞ :=
  frozenPartial X τ s t ω +
    {ω | ((s + t : ℕ) : WithTop ℕ) ≤ τ ω}.indicator (X t) ω

def frozenEndpoint (X : ℕ → Ω L 256 → ℝ≥0∞)
    (τ : Ω L 256 → WithTop ℕ) (s : ℕ) (ω : Ω L 256) : ℝ≥0∞ :=
  ∑' u : ℕ, endpointPiece X τ s u ω

theorem measurable_endpointPiece (X : ℕ → Ω L 256 → ℝ≥0∞)
    (hX : ∀ u, Measurable (X u))
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ) (s u : ℕ) :
    Measurable (endpointPiece X τ s u) :=
  (hX u).indicator ((pairLogFiltration L 256).le (s + u) _ (hτ (s + u)))

theorem measurable_frozenPartial (X : ℕ → Ω L 256 → ℝ≥0∞)
    (hX : ∀ u, Measurable (X u))
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ) (s t : ℕ) :
    Measurable (frozenPartial X τ s t) := by
  apply Finset.measurable_sum
  intro u _
  exact measurable_endpointPiece X hX τ hτ s u

theorem measurable_frozenEndpoint (X : ℕ → Ω L 256 → ℝ≥0∞)
    (hX : ∀ u, Measurable (X u))
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ) (s : ℕ) :
    Measurable (frozenEndpoint X τ s) :=
  Measurable.ennreal_tsum (fun u => measurable_endpointPiece X hX τ hτ s u)

theorem frozenEndpoint_eq_on_fibre (X : ℕ → Ω L 256 → ℝ≥0∞)
    (τ : Ω L 256 → WithTop ℕ) (s u : ℕ) (ω : Ω L 256)
    (hu : τ ω = ((s + u : ℕ) : WithTop ℕ)) :
    frozenEndpoint X τ s ω = X u ω := by
  classical
  have hzero (v : ℕ) (hvu : v ≠ u) : endpointPiece X τ s v ω = 0 := by
    have hv : τ ω ≠ ((s + v : ℕ) : WithTop ℕ) := by
      intro he
      have hnat : s + u = s + v := WithTop.coe_injective (hu.symm.trans he)
      exact hvu (by omega)
    simp only [endpointPiece,
      Set.indicator_of_notMem (show ω ∉ {ω | τ ω = ((s + v : ℕ) : WithTop ℕ)} from hv)]
  calc
    frozenEndpoint X τ s ω = endpointPiece X τ s u ω := tsum_eq_single u hzero
    _ = X u ω := by
      simp only [endpointPiece,
        Set.indicator_of_mem (show ω ∈ {ω | τ ω = ((s + u : ℕ) : WithTop ℕ)} from hu)]

open Classical in
theorem endpoint_ge_partition (r : ℕ) (x : WithTop ℕ) (v : ℝ≥0∞) :
    (if (r : WithTop ℕ) ≤ x then v else 0) =
      (if x = (r : WithTop ℕ) then v else 0) +
        (if ((r + 1 : ℕ) : WithTop ℕ) ≤ x then v else 0) := by
  cases x with
  | top => simp
  | coe q =>
      simp only [Nat.cast_withTop, WithTop.coe_le_coe, WithTop.coe_inj]
      by_cases he : q = r
      · subst q
        simp
      · by_cases hge : r ≤ q
        · have hs : r + 1 ≤ q := by omega
          simp [he, hge, hs]
        · have hs : ¬ r + 1 ≤ q := by omega
          simp [he, hge, hs]

/-- At the sampled endpoint the old value is retained; after that point only
its single endpoint fibre remains in the frozen partial sum. -/
theorem stoppedEndpoint_split (X : ℕ → Ω L 256 → ℝ≥0∞)
    (τ : Ω L 256 → WithTop ℕ) (s t : ℕ) (ω : Ω L 256) :
    stoppedEndpoint X τ s t ω =
      frozenPartial X τ s (t + 1) ω +
        {ω | ((s + t + 1 : ℕ) : WithTop ℕ) ≤ τ ω}.indicator (X t) ω := by
  classical
  simp only [stoppedEndpoint, frozenPartial, Finset.sum_range_succ,
    endpointPiece, Set.indicator_apply, Set.mem_setOf_eq]
  rw [endpoint_ge_partition (s + t) (τ ω) (X t ω)]
  ring

theorem stoppedEndpoint_moment (init : Cfg L 256) (s : ℕ)
    (X : ℕ → Ω L 256 → ℝ≥0∞) (hX : ∀ u, Measurable (X u))
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ)
    (C : ℝ≥0∞) (hstart : (∫⁻ ω, X 0 ω ∂law init) ≤ C)
    (hstep : ∀ t,
      (∫⁻ ω, {ω | ((s + t + 1 : ℕ) : WithTop ℕ) ≤ τ ω}.indicator
        (X (t + 1)) ω ∂law init) ≤
      ∫⁻ ω, {ω | ((s + t + 1 : ℕ) : WithTop ℕ) ≤ τ ω}.indicator
        (X t) ω ∂law init)
    (T : ℕ) :
    (∫⁻ ω, stoppedEndpoint X τ s T ω ∂law init) ≤ C := by
  induction T with
  | zero =>
      refine (lintegral_mono fun ω => ?_).trans hstart
      classical
      simp only [stoppedEndpoint, frozenPartial, Finset.sum_range_zero, zero_add]
      exact Set.indicator_le_self _ _ ω
  | succ t ih =>
      have hp := measurable_frozenPartial X hX τ hτ s (t + 1)
      calc
        (∫⁻ ω, stoppedEndpoint X τ s (t + 1) ω ∂law init) =
            (∫⁻ ω, frozenPartial X τ s (t + 1) ω ∂law init) +
              ∫⁻ ω, {ω | ((s + t + 1 : ℕ) : WithTop ℕ) ≤ τ ω}.indicator
                (X (t + 1)) ω ∂law init := by
                  simpa only [stoppedEndpoint, Nat.add_assoc] using
                    (lintegral_add_left hp
                      (fun ω => {ω | ((s + t + 1 : ℕ) : WithTop ℕ) ≤ τ ω}.indicator
                        (X (t + 1)) ω))
        _ ≤ (∫⁻ ω, frozenPartial X τ s (t + 1) ω ∂law init) +
              ∫⁻ ω, {ω | ((s + t + 1 : ℕ) : WithTop ℕ) ≤ τ ω}.indicator
                (X t) ω ∂law init := add_le_add le_rfl (hstep t)
        _ = ∫⁻ ω, stoppedEndpoint X τ s t ω ∂law init := by
          rw [← lintegral_add_left hp]
          apply lintegral_congr
          intro ω
          exact (stoppedEndpoint_split X τ s t ω).symm
        _ ≤ C := ih

/-- No endpoint-count factor occurs: nonnegative monotone convergence is
applied to the retained endpoint values, not to endpoint failure bounds. -/
theorem frozenEndpoint_moment (init : Cfg L 256) (s : ℕ)
    (X : ℕ → Ω L 256 → ℝ≥0∞) (hX : ∀ u, Measurable (X u))
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ)
    (C : ℝ≥0∞) (hstart : (∫⁻ ω, X 0 ω ∂law init) ≤ C)
    (hstep : ∀ t,
      (∫⁻ ω, {ω | ((s + t + 1 : ℕ) : WithTop ℕ) ≤ τ ω}.indicator
        (X (t + 1)) ω ∂law init) ≤
      ∫⁻ ω, {ω | ((s + t + 1 : ℕ) : WithTop ℕ) ≤ τ ω}.indicator
        (X t) ω ∂law init) :
    (∫⁻ ω, frozenEndpoint X τ s ω ∂law init) ≤ C := by
  simp only [frozenEndpoint]
  rw [lintegral_tsum
    (fun u => (measurable_endpointPiece X hX τ hτ s u).aemeasurable),
    ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro T
  rw [← lintegral_finsetSum (Finset.range T)
    (fun u _ => measurable_endpointPiece X hX τ hτ s u)]
  calc
    (∫⁻ ω, ∑ u ∈ Finset.range T, endpointPiece X τ s u ω ∂law init) ≤
        ∫⁻ ω, stoppedEndpoint X τ s T ω ∂law init := by
          apply lintegral_mono
          intro ω
          change frozenPartial X τ s T ω ≤ frozenPartial X τ s T ω + _
          exact le_add_of_nonneg_right zero_le
    _ ≤ C := stoppedEndpoint_moment init s X hX τ hτ C hstart hstep T

/-- The past-event restricted moment step is still derived from the full
actual transition, including the sampled step which fails the next gate. -/
theorem compensatedWork_restricted_step (init : Cfg L 256) (s h : ℕ)
    (hh : 1 ≤ h) (ρ : ℝ≥0∞) (hρ : ρ < 1)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool)
    (hwork : ∀ u, Measurable[pairLogFiltration L 256 (s + u)] (work u))
    (t : ℕ) (E : Set (Ω L 256))
    (hE : MeasurableSet[pairLogFiltration L 256 (s + t)] E) :
    (∫⁻ ω, E.indicator (compensatedWork init s h ρ A Ψ work (t + 1)) ω ∂law init) ≤
      ∫⁻ ω, E.indicator (compensatedWork init s h ρ A Ψ work t) ω ∂law init := by
  classical
  have hcoef := (measurable_workStepCoefficient init s h ρ A Ψ work hwork t).indicator hE
  rw [pairLogFiltration_eq_comap] at hcoef
  obtain ⟨f, -, hf⟩ := hcoef.exists_eq_measurable_comp
  let F : ((i : Finset.Iic (s + t)) → Draw L 256) → Draw L 256 → ℝ≥0∞ :=
    fun p d => f p * (augmentedPhiNat h (applyDraw (prefixCfg init (s + t) p) d) : ℝ≥0∞)
  have hpoint (ω : Ω L 256) :
      E.indicator (compensatedWork init s h ρ A Ψ work (t + 1)) ω ≤
        F (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω) (ω (s + t + 1)) := by
    have he := congrFun hf ω
    dsimp only [Function.comp_apply] at he
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω] at he ⊢
      simpa only [F, ← he] using compensatedWork_succ_le init s h ρ A Ψ work t ω
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  have hinner (ω : Ω L 256) :
      (∫⁻ d, F (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω) d
        ∂pairKernel init (s + t) (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω)) ≤
      E.indicator (compensatedWork init s h ρ A Ψ work t) ω := by
    have he := congrFun hf ω
    dsimp only [Function.comp_apply] at he
    dsimp only [F]
    rw [lintegral_const_mul _ (measurable_of_countable _),
      lintegral_pairKernel_applyDraw init (s + t) _ (fun c => (augmentedPhiNat h c : ℝ≥0∞)),
      ← he]
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      exact compensatedWork_kernel_step init s h hh ρ hρ A Ψ work t ω
    · simp only [Set.indicator_of_notMem hω, zero_mul, le_refl]
  calc
    _ ≤ ∫⁻ ω, F (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω)
          (ω (s + t + 1)) ∂law init := lintegral_mono hpoint
    _ = ∫⁻ ω, (∫⁻ d,
        F (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω) d
          ∂pairKernel init (s + t)
            (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + t) ω)) ∂law init :=
      lintegral_prefix_next init (s + t) F
    _ ≤ _ := lintegral_mono hinner

theorem compensatedWork_frozen_moment (init : Cfg L 256) (s h : ℕ)
    (hh : 1 ≤ h) (ρ : ℝ≥0∞) (hρ : ρ < 1)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool)
    (hwork : ∀ u, Measurable[pairLogFiltration L 256 (s + u)] (work u))
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ) :
    (∫⁻ ω, frozenEndpoint (compensatedWork init s h ρ A Ψ work) τ s ω ∂law init) ≤
      (Ψ : ℝ≥0∞) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
  apply frozenEndpoint_moment init s
    (compensatedWork init s h ρ A Ψ work)
    (fun u => (measurable_compensatedWork init s h ρ A Ψ work hwork u).mono
      ((pairLogFiltration L 256).le (s + u)) le_rfl)
    τ hτ _
    (compensatedWork_moment init s h hh ρ hρ A Ψ work hwork 0)
  intro t
  exact compensatedWork_restricted_step init s h hh ρ hρ A Ψ work hwork t _
    (pastTime_measurable_next τ hτ (s + t))

/-- A genuinely random finite endpoint, without counting its possible values. -/
theorem random_endpoint_work_tail (init : Cfg L 256) (s h : ℕ)
    (hh : 1 ≤ h) (ρ : ℝ≥0∞) (hρ : ρ < 1)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (work : ℕ → Ω L 256 → Bool)
    (hwork : ∀ u, Measurable[pairLogFiltration L 256 (s + u)] (work u))
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ) (K : ℕ) :
    law init {ω | ∃ u : ℕ, τ ω = ((s + u : ℕ) : WithTop ℕ) ∧
        WorkLive init s h ρ A Ψ work u ω ∧ K ≤ workCount work u ω ∧
        1 ≤ augmentedPhiNat h (trace init ω (s + u))} ≤
      (1 - ρ) ^ K * Ψ *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
  classical
  let X := compensatedWork init s h ρ A Ψ work
  let Z := frozenEndpoint X τ s
  have hX (u : ℕ) : Measurable (X u) :=
    (measurable_compensatedWork init s h ρ A Ψ work hwork u).mono
      ((pairLogFiltration L 256).le (s + u)) le_rfl
  have hZ : Measurable Z := measurable_frozenEndpoint X hX τ hτ s
  have hzero : 1 - ρ ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hρ)
  have htop : 1 - ρ ≠ (⊤ : ℝ≥0∞) :=
    (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top).ne
  have hinv : (1 : ℝ≥0∞) ≤ (1 - ρ)⁻¹ := by
    simpa only [inv_one] using (ENNReal.inv_le_inv).2
      (show 1 - ρ ≤ (1 : ℝ≥0∞) from tsub_le_self)
  let E : Set (Ω L 256) :=
    {ω | ∃ u : ℕ, τ ω = ((s + u : ℕ) : WithTop ℕ) ∧
      WorkLive init s h ρ A Ψ work u ω ∧ K ≤ workCount work u ω ∧
      1 ≤ augmentedPhiNat h (trace init ω (s + u))}
  have hsub : E ⊆ {ω | ((1 - ρ)⁻¹) ^ K ≤ Z ω} := by
    rintro ω ⟨u, hu, hlive, hcount, hphi⟩
    have hvalue : ((1 - ρ)⁻¹) ^ K ≤ X u ω := by
      change _ ≤ compensatedWork init s h ρ A Ψ work u ω
      rw [compensatedWork, if_pos hlive]
      calc
        ((1 - ρ)⁻¹) ^ K ≤ ((1 - ρ)⁻¹) ^ workCount work u ω :=
          pow_le_pow_right₀ hinv hcount
        _ = ((1 - ρ)⁻¹) ^ workCount work u ω * 1 := by rw [mul_one]
        _ ≤ _ := mul_le_mul_left' (by exact_mod_cast hphi) _
    have hterm : X u ω ≤ Z ω := by
      have ht := ENNReal.le_tsum (f := fun v => endpointPiece X τ s v ω) u
      simpa only [Z, frozenEndpoint, endpointPiece,
        Set.indicator_of_mem (show ω ∈ {ω | τ ω = ((s + u : ℕ) : WithTop ℕ)} from hu)] using ht
    exact hvalue.trans hterm
  have hmarkov :
      ((1 - ρ)⁻¹) ^ K * law init E ≤
        (Ψ : ℝ≥0∞) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
    calc
      _ ≤ ((1 - ρ)⁻¹) ^ K * law init {ω | ((1 - ρ)⁻¹) ^ K ≤ Z ω} :=
        mul_le_mul_left' (measure_mono hsub) _
      _ ≤ ∫⁻ ω, Z ω ∂law init := mul_meas_ge_le_lintegral₀ hZ.aemeasurable _
      _ ≤ _ := compensatedWork_frozen_moment init s h hh ρ hρ A Ψ work hwork τ hτ
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

end Ripple.PopulationProtocol.ExactMajority.AveragingFrozenWork

end

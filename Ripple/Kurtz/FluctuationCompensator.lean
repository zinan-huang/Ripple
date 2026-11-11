import Ripple.Kurtz.FluctuationLemmas
import Ripple.Kurtz.Adjoint
import Ripple.Kurtz.ExponentialTail
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Compensators for the finite-dimensional fluctuation theorem


L4: the explicit quadratic-compensator estimate, its exact-supremum version,
and the canonical-law probability consequence.
L5: the nonlinear listed-jump rewrite and the linear drift rewrite.
L6, implemented portion: the zero-off-Cauchy total jump functional,
measurability, a common almost-sure event, a cutoff uniform in the test
function and sub-horizon, and measurability of the compensated functional
and Taylor remainder.

NOT IMPLEMENTED HERE: L6's jump-count exponential moment and expectation
bounds, integrability of the total jump functional, adjoint integration by
parts, and the inclusive-cutoff identity for the compensated functional.
There are no declarations standing in for these missing results.
-/

namespace Ripple.Kurtz

open MeasureTheory Filter Topology Set Finset
open Ripple.CTMC
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Elementary measurable and supremum interfaces -/

private theorem fc_measurable_dot {Ω : Type*} [MeasurableSpace Ω]
    {u v : Ω → Fin d → ℝ} (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun ω => u ω ⬝ᵥ v ω) := by
  unfold dotProduct
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hu).mul
      ((measurable_pi_apply i).comp hv)

/-- The dimension factor is necessary for the coordinate-sum pairing on the
sup-norm space `Fin d → ℝ`. -/
theorem fluctuation_abs_dot_le (u v : Fin d → ℝ) :
    |u ⬝ᵥ v| ≤ (d : ℝ) * ‖u‖ * ‖v‖ := by
  unfold dotProduct
  calc
    |∑ i, u i * v i| ≤ ∑ i, |u i * v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖u‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm v i)
        (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * ‖u‖ * ‖v‖ := by simp [mul_assoc]

/-- The same double supremum used by the repository's finite-horizon LLN. -/
def fluctuationTimeSup (T : ℝ) (f : ℝ → ℝ) : ℝ :=
  ⨆ s : ℝ, ⨆ _ : 0 ≤ s ∧ s ≤ T, f s

private theorem fc_timeSup_nonneg {T : ℝ} {f : ℝ → ℝ}
    (hf : ∀ s, 0 ≤ f s) : 0 ≤ fluctuationTimeSup T f := by
  unfold fluctuationTimeSup
  exact Real.iSup_nonneg fun s => Real.iSup_nonneg fun _ => hf s

private theorem fc_timeSup_le {T B : ℝ} {f : ℝ → ℝ}
    (hB : 0 ≤ B) (hf : ∀ s ∈ Icc 0 T, f s ≤ B) :
    fluctuationTimeSup T f ≤ B := by
  unfold fluctuationTimeSup
  exact Real.iSup_le (fun s => Real.iSup_le (fun hs => hf s hs) hB) hB

private theorem fc_le_timeSup {T B s : ℝ} {f : ℝ → ℝ}
    (hB : 0 ≤ B) (hf : ∀ u ∈ Icc 0 T, f u ≤ B)
    (hs : s ∈ Icc 0 T) : f s ≤ fluctuationTimeSup T f := by
  have hi : BddAbove (Set.range (fun _ : 0 ≤ s ∧ s ≤ T => f s)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨h, rfl⟩
    exact hf s h
  have ho : BddAbove
      (Set.range (fun u : ℝ => ⨆ _ : 0 ≤ u ∧ u ≤ T, f u)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact Real.iSup_le (fun hu => hf u hu) hB
  exact (le_ciSup hi hs).trans (le_ciSup ho s)

private theorem fc_rate_continuous (Γ : RateSpec d)
    (ℓ : Fin d → ℤ) (hℓ : ℓ ∈ Γ.jumps) : Continuous (Γ.rate ℓ) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  let R : ℝ := ‖x‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨L, hL, hLip⟩ := Γ.rate_lipschitz ℓ hℓ R hR
  refine ⟨min 1 (ε / L), lt_min one_pos (div_pos hε hL), ?_⟩
  intro y hy
  have hy1 : dist y x < 1 := hy.trans_le (min_le_left _ _)
  have hyε : dist y x < ε / L := hy.trans_le (min_le_right _ _)
  have hxR : ‖x‖ ≤ R := by dsimp [R]; linarith
  have hyR : ‖y‖ ≤ R := by
    have htri : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      calc
        ‖y‖ = ‖x + (y - x)‖ := by congr 1; abel
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
    rw [dist_eq_norm] at hy1
    dsimp [R]
    linarith
  rw [dist_eq_norm]
  calc
    ‖Γ.rate ℓ y - Γ.rate ℓ x‖ ≤ L * ‖y - x‖ := hLip y x hyR hxR
    _ < L * (ε / L) :=
      mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hyε) hL
    _ = ε := by field_simp

private theorem fc_abs_integral_le {T C : ℝ} (hT : 0 ≤ T)
    (f : ℝ → ℝ) (hb : ∀ s ∈ Icc 0 T, |f s| ≤ C) :
    |∫ s in Icc 0 T, f s| ≤ T * C := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) :=
    ⟨by simpa using (measure_Icc_lt_top : volume (Icc (0 : ℝ) T) < ⊤)⟩
  have hbound : (fun s => |f s|) ≤ᵐ[volume.restrict (Icc 0 T)]
      (fun _ => C) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
    exact hb s hs
  calc
    |∫ s in Icc 0 T, f s| ≤ ∫ s in Icc 0 T, |f s| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (f := f) (μ := volume.restrict (Icc 0 T)))
    _ ≤ ∫ _s in Icc (0 : ℝ) T, C :=
      integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg (f s))
        (integrable_const C) hbound
    _ = T * C := by
      simp [Real.volume_Icc, hT, smul_eq_mul]

/-! ## L4: quadratic compensator -/

/-- `p ℓ s` is the coefficient denoted `p_ℓ(s)` in L4. -/
def fluctuationQuadraticCompensator (Γ : RateSpec d)
    (p : (Fin d → ℤ) → ℝ → ℝ) (X : ℝ → Fin d → ℝ) (T : ℝ) : ℝ :=
  ∫ s in Icc 0 T, ∑ ℓ ∈ Γ.jumps, Γ.rate ℓ (X s) * (p ℓ s) ^ 2

private theorem fc_quadratic_integrable (Γ : RateSpec d)
    (p : (Fin d → ℤ) → ℝ → ℝ) (P : (Fin d → ℤ) → ℝ)
    {T : ℝ} (hp : ∀ ℓ ∈ Γ.jumps, Measurable (p ℓ))
    (hP : ∀ ℓ ∈ Γ.jumps, ∀ s ∈ Icc 0 T, |p ℓ s| ≤ P ℓ)
    (X : ℝ → Fin d → ℝ) (hXm : Measurable X)
    (hX : ∀ s ∈ Icc 0 T, ‖X s‖ ≤ 1) :
    IntegrableOn
      (fun s => ∑ ℓ ∈ Γ.jumps, Γ.rate ℓ (X s) * (p ℓ s) ^ 2)
      (Icc 0 T) volume := by
  obtain ⟨B, hB, hrate⟩ := Γ.exists_rate_bound_on_ball 1 (by norm_num)
  have hm : Measurable
      (fun s => ∑ ℓ ∈ Γ.jumps, Γ.rate ℓ (X s) * (p ℓ s) ^ 2) :=
    Finset.measurable_sum _ fun ℓ hℓ =>
      ((fc_rate_continuous Γ ℓ hℓ).measurable.comp hXm).mul
        ((hp ℓ hℓ).pow_const 2)
  refine IntegrableOn.of_bound measure_Icc_lt_top hm.aestronglyMeasurable
    (∑ ℓ ∈ Γ.jumps, B * (P ℓ) ^ 2) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro ℓ hℓ
  have hpSq : (p ℓ s) ^ 2 ≤ (P ℓ) ^ 2 :=
    sq_le_sq' (abs_le.mp (hP ℓ hℓ s hs)).1
      (abs_le.mp (hP ℓ hℓ s hs)).2
  rw [abs_mul, abs_of_nonneg (sq_nonneg (p ℓ s))]
  exact mul_le_mul (hrate ℓ hℓ (X s) (hX s hs)) hpSq
    (sq_nonneg _) hB.le

/-- L4 with arbitrary certified coefficient bounds.  All constants occur
literally in the conclusion; no probability or convergence premise is used. -/
theorem fluctuation_quadratic_compensator_lipschitz
    (Γ : RateSpec d) (p : (Fin d → ℤ) → ℝ → ℝ)
    (L P : (Fin d → ℤ) → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hp : ∀ ℓ ∈ Γ.jumps, Measurable (p ℓ))
    (hP : ∀ ℓ ∈ Γ.jumps, ∀ s ∈ Icc 0 T, |p ℓ s| ≤ P ℓ)
    (hL : ∀ ℓ ∈ Γ.jumps, 0 ≤ L ℓ)
    (hLip : ∀ ℓ ∈ Γ.jumps, ∀ z w : Fin d → ℝ,
      ‖z‖ ≤ 1 → ‖w‖ ≤ 1 →
      |Γ.rate ℓ z - Γ.rate ℓ w| ≤ L ℓ * ‖z - w‖)
    (X x : ℝ → Fin d → ℝ) (hXm : Measurable X) (hxm : Measurable x)
    (hX : ∀ s ∈ Icc 0 T, ‖X s‖ ≤ 1)
    (hx : ∀ s ∈ Icc 0 T, ‖x s‖ ≤ 1) :
    |fluctuationQuadraticCompensator Γ p X T -
        fluctuationQuadraticCompensator Γ p x T| ≤
      (T * ∑ ℓ ∈ Γ.jumps, L ℓ * (P ℓ) ^ 2) *
        fluctuationTimeSup T (fun s => ‖X s - x s‖) := by
  let A : ℝ := ∑ ℓ ∈ Γ.jumps, L ℓ * (P ℓ) ^ 2
  let U : ℝ := fluctuationTimeSup T (fun s => ‖X s - x s‖)
  have hA : 0 ≤ A := Finset.sum_nonneg fun ℓ hℓ =>
    mul_nonneg (hL ℓ hℓ) (sq_nonneg _)
  have hU : 0 ≤ U := fc_timeSup_nonneg fun s => norm_nonneg _
  have hdiff : ∀ s ∈ Icc 0 T, ‖X s - x s‖ ≤ 2 := by
    intro s hs
    exact (norm_sub_le _ _).trans (by linarith [hX s hs, hx s hs])
  have hsup : ∀ s ∈ Icc 0 T, ‖X s - x s‖ ≤ U :=
    fun s hs => fc_le_timeSup (by norm_num) hdiff hs
  have hintX := fc_quadratic_integrable Γ p P hp hP X hXm hX
  have hintx := fc_quadratic_integrable Γ p P hp hP x hxm hx
  unfold fluctuationQuadraticCompensator
  rw [← integral_sub hintX hintx]
  have hbound : ∀ s ∈ Icc 0 T,
      |(∑ ℓ ∈ Γ.jumps, Γ.rate ℓ (X s) * (p ℓ s) ^ 2) -
        (∑ ℓ ∈ Γ.jumps, Γ.rate ℓ (x s) * (p ℓ s) ^ 2)| ≤ A * U := by
    intro s hs
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ ℓ ∈ Γ.jumps,
          (Γ.rate ℓ (X s) * (p ℓ s) ^ 2 -
            Γ.rate ℓ (x s) * (p ℓ s) ^ 2)| ≤
          ∑ ℓ ∈ Γ.jumps,
            |Γ.rate ℓ (X s) * (p ℓ s) ^ 2 -
              Γ.rate ℓ (x s) * (p ℓ s) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ℓ ∈ Γ.jumps, (L ℓ * ‖X s - x s‖) * (P ℓ) ^ 2 := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        have hpSq : (p ℓ s) ^ 2 ≤ (P ℓ) ^ 2 :=
          sq_le_sq' (abs_le.mp (hP ℓ hℓ s hs)).1
            (abs_le.mp (hP ℓ hℓ s hs)).2
        rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg (p ℓ s))]
        exact mul_le_mul (hLip ℓ hℓ _ _ (hX s hs) (hx s hs)) hpSq
          (sq_nonneg _) (mul_nonneg (hL ℓ hℓ) (norm_nonneg _))
      _ = A * ‖X s - x s‖ := by
        dsimp only [A]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ℓ _
        ring
      _ ≤ A * U := mul_le_mul_of_nonneg_left (hsup s hs) hA
  exact (fc_abs_integral_le hT _ hbound).trans (le_of_eq (by
    dsimp only [A, U]
    ring))

/-- The document's coefficient `p_ℓ`. -/
def fluctuationPairing (ψ : ℝ → Fin d → ℝ) (ℓ : Fin d → ℤ) (s : ℝ) : ℝ :=
  ψ s ⬝ᵥ (fun i => (ℓ i : ℝ))

/-- The exact `P_ℓ = sup_[0,T] |p_ℓ|` from L4. -/
def fluctuationPairingSup (ψ : ℝ → Fin d → ℝ) (T : ℝ) (ℓ : Fin d → ℤ) : ℝ :=
  fluctuationTimeSup T (fun s => |fluctuationPairing ψ ℓ s|)

/-- L4, equation (4.22), with precisely the coefficient suprema specified in
that equation.  A bounded Borel test is more general than the cut-off adjoint
sum used in the CLT. -/
theorem fluctuation_quadratic_compensator_lipschitz_exactSup
    (Γ : RateSpec d) (ψ : ℝ → Fin d → ℝ) (hψ : Measurable ψ)
    (L : (Fin d → ℤ) → ℝ) {T Cψ : ℝ} (hT : 0 ≤ T) (hCψ : 0 ≤ Cψ)
    (hψb : ∀ s ∈ Icc 0 T, ‖ψ s‖ ≤ Cψ)
    (hL : ∀ ℓ ∈ Γ.jumps, 0 ≤ L ℓ)
    (hLip : ∀ ℓ ∈ Γ.jumps, ∀ z w : Fin d → ℝ,
      ‖z‖ ≤ 1 → ‖w‖ ≤ 1 →
      |Γ.rate ℓ z - Γ.rate ℓ w| ≤ L ℓ * ‖z - w‖)
    (X x : ℝ → Fin d → ℝ) (hXm : Measurable X) (hxm : Measurable x)
    (hX : ∀ s ∈ Icc 0 T, ‖X s‖ ≤ 1)
    (hx : ∀ s ∈ Icc 0 T, ‖x s‖ ≤ 1) :
    |fluctuationQuadraticCompensator Γ (fluctuationPairing ψ) X T -
        fluctuationQuadraticCompensator Γ (fluctuationPairing ψ) x T| ≤
      (T * ∑ ℓ ∈ Γ.jumps, L ℓ * (fluctuationPairingSup ψ T ℓ) ^ 2) *
        fluctuationTimeSup T (fun s => ‖X s - x s‖) := by
  apply fluctuation_quadratic_compensator_lipschitz Γ (fluctuationPairing ψ)
    L (fluctuationPairingSup ψ T) hT
  · intro ℓ _
    exact fc_measurable_dot hψ measurable_const
  · intro ℓ _ s hs
    have hb : ∀ u ∈ Icc 0 T,
        |fluctuationPairing ψ ℓ u| ≤
          (d : ℝ) * Cψ * ‖(fun i => (ℓ i : ℝ))‖ := by
      intro u hu
      exact (fluctuation_abs_dot_le _ _).trans (by
        gcongr
        exact hψb u hu)
    exact fc_le_timeSup (by positivity) hb hs
  · exact hL
  · exact hLip
  · exact hXm
  · exact hxm
  · exact hX
  · exact hx

/-! ### Applying L4 to the actual frozen density readout -/

private theorem fc_scaled_nonneg_le_one (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) (i : Fin d) :
    0 ≤ M.scaledState z i ∧ M.scaledState z i ≤ 1 := by
  have hN : (0 : ℝ) < M.N := by exact_mod_cast M.hN
  change 0 ≤ (z i : ℝ) / M.N ∧ (z i : ℝ) / M.N ≤ 1
  refine ⟨div_nonneg (Nat.cast_nonneg _) hN.le, ?_⟩
  apply (div_le_one hN).2
  exact_mod_cast (Nat.le_of_lt_succ (z i).isLt)

private theorem fc_scaled_norm_le_one (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) : ‖M.scaledState z‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (fc_scaled_nonneg_le_one M z i).1]
  exact (fc_scaled_nonneg_le_one M z i).2

private theorem fc_frozen_measurable (M : DensityDepCTMC d)
    (ω : M.canonicalRecordΩ) :
    Measurable (fun s => M.frozenDensityProcess M.canonicalPathMap s ω) := by
  change Measurable (fun s => M.scaledState ((M.canonicalPathMap ω).frozenStateAt s))
  exact (Measurable.of_discrete (f := M.scaledState)).comp
    (M.measurable_canonicalPathMap_frozenStateAt_section ω)

private theorem fc_frozen_joint_measurable (M : DensityDepCTMC d) :
    Measurable (fun q : M.canonicalRecordΩ × ℝ =>
      M.frozenDensityProcess M.canonicalPathMap q.2 q.1) := by
  change Measurable (fun q : M.canonicalRecordΩ × ℝ =>
    M.scaledState ((M.canonicalPathMap q.1).frozenStateAt q.2))
  exact (Measurable.of_discrete (f := M.scaledState)).comp
    (M.measurable_prod_canonicalPathMap_frozenStateAt.comp measurable_swap)

/-- L4 is pathwise even on ambient records: the total frozen readout always
returns a lattice-cube state, whose scaled sup norm is at most one. -/
theorem fluctuation_quadratic_compensator_canonical_bound
    (M : DensityDepCTMC d) (p : (Fin d → ℤ) → ℝ → ℝ)
    (L P : (Fin d → ℤ) → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hp : ∀ ℓ ∈ M.rateSpec.jumps, Measurable (p ℓ))
    (hP : ∀ ℓ ∈ M.rateSpec.jumps, ∀ s ∈ Icc 0 T, |p ℓ s| ≤ P ℓ)
    (hL : ∀ ℓ ∈ M.rateSpec.jumps, 0 ≤ L ℓ)
    (hLip : ∀ ℓ ∈ M.rateSpec.jumps, ∀ z w : Fin d → ℝ,
      ‖z‖ ≤ 1 → ‖w‖ ≤ 1 →
      |M.rateSpec.rate ℓ z - M.rateSpec.rate ℓ w| ≤ L ℓ * ‖z - w‖)
    (x : ℝ → Fin d → ℝ) (hxm : Measurable x)
    (hx : ∀ s ∈ Icc 0 T, ‖x s‖ ≤ 1) (ω : M.canonicalRecordΩ) :
    |fluctuationQuadraticCompensator M.rateSpec p
          (fun s => M.frozenDensityProcess M.canonicalPathMap s ω) T -
        fluctuationQuadraticCompensator M.rateSpec p x T| ≤
      (T * ∑ ℓ ∈ M.rateSpec.jumps, L ℓ * (P ℓ) ^ 2) *
        fluctuationTimeSup T
          (fun s => ‖M.frozenDensityProcess M.canonicalPathMap s ω - x s‖) := by
  exact fluctuation_quadratic_compensator_lipschitz M.rateSpec p L P hT hp hP
    hL hLip _ x (fc_frozen_measurable M ω) hxm
    (fun s _ => fc_scaled_norm_le_one M _) hx

/-- Quantitative probability consequence of L4 and the already-proved LLN.
No maximal inequality or LLN estimate is carried as an unproved premise. -/
theorem fluctuation_quadratic_compensator_probability_of_close [NeZero d]
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (hcons : ∀ N (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBC : ∀ N (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hsol : ∀ s, 0 ≤ s → ‖mf.sol s‖ ≤ 1)
    (p : (Fin d → ℤ) → ℝ → ℝ) (L P : (Fin d → ℤ) → ℝ)
    {T : ℝ} (hT : 0 < T)
    (hp : ∀ ℓ ∈ Γ.jumps, Measurable (p ℓ))
    (hP : ∀ ℓ ∈ Γ.jumps, ∀ s ∈ Icc 0 T, |p ℓ s| ≤ P ℓ)
    (hL : ∀ ℓ ∈ Γ.jumps, 0 ≤ L ℓ)
    (hLip : ∀ ℓ ∈ Γ.jumps, ∀ z w : Fin d → ℝ,
      ‖z‖ ≤ 1 → ‖w‖ ≤ 1 →
      |Γ.rate ℓ z - Γ.rate ℓ w| ≤ L ℓ * ‖z - w‖)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hN : 0 < N)
      (z : Fin d → Fin (N + 1)),
      (DensityDepCTMC.mk N hN Γ).InSimplex z →
      ‖(fun i => (z i : ℝ) / (N : ℝ)) - mf.x₀‖ ≤ δ →
      let M := DensityDepCTMC.mk N hN Γ
      M.canonicalRecordMeasure z
        {ω | ε < |fluctuationQuadraticCompensator Γ p
            (fun s => M.frozenDensityProcess M.canonicalPathMap s ω) T -
          fluctuationQuadraticCompensator Γ p mf.sol T|} ≤ ENNReal.ofReal η := by
  let C : ℝ := T * ∑ ℓ ∈ Γ.jumps, L ℓ * (P ℓ) ^ 2
  have hC : 0 ≤ C := mul_nonneg hT.le
    (Finset.sum_nonneg fun ℓ hℓ => mul_nonneg (hL ℓ hℓ) (sq_nonneg _))
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨δ, hδ, N₀, hN₀⟩ :=
    kurtz_finite_horizon_of_close Γ mf hcons hBC hsol hT
      (ε / (C + 1)) (div_pos hε hC1) η hη
  refine ⟨δ, hδ, N₀, ?_⟩
  intro N hNN hN z hz hnear
  let M := DensityDepCTMC.mk N hN Γ
  change M.canonicalRecordMeasure z _ ≤ ENNReal.ofReal η
  have hQ : fluctuationQuadraticCompensator Γ p mf.extendLeft.sol T =
      fluctuationQuadraticCompensator Γ p mf.sol T := by
    unfold fluctuationQuadraticCompensator
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp only [mf.extendLeft_sol_of_nonneg hs.1]
  have hsub :
      {ω : M.canonicalRecordΩ | ε < |fluctuationQuadraticCompensator Γ p
          (fun s => M.frozenDensityProcess M.canonicalPathMap s ω) T -
        fluctuationQuadraticCompensator Γ p mf.sol T|} ⊆
      {ω : M.canonicalRecordΩ | ε / (C + 1) <
        ⨆ s : ℝ, ⨆ _ : 0 ≤ s ∧ s ≤ T,
          ‖M.frozenDensityProcess M.canonicalPathMap s ω - mf.sol s‖} := by
    intro ω hω
    have hb := fluctuation_quadratic_compensator_canonical_bound M p L P hT.le
      hp hP hL hLip mf.extendLeft.sol mf.extendLeft_measurable
      (fun s hs => by rw [mf.extendLeft_sol_of_nonneg hs.1]; exact hsol s hs.1) ω
    rw [hQ] at hb
    have hsup : fluctuationTimeSup T
        (fun s => ‖M.frozenDensityProcess M.canonicalPathMap s ω - mf.extendLeft.sol s‖) =
        fluctuationTimeSup T
          (fun s => ‖M.frozenDensityProcess M.canonicalPathMap s ω - mf.sol s‖) := by
      unfold fluctuationTimeSup
      refine iSup_congr fun s => iSup_congr fun hs => ?_
      simp only [mf.extendLeft_sol_of_nonneg hs.1]
    rw [hsup] at hb
    let U := fluctuationTimeSup T
      (fun s => ‖M.frozenDensityProcess M.canonicalPathMap s ω - mf.sol s‖)
    have hU : 0 ≤ U := fc_timeSup_nonneg fun s => norm_nonneg _
    change ε / (C + 1) < U
    by_contra hnot
    have hle : U ≤ ε / (C + 1) := le_of_not_gt hnot
    have hCU : C * U ≤ ε := by
      calc
        C * U ≤ (C + 1) * U := by nlinarith
        _ ≤ (C + 1) * (ε / (C + 1)) :=
          mul_le_mul_of_nonneg_left hle hC1.le
        _ = ε := by field_simp
    exact (not_lt_of_ge (hb.trans hCU)) hω
  exact (measure_mono hsub).trans (hN₀ N hNN hN z hz hnear)

/-! ## L5: rewriting the nonlinear compensator over the listed jumps -/

/-- An observable of existing lattice states, not a new transition model. -/
def fluctuationLatticeJump (M : DensityDepCTMC d)
    (x y : Fin d → Fin (M.N + 1)) : Fin d → ℤ :=
  fun i => (y i : ℤ) - (x i : ℤ)

private theorem fc_latticeJump_self (M : DensityDepCTMC d)
    (x : Fin d → Fin (M.N + 1)) : fluctuationLatticeJump M x x = 0 := by
  ext i
  simp [fluctuationLatticeJump]

private theorem fc_latticeJump_injective (M : DensityDepCTMC d)
    (x : Fin d → Fin (M.N + 1)) :
    Function.Injective (fluctuationLatticeJump M x) := by
  intro y z h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change (y i : ℤ) - (x i : ℤ) = (z i : ℤ) - (x i : ℤ) at hi
  have hcast : (y i : ℤ) = (z i : ℤ) := by linarith
  exact_mod_cast hcast

/-- The zero-observable version of the finite-sum rewrite.  Boundary
compatibility is used only in the branch with no lattice target. -/
theorem fluctuation_sum_rate_latticeJump
    (M : DensityDepCTMC d) (hBC : M.BoundaryCompatibleOnSimplex)
    {x : Fin d → Fin (M.N + 1)} (hx : M.InSimplex x)
    (f : (Fin d → ℤ) → ℂ) (hf : f 0 = 0) :
    (∑ y ∈ Finset.univ.filter (fun y => y ≠ x),
      (M.toQMatrix.rate x y : ℂ) * f (fluctuationLatticeJump M x y)) =
    (M.N : ℂ) * ∑ ℓ ∈ M.rateSpec.jumps,
      (M.rateSpec.rate ℓ (M.scaledState x) : ℂ) * f ℓ := by
  classical
  let w : (Fin d → ℤ) → ℂ := fun ℓ =>
    (M.N : ℂ) * (M.rateSpec.rate ℓ (M.scaledState x) : ℂ) * f ℓ
  have hrow (y : Fin d → Fin (M.N + 1)) :
      (if y ≠ x then
        (M.toQMatrix.rate x y : ℂ) * f (fluctuationLatticeJump M x y)
       else 0) =
      ∑ ℓ ∈ M.rateSpec.jumps,
        if fluctuationLatticeJump M x y = ℓ then w ℓ else 0 := by
    by_cases hy : y = x
    · subst y
      simp only [ne_eq, not_true_eq_false, if_false, fc_latticeJump_self]
      symm
      apply Finset.sum_eq_zero
      intro ℓ _
      by_cases hℓ : (0 : Fin d → ℤ) = ℓ
      · subst ℓ
        simp [w, hf]
      · simp [hℓ]
    · rw [if_pos hy, M.toQMatrix_rate_of_ne hy]
      have hfilter :
          M.rateSpec.jumps.filter
              (fun ℓ => ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) =
          M.rateSpec.jumps.filter
              (fun ℓ => fluctuationLatticeJump M x y = ℓ) := by
        ext ℓ
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hm, he⟩
          exact ⟨hm, funext he⟩
        · rintro ⟨hm, he⟩
          exact ⟨hm, fun i => congrFun he i⟩
      rw [DensityDepCTMC.offDiagRate, if_neg (Ne.symm hy), hfilter,
        Complex.ofReal_sum, Finset.sum_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ℓ _
      by_cases he : fluctuationLatticeJump M x y = ℓ
      · simp only [if_pos he, Complex.ofReal_mul, he]
        rfl
      · simp [he]
  rw [Finset.sum_filter]
  calc
    (∑ y, if y ≠ x then
        (M.toQMatrix.rate x y : ℂ) * f (fluctuationLatticeJump M x y)
      else 0) =
        ∑ y, ∑ ℓ ∈ M.rateSpec.jumps,
          if fluctuationLatticeJump M x y = ℓ then w ℓ else 0 :=
      Finset.sum_congr rfl fun y _ => hrow y
    _ = ∑ ℓ ∈ M.rateSpec.jumps, ∑ y,
        if fluctuationLatticeJump M x y = ℓ then w ℓ else 0 :=
      Finset.sum_comm
    _ = ∑ ℓ ∈ M.rateSpec.jumps, w ℓ := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      by_cases hex : ∃ y, fluctuationLatticeJump M x y = ℓ
      · obtain ⟨y, hy⟩ := hex
        rw [Finset.sum_eq_single y]
        · simp [hy]
        · intro z _ hzy
          have hz : fluctuationLatticeJump M x z ≠ ℓ := by
            intro hz
            exact hzy (fc_latticeJump_injective M x (hz.trans hy.symm))
          simp [hz]
        · simp
      · have hr : M.rateSpec.rate ℓ (M.scaledState x) = 0 :=
          hBC x hx ℓ hℓ (by
            rintro ⟨y, hy⟩
            exact hex ⟨y, funext hy⟩)
        have hw : w ℓ = 0 := by simp [w, hr]
        simp [hw]
    _ = (M.N : ℂ) * ∑ ℓ ∈ M.rateSpec.jumps,
        (M.rateSpec.rate ℓ (M.scaledState x) : ℂ) * f ℓ := by
      simp only [w, Finset.mul_sum, mul_assoc]

/-- L5, equation (4.23), including zero listed jumps and invalid targets. -/
theorem fluctuation_nonlinear_compensator_rewrite
    (M : DensityDepCTMC d) (hBC : M.BoundaryCompatibleOnSimplex)
    {z : Fin d → Fin (M.N + 1)} (hz : M.InSimplex z)
    (b : Fin d → ℝ) (h : ℝ → ℂ) (hzero : h 0 = 0) :
    (∑ y ∈ Finset.univ.filter (fun y => y ≠ z),
      (M.toQMatrix.rate z y : ℂ) *
        h ((b ⬝ᵥ (fun i => (y i : ℝ) - (z i : ℝ))) /
          Real.sqrt (M.N : ℝ))) =
      (M.N : ℂ) * ∑ ℓ ∈ M.rateSpec.jumps,
        (M.rateSpec.rate ℓ (M.scaledState z) : ℂ) *
          h ((b ⬝ᵥ (fun i => (ℓ i : ℝ))) / Real.sqrt (M.N : ℝ)) := by
  have hh := fluctuation_sum_rate_latticeJump M hBC hz
    (fun ℓ => h ((b ⬝ᵥ (fun i => (ℓ i : ℝ))) / Real.sqrt (M.N : ℝ)))
    (by simp [dotProduct, hzero])
  simpa [fluctuationLatticeJump] using hh

/-- L5, equation (4.24), with lattice rather than scaled increments. -/
theorem fluctuation_linear_compensator_rewrite
    (M : DensityDepCTMC d) (hBC : M.BoundaryCompatibleOnSimplex)
    {z : Fin d → Fin (M.N + 1)} (hz : M.InSimplex z) :
    (∑ y ∈ Finset.univ.filter (fun y => y ≠ z),
      M.toQMatrix.rate z y • (fun i => (y i : ℝ) - (z i : ℝ))) =
      (M.N : ℝ) • M.rateSpec.drift (M.scaledState z) := by
  ext i
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    M.sum_rate_mul_coord_sub hBC hz i

/-! ## L6: the total zero-off-Cauchy construction -/

private theorem fc_cauchy_iff (u : ℕ → ℝ) :
    CauchySeq u ↔ ∀ q : ℕ, ∃ R : ℕ, ∀ r ≥ R, ∀ s ≥ R,
      |u r - u s| < 1 / ((q : ℝ) + 1) := by
  constructor
  · intro hu q
    obtain ⟨R, hR⟩ := (Metric.cauchySeq_iff.mp hu)
      (1 / ((q : ℝ) + 1)) (by positivity)
    exact ⟨R, fun r hr s hs => by
      simpa only [Real.dist_eq] using hR r hr s hs⟩
  · intro hu
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨q, hq⟩ := exists_nat_gt (1 / ε)
    have hsmall : 1 / ((q : ℝ) + 1) < ε := by
      apply (div_lt_iff₀ (by positivity : 0 < (q : ℝ) + 1)).2
      have hq' : 1 < (q : ℝ) * ε := (div_lt_iff₀ hε).mp hq
      nlinarith
    obtain ⟨R, hR⟩ := hu q
    exact ⟨R, fun r hr s hs => by
      simpa only [Real.dist_eq] using (hR r hr s hs).trans hsmall⟩

open Classical in
/-- A limit on the Cauchy set and exactly zero off that set. -/
noncomputable def fluctuationLimitZero (u : ℕ → ℝ) : ℝ :=
  if h : CauchySeq u then (cauchySeq_tendsto_of_complete h).choose else 0

private theorem fc_limit_tendsto {u : ℕ → ℝ} (hu : CauchySeq u) :
    Tendsto u atTop (𝓝 (fluctuationLimitZero u)) := by
  simpa only [fluctuationLimitZero, dif_pos hu] using
    (cauchySeq_tendsto_of_complete hu).choose_spec

/-- The countable Cauchy-event construction from L6; `q+1` enumerates its
positive integer denominators. -/
theorem fluctuation_measurableSet_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (S : ℕ → Ω → ℝ) (hS : ∀ r, Measurable (S r)) :
    MeasurableSet {ω | CauchySeq (fun r => S r ω)} := by
  classical
  have heq : {ω | CauchySeq (fun r => S r ω)} =
      ⋂ q : ℕ, ⋃ R : ℕ, ⋂ r : ℕ, ⋂ s : ℕ,
        {ω | R ≤ r → R ≤ s →
          |S r ω - S s ω| < 1 / ((q : ℝ) + 1)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h q
      obtain ⟨R, hR⟩ := (fc_cauchy_iff _).mp h q
      exact ⟨R, fun r s hr hs => hR r hr s hs⟩
    · intro h
      apply (fc_cauchy_iff _).mpr
      intro q
      obtain ⟨R, hR⟩ := h q
      exact ⟨R, fun r hr s hs => hR r s hr hs⟩
  rw [heq]
  refine MeasurableSet.iInter fun q => MeasurableSet.iUnion fun R =>
    MeasurableSet.iInter fun r => MeasurableSet.iInter fun s => ?_
  by_cases hr : R ≤ r
  · by_cases hs : R ≤ s
    · simpa only [hr, hs, true_implies] using
        (measurableSet_lt ((hS r).sub (hS s)).abs measurable_const)
    · simp [hs]
  · simp [hr]

/-- Measurability is ordinary measurability, not only a.e. measurability. -/
theorem fluctuation_measurable_limitZero {Ω : Type*} [MeasurableSpace Ω]
    (S : ℕ → Ω → ℝ) (hS : ∀ r, Measurable (S r)) :
    Measurable (fun ω => fluctuationLimitZero (fun r => S r ω)) := by
  classical
  let C : Set Ω := {ω | CauchySeq (fun r => S r ω)}
  let F : ℕ → Ω → ℝ := fun r ω => if ω ∈ C then S r ω else 0
  have hC : MeasurableSet C := fluctuation_measurableSet_cauchy S hS
  have hF : ∀ r, Measurable (F r) :=
    fun r => Measurable.ite hC (hS r) measurable_const
  apply measurable_of_tendsto_metrizable hF
  apply tendsto_pi_nhds.mpr
  intro ω
  by_cases hω : CauchySeq (fun r => S r ω)
  · simpa only [F, C, Set.mem_setOf_eq, if_pos hω] using fc_limit_tendsto hω
  · simp only [F, C, Set.mem_setOf_eq, if_neg hω,
      fluctuationLimitZero, dif_neg hω]
    exact tendsto_const_nhds

private theorem fc_limit_eq_of_constant_tail (u : ℕ → ℝ) (K : ℕ) (a : ℝ)
    (hu : ∀ r, K ≤ r → u r = a) :
    CauchySeq u ∧ fluctuationLimitZero u = a := by
  have hc : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    refine ⟨K, fun r hr s hs => ?_⟩
    rw [hu r hr, hu s hs, dist_self]
    exact hε
  have heq : (fun _ : ℕ => a) =ᶠ[atTop] u :=
    (eventually_ge_atTop K).mono fun r hr => (hu r hr).symm
  have ht : Tendsto u atTop (𝓝 a) := tendsto_const_nhds.congr' heq
  exact ⟨hc, tendsto_nhds_unique (fc_limit_tendsto hc) ht⟩

private theorem fc_recTime_measurable (M : DensityDepCTMC d) (k : ℕ) :
    Measurable (fun ω : M.canonicalRecordΩ => QMatrix.recTime ω k) := by
  unfold QMatrix.recTime
  exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply (j + 1)).fst

private theorem fc_recTime_eq_sojourn (M : DensityDepCTMC d)
    (ω : M.canonicalRecordΩ) (k : ℕ) :
    QMatrix.recTime ω k = (M.canonicalPathMap ω).sojournStart k :=
  (M.canonicalPathMap_sojournStart ω k).symm

/-- Index `k` here is the document's jump index `k+1`.  Both indicators in
L6 are retained, including the state-change indicator after absorption. -/
def fluctuationJumpSummand (M : DensityDepCTMC d)
    (ψ : ℝ → Fin d → ℝ) (τ : ℝ) (k : ℕ) (ω : M.canonicalRecordΩ) : ℝ :=
  if QMatrix.recTime ω (k + 1) ≤ τ ∧ (ω (k + 1)).2 ≠ (ω k).2 then
    ψ (QMatrix.recTime ω (k + 1)) ⬝ᵥ
      (M.scaledState (ω (k + 1)).2 - M.scaledState (ω k).2)
  else 0

/-- The increment in the preceding definition is exactly the scaled record
increment in L6, not an increment of an auxiliary process. -/
theorem fluctuation_scaled_record_increment (M : DensityDepCTMC d)
    (ω : M.canonicalRecordΩ) (k : ℕ) (i : Fin d) :
    (M.scaledState (ω (k + 1)).2 - M.scaledState (ω k).2) i =
      (((ω (k + 1)).2 i : ℝ) - ((ω k).2 i : ℝ)) / (M.N : ℝ) := by
  change _ / (M.N : ℝ) - _ / (M.N : ℝ) = _
  ring

def fluctuationJumpPartialSum (M : DensityDepCTMC d)
    (ψ : ℝ → Fin d → ℝ) (τ : ℝ) (r : ℕ) (ω : M.canonicalRecordΩ) : ℝ :=
  ∑ k ∈ Finset.range r, fluctuationJumpSummand M ψ τ k ω

/-- The total functional requested in L6, including its off-Cauchy value. -/
def fluctuationJumpFunctional (M : DensityDepCTMC d)
    (ψ : ℝ → Fin d → ℝ) (τ : ℝ) (ω : M.canonicalRecordΩ) : ℝ :=
  fluctuationLimitZero (fun r => fluctuationJumpPartialSum M ψ τ r ω)

theorem measurable_fluctuationJumpSummand (M : DensityDepCTMC d)
    {ψ : ℝ → Fin d → ℝ} (hψ : Measurable ψ) (τ : ℝ) (k : ℕ) :
    Measurable (fluctuationJumpSummand M ψ τ k) := by
  classical
  have hnext : Measurable (fun ω : M.canonicalRecordΩ => (ω (k + 1)).2) :=
    (measurable_pi_apply (k + 1)).snd
  have hcur : Measurable (fun ω : M.canonicalRecordΩ => (ω k).2) :=
    (measurable_pi_apply k).snd
  have htime := fc_recTime_measurable M (k + 1)
  have hgate : MeasurableSet
      {ω : M.canonicalRecordΩ |
        QMatrix.recTime ω (k + 1) ≤ τ ∧ (ω (k + 1)).2 ≠ (ω k).2} :=
    (measurableSet_le htime measurable_const).inter
      (measurableSet_eq_fun hnext hcur).compl
  have hscaled : Measurable M.scaledState := Measurable.of_discrete
  exact Measurable.ite hgate
    (fc_measurable_dot (hψ.comp htime)
      ((hscaled.comp hnext).sub (hscaled.comp hcur))) measurable_const

theorem measurable_fluctuationJumpPartialSum (M : DensityDepCTMC d)
    {ψ : ℝ → Fin d → ℝ} (hψ : Measurable ψ) (τ : ℝ) (r : ℕ) :
    Measurable (fluctuationJumpPartialSum M ψ τ r) := by
  unfold fluctuationJumpPartialSum
  exact Finset.measurable_sum _ fun k _ =>
    measurable_fluctuationJumpSummand M hψ τ k

theorem measurable_fluctuationJumpFunctional (M : DensityDepCTMC d)
    {ψ : ℝ → Fin d → ℝ} (hψ : Measurable ψ) (τ : ℝ) :
    Measurable (fluctuationJumpFunctional M ψ τ) :=
  fluctuation_measurable_limitZero _
    (fun r => measurable_fluctuationJumpPartialSum M hψ τ r)

/-- A single record cutoff works for every test and every sub-horizon. -/
theorem fluctuation_goodRecords_cutoff (M : DensityDepCTMC d)
    {z : Fin d → Fin (M.N + 1)} {T : ℝ} {ω : M.canonicalRecordΩ}
    (hg : M.GoodRecords z T ω) :
    ∃ K : ℕ, ∀ k, K ≤ k →
      (ω (k + 1)).2 = (ω k).2 ∨ T < QMatrix.recTime ω (k + 1) := by
  rcases hg.absorb_or_escape with ⟨a, ha⟩ | ⟨r, hr⟩
  · refine ⟨a, fun k hk => Or.inl ?_⟩
    exact ((hg.stay_of_absorbing ha) (k + 1) (by omega)).1.trans
      (((hg.stay_of_absorbing ha) k hk).1.symm)
  · refine ⟨r, fun k hk => Or.inr ?_⟩
    rw [fc_recTime_eq_sojourn]
    change T < (M.canonicalPathMap ω).sojournStart (r + 1) at hr
    exact hr.trans_le (hg.sojournStart_mono (Nat.succ_le_succ hk))

/-- L6's eventual constancy, with all tests and sub-horizons inside the
quantifiers after the single cutoff.  No measurability assumption is needed
for this deterministic pathwise assertion. -/
theorem fluctuation_goodRecords_uniform_finite (M : DensityDepCTMC d)
    {z : Fin d → Fin (M.N + 1)} {T : ℝ} {ω : M.canonicalRecordΩ}
    (hg : M.GoodRecords z T ω) :
    ∃ K : ℕ, ∀ (ψ : ℝ → Fin d → ℝ) (τ : ℝ), τ ≤ T →
      (∀ k, K ≤ k → fluctuationJumpSummand M ψ τ k ω = 0) ∧
      (∀ r, K ≤ r → fluctuationJumpPartialSum M ψ τ r ω =
        fluctuationJumpPartialSum M ψ τ K ω) ∧
      CauchySeq (fun r => fluctuationJumpPartialSum M ψ τ r ω) ∧
      fluctuationJumpFunctional M ψ τ ω = fluctuationJumpPartialSum M ψ τ K ω := by
  obtain ⟨K, hK⟩ := fluctuation_goodRecords_cutoff M hg
  refine ⟨K, ?_⟩
  intro ψ τ hτ
  have hzero : ∀ k, K ≤ k → fluctuationJumpSummand M ψ τ k ω = 0 := by
    intro k hk
    rcases hK k hk with he | ht
    · simp [fluctuationJumpSummand, he]
    · have hnot : ¬ QMatrix.recTime ω (k + 1) ≤ τ :=
        not_le.mpr (hτ.trans_lt ht)
      simp [fluctuationJumpSummand, hnot]
  have hpartial : ∀ r, K ≤ r → fluctuationJumpPartialSum M ψ τ r ω =
      fluctuationJumpPartialSum M ψ τ K ω := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => rfl
    | succ r hr ih =>
        change (∑ k ∈ Finset.range (r + 1), fluctuationJumpSummand M ψ τ k ω) = _
        rw [Finset.sum_range_succ]
        change fluctuationJumpPartialSum M ψ τ r ω +
          fluctuationJumpSummand M ψ τ r ω = _
        rw [ih, hzero r hr, add_zero]
  have hlim := fc_limit_eq_of_constant_tail
    (fun r => fluctuationJumpPartialSum M ψ τ r ω) K
    (fluctuationJumpPartialSum M ψ τ K ω) hpartial
  exact ⟨hzero, hpartial, hlim.1, hlim.2⟩

/-- L6's common almost-sure event.  `GoodRecords` includes the record-zero,
holding-time, genuine-transition, absorption and simplex clauses.  The
additional displayed clause is simplex membership of every readout on the
whole horizon. -/
theorem fluctuation_common_event (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) (hcons : M.ConservativeJumps)
    (hz : M.InSimplex z) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂M.canonicalRecordMeasure z,
      M.GoodRecords z T ω ∧
      (∀ s ∈ Icc 0 T, M.InSimplex ((M.canonicalPathMap ω).frozenStateAt s)) ∧
      ∃ K : ℕ, ∀ (ψ : ℝ → Fin d → ℝ) (τ : ℝ), τ ≤ T →
        (∀ k, K ≤ k → fluctuationJumpSummand M ψ τ k ω = 0) ∧
        (∀ r, K ≤ r → fluctuationJumpPartialSum M ψ τ r ω =
          fluctuationJumpPartialSum M ψ τ K ω) ∧
        CauchySeq (fun r => fluctuationJumpPartialSum M ψ τ r ω) ∧
        fluctuationJumpFunctional M ψ τ ω = fluctuationJumpPartialSum M ψ τ K ω := by
  filter_upwards [M.goodRecords_ae z hcons hz hT] with ω hω
  exact ⟨hω, (fun s hs => hω.inSimplex_frozenStateAt hs),
    fluctuation_goodRecords_uniform_finite M hω⟩

/-! ### Total compensated and remainder functionals; measurability only -/

/-- The ordinary drift integral in the definition of `I_n`. -/
def fluctuationDriftIntegral (M : DensityDepCTMC d)
    (ψ : ℝ → Fin d → ℝ) (τ : ℝ) (ω : M.canonicalRecordΩ) : ℝ :=
  ∫ s in Icc 0 τ, ψ s ⬝ᵥ
    M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s ω)

/-- The total `I_n` in L6; time integration uses `Icc`, as in the existing
`frozenMartingalePart`. -/
def fluctuationCompensatedJump (M : DensityDepCTMC d)
    (ψ : ℝ → Fin d → ℝ) (τ : ℝ) (ω : M.canonicalRecordΩ) : ℝ :=
  fluctuationJumpFunctional M ψ τ ω - fluctuationDriftIntegral M ψ τ ω

/-- The total Taylor remainder `R_n` in L6. -/
def fluctuationRemainder (M : DensityDepCTMC d)
    (ψ x : ℝ → Fin d → ℝ) (τ : ℝ) (ω : M.canonicalRecordΩ) : ℝ :=
  ∫ s in Icc 0 τ, ψ s ⬝ᵥ
    (M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s ω) -
      M.rateSpec.drift (x s) -
      (fderiv ℝ M.rateSpec.drift (x s))
        (M.frozenDensityProcess M.canonicalPathMap s ω - x s))

theorem measurable_fluctuationDriftIntegral (M : DensityDepCTMC d)
    {ψ : ℝ → Fin d → ℝ} (hψ : Measurable ψ) (τ : ℝ) :
    Measurable (fluctuationDriftIntegral M ψ τ) := by
  have hm : Measurable (fun q : M.canonicalRecordΩ × ℝ =>
      ψ q.2 ⬝ᵥ M.rateSpec.drift
        (M.frozenDensityProcess M.canonicalPathMap q.2 q.1)) :=
    fc_measurable_dot (hψ.comp measurable_snd)
      (M.rateSpec.drift_continuous.measurable.comp (fc_frozen_joint_measurable M))
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Icc 0 τ))).measurable

theorem measurable_fluctuationCompensatedJump (M : DensityDepCTMC d)
    {ψ : ℝ → Fin d → ℝ} (hψ : Measurable ψ) (τ : ℝ) :
    Measurable (fluctuationCompensatedJump M ψ τ) :=
  (measurable_fluctuationJumpFunctional M hψ τ).sub
    (measurable_fluctuationDriftIntegral M hψ τ)

/-- For a repository mean-field solution, instantiate `x` by
`mf.extendLeft.sol`; it is measurable and agrees with `mf.sol` on `[0,∞)`. -/
theorem measurable_fluctuationRemainder (M : DensityDepCTMC d)
    {ψ x : ℝ → Fin d → ℝ} (hψ : Measurable ψ) (hx : Measurable x)
    (hF : ContDiff ℝ 1 M.rateSpec.drift) (τ : ℝ) :
    Measurable (fluctuationRemainder M ψ x τ) := by
  have hX := fc_frozen_joint_measurable M
  have hx' : Measurable (fun q : M.canonicalRecordΩ × ℝ => x q.2) :=
    hx.comp measurable_snd
  have hD : Continuous (fderiv ℝ M.rateSpec.drift) :=
    hF.continuous_fderiv (by simp)
  have heval : Continuous
      (fun q : ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) × (Fin d → ℝ) => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  have hlin : Measurable (fun q : M.canonicalRecordΩ × ℝ =>
      (fderiv ℝ M.rateSpec.drift (x q.2))
        (M.frozenDensityProcess M.canonicalPathMap q.2 q.1 - x q.2)) :=
    heval.measurable.comp ((hD.measurable.comp hx').prodMk (hX.sub hx'))
  have hm : Measurable (fun q : M.canonicalRecordΩ × ℝ =>
      ψ q.2 ⬝ᵥ
        (M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap q.2 q.1) -
          M.rateSpec.drift (x q.2) -
          (fderiv ℝ M.rateSpec.drift (x q.2))
            (M.frozenDensityProcess M.canonicalPathMap q.2 q.1 - x q.2))) :=
    fc_measurable_dot (hψ.comp measurable_snd)
      (((M.rateSpec.drift_continuous.measurable.comp hX).sub
        (M.rateSpec.drift_continuous.measurable.comp hx')).sub hlin)
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Icc 0 τ))).measurable

end

end Ripple.Kurtz

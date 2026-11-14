-- Ripple/Kurtz/StrongApprox/CellRandomTimeEvaluation.lean
import Ripple.Kurtz.StrongApprox.PoissonCellTimeChangeFactor
import Ripple.Kurtz.StrongApprox.PoissonPathArrivals
import Mathlib.MeasureTheory.Function.Floor

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellRandomTimeEvaluation

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

/-- The denominator of the `m`-th upper dyadic grid. -/
def dyadicDen (m : ℕ) : ℕ := 2 ^ m

theorem dyadicDen_pos (m : ℕ) : 0 < dyadicDen m := by
  simp [dyadicDen]

/-- Integer upper-grid coordinate. -/
noncomputable def upperDyadicIndex (m : ℕ) (t : ℝ≥0) : ℕ :=
  Nat.ceil ((dyadicDen m : ℝ) * (t : ℝ))

/-- A nonnegative dyadic grid point. -/
noncomputable def dyadicGridTime (m k : ℕ) : ℝ≥0 :=
  (k : ℝ≥0) / (dyadicDen m : ℝ≥0)

/-- Approximation of `t` from above on the `m`-th dyadic grid. -/
noncomputable def upperDyadicTime (m : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  dyadicGridTime m (upperDyadicIndex m t)

@[fun_prop]
theorem measurable_upperDyadicIndex (m : ℕ) :
    Measurable (upperDyadicIndex m) := by
  unfold upperDyadicIndex
  exact Nat.measurable_ceil.comp
    (measurable_const.mul measurable_coe_nnreal_real)

@[fun_prop]
theorem measurable_upperDyadicTime (m : ℕ) :
    Measurable (upperDyadicTime m) := by
  unfold upperDyadicTime
  exact (measurable_of_countable (dyadicGridTime m)).comp
    (measurable_upperDyadicIndex m)

theorem upperDyadicIndex_le_iff (m k : ℕ) (t : ℝ≥0) :
    upperDyadicIndex m t ≤ k ↔ t ≤ dyadicGridTime m k := by
  have hd : (0 : ℝ) < (dyadicDen m : ℝ) := by
    exact_mod_cast dyadicDen_pos m
  unfold upperDyadicIndex dyadicGridTime
  rw [Nat.ceil_le]
  change (dyadicDen m : ℝ) * (t : ℝ) ≤ (k : ℝ) ↔
    (t : ℝ) ≤ (k : ℝ) / (dyadicDen m : ℝ)
  rw [le_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem le_upperDyadicTime (m : ℕ) (t : ℝ≥0) :
    t ≤ upperDyadicTime m t := by
  exact (upperDyadicIndex_le_iff m (upperDyadicIndex m t) t).1 le_rfl

theorem dist_upperDyadicTime_le (m : ℕ) (t : ℝ≥0) :
    dist (upperDyadicTime m t : ℝ) (t : ℝ) ≤ (1 / 2 : ℝ) ^ m := by
  have hd : (0 : ℝ) < (dyadicDen m : ℝ) := by
    exact_mod_cast dyadicDen_pos m
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ (dyadicDen m : ℝ) * (t : ℝ) by positivity)
  have hupper :
      (upperDyadicTime m t : ℝ) <
        (t : ℝ) + 1 / (dyadicDen m : ℝ) := by
    unfold upperDyadicTime dyadicGridTime upperDyadicIndex
    apply (div_lt_iff₀ hd).2
    have heq :
        ((t : ℝ) + 1 / (dyadicDen m : ℝ)) * (dyadicDen m : ℝ) =
          (dyadicDen m : ℝ) * (t : ℝ) + 1 := by
      field_simp [ne_of_gt hd]
    rw [heq]
    exact hceil
  have hge : (t : ℝ) ≤ (upperDyadicTime m t : ℝ) := by
    exact_mod_cast le_upperDyadicTime m t
  have hpow : 1 / (dyadicDen m : ℝ) = (1 / 2 : ℝ) ^ m := by
    simp [dyadicDen, one_div_pow]
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hge)]
  linarith

theorem upperDyadicTime_tendsto_right (t : ℝ≥0) :
    Tendsto (fun m => (upperDyadicTime m t : ℝ)) atTop
      (𝓝[≥] (t : ℝ)) := by
  have hpow : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hup : Tendsto (fun m : ℕ => (t : ℝ) + (1 / 2 : ℝ) ^ m) atTop
      (𝓝 (t : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (t : ℝ))).add hpow
  have hmetric : Tendsto (fun m => (upperDyadicTime m t : ℝ)) atTop
      (𝓝 (t : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun m => ?_) (fun m => ?_)
    · exact_mod_cast le_upperDyadicTime m t
    · have h := dist_upperDyadicTime_le m t
      rw [Real.dist_eq] at h
      linarith [(abs_le.mp h).2]
  apply tendsto_nhdsWithin_iff.2
  refine ⟨hmetric, ?_⟩
  exact Filter.Eventually.of_forall fun m => by
    exact_mod_cast le_upperDyadicTime m t

theorem upperDyadicTime_add_tendsto_right (t q : ℝ≥0) :
    Tendsto (fun m => (upperDyadicTime m t : ℝ) + (q : ℝ)) atTop
      (𝓝[≥] ((t : ℝ) + (q : ℝ))) := by
  have h := upperDyadicTime_tendsto_right t
  apply tendsto_nhdsWithin_iff.2
  constructor
  · exact (h.mono_right nhdsWithin_le_nhds).add_const (q : ℝ)
  · filter_upwards [h.eventually self_mem_nhdsWithin] with m hm
    simp only [Set.mem_Ici] at hm ⊢
    linarith

/-- A fixed cell path is right-continuous because it is the canonical
`poisPath` of `cellSample`. -/
theorem cellPath_eventually_right (c : ℕ → CellSpace)
    (t : ℝ) :
    ∀ᶠ s in 𝓝[≥] t, cellPath s c =
      cellPath t c := by
  simpa only [← poisPath_cellSample] using
    (poisPath_eventually_right
      canonicalCount t
      (cellSample c))

theorem cellPath_upperDyadic_eventually
    (c : ℕ → CellSpace) (t : ℝ≥0) :
    ∀ᶠ m : ℕ in atTop,
      cellPath (upperDyadicTime m t) c =
        cellPath t c := by
  exact (upperDyadicTime_tendsto_right t).eventually
    (cellPath_eventually_right c (t : ℝ))

theorem cellPath_upperDyadic_add_eventually
    (c : ℕ → CellSpace) (t q : ℝ≥0) :
    ∀ᶠ m : ℕ in atTop,
      cellPath
          ((upperDyadicTime m t : ℝ) + (q : ℝ)) c =
        cellPath ((t : ℝ) + (q : ℝ)) c := by
  exact (upperDyadicTime_add_tendsto_right t q).eventually
    (cellPath_eventually_right c ((t : ℝ) + (q : ℝ)))

/-- Evaluation at a countably-valued measurable random time is measurable.
This is the step that is unavailable on the uncountable flat-driver product. -/
theorem measurable_cellPath_at_countable_time
    {X : Type*} [MeasurableSpace X]
    (C : X → ℕ → CellSpace) (hC : Measurable C)
    (τ : X → ℝ) (hτ : Measurable τ)
    (hcount : (Set.range τ).Countable) :
    Measurable fun x => cellPath (τ x) (C x) := by
  classical
  haveI : Countable (Set.range τ) := hcount.to_subtype
  apply measurable_to_countable'
  intro k
  show MeasurableSet {x | cellPath (τ x) (C x) = k}
  have hset :
      {x | cellPath (τ x) (C x) = k} =
        ⋃ r : Set.range τ,
          {x | τ x = r.1} ∩
            {x | cellPath r.1 (C x) = k} := by
    ext x
    constructor
    · intro hx
      apply Set.mem_iUnion.mpr
      refine ⟨⟨τ x, ⟨x, rfl⟩⟩, rfl, hx⟩
    · intro hx
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hr ⊢
      rw [hr.1]
      exact hr.2
  rw [hset]
  apply MeasurableSet.iUnion
  intro r
  exact (hτ (measurableSet_singleton r.1)).inter
    ((measurable_cellPath r.1).comp hC
      (measurableSet_singleton k))

private theorem upperTime_range_countable (m : ℕ) :
    (Set.range fun p : (ℕ → CellSpace) × ℝ≥0 =>
      (upperDyadicTime m p.2 : ℝ)).Countable := by
  refine Set.Countable.mono ?_
    (Set.countable_range fun k : ℕ => (dyadicGridTime m k : ℝ))
  rintro x ⟨p, rfl⟩
  exact ⟨upperDyadicIndex m p.2, rfl⟩

private theorem measurable_cellPath_upper_approx (m : ℕ) :
    Measurable fun p : (ℕ → CellSpace) × ℝ≥0 =>
      cellPath (upperDyadicTime m p.2) p.1 := by
  apply measurable_cellPath_at_countable_time
    (fun p : (ℕ → CellSpace) × ℝ≥0 => p.1)
    measurable_fst
    (fun p => (upperDyadicTime m p.2 : ℝ))
    (measurable_coe_nnreal_real.comp
      ((measurable_upperDyadicTime m).comp measurable_snd))
    (upperTime_range_countable m)

/-- **Joint evaluation theorem.**  The map `(c,t) ↦ cellPath t c` is
measurable on the cell carrier and nonnegative time. -/
@[fun_prop]
theorem measurable_cellPath_joint :
    Measurable fun p : (ℕ → CellSpace) × ℝ≥0 =>
      cellPath p.2 p.1 := by
  apply measurable_to_countable'
  intro k
  let F : ℕ → ((ℕ → CellSpace) × ℝ≥0) → ℕ :=
    fun m p => cellPath (upperDyadicTime m p.2) p.1
  have hF : ∀ m, Measurable (F m) := measurable_cellPath_upper_approx
  have hevent (p : (ℕ → CellSpace) × ℝ≥0) :
      ∀ᶠ m : ℕ in atTop,
        F m p = cellPath p.2 p.1 := by
    exact cellPath_upperDyadic_eventually p.1 p.2
  show MeasurableSet {p : (ℕ → CellSpace) × ℝ≥0 | cellPath p.2 p.1 = k}
  have hset :
      {p : (ℕ → CellSpace) × ℝ≥0 | cellPath p.2 p.1 = k} =
        ⋃ N : ℕ, ⋂ m : ℕ, {p | N ≤ m → F m p = k} := by
    ext p
    constructor
    · intro hp
      obtain ⟨N, hN⟩ := (eventually_atTop.1 (hevent p))
      apply Set.mem_iUnion.mpr
      refine ⟨N, Set.mem_iInter.mpr fun m => ?_⟩
      intro hNm
      show F m p = k
      rw [hN m hNm]
      exact hp
    · intro hp
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hp
      obtain ⟨M, hM⟩ := eventually_atTop.1 (hevent p)
      have hNM : F (max N M) p = k :=
        (Set.mem_iInter.mp hN (max N M)) (le_max_left _ _)
      rw [hM (max N M) (le_max_right _ _)] at hNM
      exact hNM
  rw [hset]
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro m
  by_cases hNm : N ≤ m
  · have e : {p : (ℕ → CellSpace) × ℝ≥0 | N ≤ m → F m p = k} = F m ⁻¹' {k} := by
      ext p
      simp [hNm]
    rw [e]
    exact (hF m) (measurableSet_singleton k)
  · have e : {p : (ℕ → CellSpace) × ℝ≥0 | N ≤ m → F m p = k} = Set.univ := by
      ext p
      simp [hNm]
    rw [e]
    exact MeasurableSet.univ

/-- Random-time evaluation for one channel of a measurable cell family. -/
theorem measurable_cellFamilyPath_randomTime
    {X ι : Type*} [MeasurableSpace X]
    (C : X → CellFamily ι) (hC : Measurable C)
    (τ : X → ι → ℝ≥0) (hτ : Measurable τ) (l : ι) :
    Measurable fun x =>
      cellPath (τ x l) (C x l) := by
  have h : Measurable ((fun p : (ℕ → CellSpace) × ℝ≥0 => cellPath p.2 p.1) ∘
      fun x => (C x l, τ x l)) :=
    measurable_cellPath_joint.comp
      (((measurable_pi_apply l).comp hC).prodMk
        ((measurable_pi_apply l).comp hτ))
  exact h

/-- Shifted count at a nonnegative delay. -/
noncomputable def shiftedCount {ι : Type*}
    (σ : CellFamily ι → ι → ℝ≥0)
    (c : CellFamily ι) (l : ι) (q : ℝ≥0) : ℕ :=
  cellPath ((σ c l : ℝ) + (q : ℝ)) (c l) -
    cellPath (σ c l) (c l)

@[fun_prop]
theorem measurable_shiftedCount {ι : Type*}
    {σ : CellFamily ι → ι → ℝ≥0}
    (hσ : Measurable σ) (l : ι) (q : ℝ≥0) :
    Measurable fun c => shiftedCount σ c l q := by
  have hs : Measurable fun c => σ c l :=
    (measurable_pi_apply l).comp hσ
  have he : Measurable fun c => σ c l + q := hs.add measurable_const
  exact (measurable_cellFamilyPath_randomTime id measurable_id
      (fun c => fun _ => σ c l + q)
      (measurable_pi_lambda _ fun _ => he) l).sub
    (measurable_cellFamilyPath_randomTime id measurable_id σ hσ l)

/-- First strictly positive rational future delay, as an extended nonnegative
real.  The value is `∞` only on a path with no later arrival. -/
noncomputable def residualWaitE {ι : Type*}
    (σ : CellFamily ι → ι → ℝ≥0)
    (c : CellFamily ι) (l : ι) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0,
    if 0 < q ∧ 0 < shiftedCount σ c l (q : ℝ≥0) then
      ((q : ℝ≥0) : ℝ≥0∞)
    else ⊤

@[fun_prop]
theorem measurable_residualWaitE {ι : Type*}
    {σ : CellFamily ι → ι → ℝ≥0}
    (hσ : Measurable σ) (l : ι) :
    Measurable fun c => residualWaitE σ c l := by
  unfold residualWaitE
  apply Measurable.iInf
  intro q
  by_cases hq : 0 < q
  · simp only [hq, true_and]
    exact Measurable.ite
      (measurableSet_lt measurable_const
        (measurable_shiftedCount hσ l (q : ℝ≥0)))
      measurable_const measurable_const
  · simp [hq]

/-- Real-valued residual used by `clockLaw`; the deterministic renewal law
proves that the exceptional `∞` set is null. -/
noncomputable def residualWait {ι : Type*}
    (σ : CellFamily ι → ι → ℝ≥0)
    (c : CellFamily ι) (l : ι) : ℝ :=
  (residualWaitE σ c l).toReal

@[fun_prop]
theorem measurable_residualWait {ι : Type*}
    {σ : CellFamily ι → ι → ℝ≥0}
    (hσ : Measurable σ) (l : ι) :
    Measurable fun c => residualWait σ c l :=
  ENNReal.measurable_toReal.comp (measurable_residualWaitE hσ l)

noncomputable def residualVector {ι : Type*}
    (σ : CellFamily ι → ι → ℝ≥0)
    (c : CellFamily ι) : ι → ℝ :=
  fun l => residualWait σ c l

@[fun_prop]
theorem measurable_residualVector {ι : Type*}
    {σ : CellFamily ι → ι → ℝ≥0}
    (hσ : Measurable σ) : Measurable (residualVector σ) := by
  apply measurable_pi_lambda
  intro l
  exact measurable_residualWait hσ l

/-- Pointwise monotonicity, restricted to the actual cell path. -/
theorem cellPath_mono (c : ℕ → CellSpace)
    {s t : ℝ} (hst : s ≤ t) :
    cellPath s c ≤
      cellPath t c := by
  simpa only [← poisPath_cellSample] using
    (poisPath_mono canonicalCount hst
      (cellSample c))

/-- Local finiteness, again only for paths produced by cells. -/
theorem cellPath_locallyFiniteJumps
    (c : ℕ → CellSpace) (U : ℝ) :
    LocallyFiniteJumpsOn (fun t => cellPath t c) U := by
  simpa only [← poisPath_cellSample] using
    (poisPath_locallyFiniteJumps
      canonicalCount U
      (cellSample c))

end Ripple.Kurtz.StrongApprox.CellRandomTimeEvaluation

end

import Ripple.Kurtz.StrongApprox.SectionFourUTailKurtz

/-!
# The fluid limit of the Kurtz diffusion

For rates `0 ≤ f_l ≤ ε_l` satisfying the Lipschitz condition (3.19), the drift
`F = tcDrift f v` is bounded by `C = Σ_l ‖v_l‖ ε_l` and globally Lipschitz with constant
`L = M Σ_l ‖v_l‖ ε_l`. For every initial point `x₀` the integral equation

`X t = x₀ + ∫₀ᵗ F (X s) ds`, `t ≥ 0`,

has a continuous solution (`exists_fluid_solution`), and it is unique among continuous
solutions (`fluid_solution_unique_Icc`, `eq_kurtzFluidLimit_of_continuous`).

Construction: on `[0, n]` Mathlib's Picard–Lindelöf fixed point
(`ODE.FunSpace.exists_isFixedPt_next` for `IsPicardLindelof.of_time_independent` with ball radius
`C n`) gives a continuous solution; the solutions for different `n` agree on the common
interval by Gronwall (`SectionFourAssembly.gronwall_norm_le`), and they glue to a global
solution.

`sectionFour_U_tail_kurtz_fluid` is `sectionFour_U_tail_kurtz` with `X` the fluid limit
`kurtzFluidLimit f v x₀`, so the premises on `X` disappear.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox

open SectionFourAssembly

section Fluid

variable {ι : Type*} [Fintype ι] {d : ℕ} {f : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
  {eps : ι → ℝ} {M : ℝ}

/-- The drift bound `C = Σ_l ‖v_l‖ ε_l`. -/
def kurtzDriftBound (v : ι → Fin d → ℝ) (eps : ι → ℝ) : ℝ := ∑ l, ‖v l‖ * eps l

theorem kurtzDriftBound_nonneg (heps : ∀ l, 0 ≤ eps l) : 0 ≤ kurtzDriftBound v eps :=
  Finset.sum_nonneg fun l _ => mul_nonneg (norm_nonneg _) (heps l)

theorem norm_tcDrift_le_kurtzDriftBound (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (x : Fin d → ℝ) : ‖tcDrift f v x‖ ≤ kurtzDriftBound v eps := by
  unfold tcDrift kurtzDriftBound
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf0 l x), mul_comm]
  exact mul_le_mul_of_nonneg_left (hfB l x) (norm_nonneg _)

/-- Uniqueness on `[0, T]` among continuous solutions (Gronwall). -/
theorem fluid_solution_unique_Icc (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) {x0 : Fin d → ℝ} {T : ℝ}
    (hT : 0 ≤ T) {Y W : ℝ → Fin d → ℝ} (hYc : Continuous Y) (hWc : Continuous W)
    (hY : ∀ t ∈ Icc (0 : ℝ) T, Y t = x0 + ∫ s in (0 : ℝ)..t, tcDrift f v (Y s))
    (hW : ∀ t ∈ Icc (0 : ℝ) T, W t = x0 + ∫ s in (0 : ℝ)..t, tcDrift f v (W s)) :
    ∀ t ∈ Icc (0 : ℝ) T, Y t = W t := by
  have hFc := continuous_tcDrift (continuous_rate_of_lip heps hM h319) v
  have h := gronwall_norm_le (T := T) (L := kurtzDriftLip v eps M) (s := 0) hT
    (kurtzDriftLip_nonneg heps hM) le_rfl (D := fun t => Y t - W t) (M := fun _ => 0)
    (Fd := fun u => tcDrift f v (Y u) - tcDrift f v (W u)) (hYc.sub hWc)
    ((hFc.comp hYc).sub (hFc.comp hWc)).continuousOn (fun _ _ => by simp)
    (fun t ht => by
      beta_reduce
      have i1 : IntervalIntegrable (fun s => tcDrift f v (Y s)) volume 0 t :=
        (hFc.comp hYc).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun s => tcDrift f v (W s)) volume 0 t :=
        (hFc.comp hWc).intervalIntegrable _ _
      rw [hY t ht, hW t ht, intervalIntegral.integral_sub i1 i2]
      abel)
    (fun u _ => norm_tcDrift_sub_le h319 _ _)
  intro t ht
  have h0 := h t ht
  rw [zero_mul] at h0
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/-- Existence on `[0, T]` from the Picard–Lindelöf fixed point. -/
theorem exists_fluid_solution_Icc (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) (x0 : Fin d → ℝ) {T : ℝ}
    (hT : 0 ≤ T) :
    ∃ Y : ℝ → Fin d → ℝ, Continuous Y ∧
      ∀ t ∈ Icc (0 : ℝ) T, Y t = x0 + ∫ s in (0 : ℝ)..t, tcDrift f v (Y s) := by
  have hC := kurtzDriftBound_nonneg (v := v) heps
  have hL := kurtzDriftLip_nonneg (v := v) heps hM
  let t0 : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hb : ∀ x ∈ closedBall x0 ((kurtzDriftBound v eps * T).toNNReal : ℝ),
      ‖tcDrift f v x‖ ≤ ((kurtzDriftBound v eps).toNNReal : ℝ) := fun x _ => by
    rw [Real.coe_toNNReal _ hC]
    exact norm_tcDrift_le_kurtzDriftBound hf0 hfB x
  have hl : LipschitzOnWith (kurtzDriftLip v eps M).toNNReal (tcDrift f v)
      (closedBall x0 ((kurtzDriftBound v eps * T).toNNReal : ℝ)) := by
    refine (LipschitzWith.of_dist_le_mul fun x y => ?_).lipschitzOnWith
    rw [Real.coe_toNNReal _ hL, dist_eq_norm, dist_eq_norm]
    exact norm_tcDrift_sub_le h319 x y
  have hm : ((kurtzDriftBound v eps).toNNReal : ℝ) * max (T - (t0 : ℝ)) ((t0 : ℝ) - 0) ≤
      ((kurtzDriftBound v eps * T).toNNReal : ℝ) - ((0 : ℝ≥0) : ℝ) := by
    show ((kurtzDriftBound v eps).toNNReal : ℝ) * max (T - 0) (0 - 0) ≤
      ((kurtzDriftBound v eps * T).toNNReal : ℝ) - ((0 : ℝ≥0) : ℝ)
    rw [Real.coe_toNNReal _ hC, Real.coe_toNNReal _ (mul_nonneg hC hT)]
    simp [max_eq_left hT]
  have hpl := IsPicardLindelof.of_time_independent (t₀ := t0) hb hl hm
  have hx : x0 ∈ closedBall x0 ((0 : ℝ≥0) : ℝ) := mem_closedBall_self le_rfl
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl hx
  refine ⟨α.compProj, α.continuous_compProj, fun t ht => ?_⟩
  have h1 : α.compProj t = ODE.FunSpace.next hpl hx α ⟨t, ht⟩ := by
    rw [ODE.FunSpace.compProj_of_mem ht, hα.eq]
  rw [h1, ODE.FunSpace.next_apply, ODE.picard_apply]

/-- Global existence of a continuous solution, by gluing the solutions on `[0, n]`. -/
theorem exists_fluid_solution (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) (x0 : Fin d → ℝ) :
    ∃ X : ℝ → Fin d → ℝ, Continuous X ∧
      ∀ t, 0 ≤ t → X t = x0 + ∫ s in (0 : ℝ)..t, tcDrift f v (X s) := by
  choose β hβc hβ using fun n : ℕ =>
    exists_fluid_solution_Icc (v := v) heps hM hf0 hfB h319 x0 (Nat.cast_nonneg (α := ℝ) n)
  -- the solutions agree on common intervals
  have hagree : ∀ k m : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ k → t ≤ m → β k t = β m t := by
    intro k m t ht0 htk htm
    have hmin : (0 : ℝ) ≤ min (k : ℝ) m := le_min (Nat.cast_nonneg k) (Nat.cast_nonneg m)
    exact fluid_solution_unique_Icc heps hM h319 hmin (hβc k) (hβc m)
      (fun s hs => hβ k s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩)
      (fun s hs => hβ m s ⟨hs.1, hs.2.trans (min_le_right _ _)⟩) t ⟨ht0, le_min htk htm⟩
  let X : ℝ → Fin d → ℝ := fun t => β ⌈t⌉₊ (max t 0)
  have hXm : ∀ m : ℕ, ∀ t : ℝ, t ≤ m → X t = β m (max t 0) := by
    intro m t htm
    refine hagree _ m _ (le_max_right t 0) ?_ (max_le htm (Nat.cast_nonneg m))
    rcases le_total 0 t with h | h
    · rw [max_eq_left h]
      exact Nat.le_ceil t
    · rw [max_eq_right h]
      exact Nat.cast_nonneg _
  have hmaxc : Continuous fun t : ℝ => max t 0 := continuous_id.max continuous_const
  refine ⟨X, ?_, fun t ht => ?_⟩
  · refine continuous_iff_continuousAt.2 fun t => ?_
    have hlt : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil t]
    refine ((hβc (⌈t⌉₊ + 1)).comp hmaxc).continuousAt.congr ?_
    filter_upwards [Iio_mem_nhds hlt] with s hs
    exact (hXm _ s (le_of_lt hs)).symm
  · have hX : X t = β ⌈t⌉₊ t := by
      rw [hXm ⌈t⌉₊ t (Nat.le_ceil t), max_eq_left ht]
    rw [hX, hβ ⌈t⌉₊ t ⟨ht, Nat.le_ceil t⟩]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    have hs' : X s = β ⌈t⌉₊ s := by
      rw [hXm ⌈t⌉₊ s (hs.2.trans (Nat.le_ceil t)), max_eq_left hs.1]
    simp only [hs']

/-- The fluid limit as a path indexed by `ℝ`: a continuous solution of
`X t = x₀ + ∫₀ᵗ tcDrift f v (X s) ds` for `t ≥ 0` (one exists under the model conditions). -/
def kurtzFluidPath (f : ι → (Fin d → ℝ) → ℝ) (v : ι → Fin d → ℝ) (x0 : Fin d → ℝ) :
    ℝ → Fin d → ℝ :=
  Classical.epsilon fun X : ℝ → Fin d → ℝ => Continuous X ∧
    ∀ t, 0 ≤ t → X t = x0 + ∫ s in (0 : ℝ)..t, tcDrift f v (X s)

/-- The fluid limit indexed by `ℝ≥0`, the form used by the Section 4 tails. -/
def kurtzFluidLimit (f : ι → (Fin d → ℝ) → ℝ) (v : ι → Fin d → ℝ) (x0 : Fin d → ℝ) :
    ℝ≥0 → Fin d → ℝ :=
  fun t => kurtzFluidPath f v x0 t

theorem kurtzFluidPath_spec (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) (x0 : Fin d → ℝ) :
    Continuous (kurtzFluidPath f v x0) ∧ ∀ t, 0 ≤ t →
      kurtzFluidPath f v x0 t = x0 + ∫ s in (0 : ℝ)..t, tcDrift f v (kurtzFluidPath f v x0 s) :=
  Classical.epsilon_spec (exists_fluid_solution heps hM hf0 hfB h319 x0)

theorem continuous_kurtzFluidLimit (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) (x0 : Fin d → ℝ) :
    Continuous (kurtzFluidLimit f v x0) :=
  (kurtzFluidPath_spec heps hM hf0 hfB h319 x0).1.comp NNReal.continuous_coe

/-- The integral equation of the fluid limit, in the `ℝ≥0`-indexed form. -/
theorem kurtzFluidLimit_eq (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) (x0 : Fin d → ℝ) (t : ℝ≥0) :
    kurtzFluidLimit f v x0 t = x0 + ∫ s in (0 : ℝ)..(t : ℝ),
      tcDrift f v (kurtzFluidLimit f v x0 s.toNNReal) := by
  unfold kurtzFluidLimit
  rw [(kurtzFluidPath_spec heps hM hf0 hfB h319 x0).2 t t.coe_nonneg]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le t.coe_nonneg] at hs
  simp only [Real.coe_toNNReal s hs.1]

/-- Uniqueness: a continuous `ℝ≥0`-indexed solution is the fluid limit. -/
theorem eq_kurtzFluidLimit_of_continuous (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) {x0 : Fin d → ℝ}
    {Y : ℝ≥0 → Fin d → ℝ} (hYc : Continuous Y)
    (hY : ∀ t : ℝ≥0, Y t = x0 + ∫ s in (0 : ℝ)..(t : ℝ), tcDrift f v (Y s.toNNReal)) :
    Y = kurtzFluidLimit f v x0 := by
  have hspec := kurtzFluidPath_spec (v := v) heps hM hf0 hfB h319 x0
  funext t
  have h := fluid_solution_unique_Icc heps hM h319 t.coe_nonneg (Y := fun s => Y s.toNNReal)
    (hYc.comp continuous_real_toNNReal) hspec.1
    (fun s hs => by
      dsimp only
      rw [hY s.toNNReal, Real.coe_toNNReal s hs.1])
    (fun s hs => hspec.2 s hs.1) t ⟨t.coe_nonneg, le_rfl⟩
  simpa only [Real.toNNReal_coe] using h

end Fluid

section Tail

attribute [local instance] channelBrownian_isFilteredPreBrownian_augmented

variable {m d : ℕ} {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
  {M : ℝ}

/-- **The `U_N` tail around the fluid limit.** `sectionFour_U_tail_kurtz` with
`X = kurtzFluidLimit f v x₀`: for every `N ≥ 2` and `r ≥ 0`,
`P (r < U_N) ≤ a_U exp (-b_U r²)` with `a_U = 2 max (1, d)` and `b_U = 1 / (2 e^{2 L T} Q)`. -/
theorem sectionFour_U_tail_kurtz_fluid (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    {T : ℝ≥0} {Q : ℝ} (hQ : sectionFourQZero v eps T ≤ Q) (hQpos : 0 < Q)
    {x0 : Fin d → ℝ} {Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZa : ∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t))
    (hSDE : ∀ N, 2 ≤ N → ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      KMTTransfer.KurtzSDEPathsNN N f v T (Z N) (channelRateIntegral T N f (Z N))
        (fun _ => x0) ω) :
    ∀ N, 2 ≤ N → ∀ r : ℝ, 0 ≤ r →
      channelKMTMeasure (Fin m)
          {ω | r < sectionFourRemainderU N (kurtzFluidLimit f v x0) (Z N) T ω} ≤
        ENNReal.ofReal (sectionFourAU d *
          Real.exp (-sectionFourBU (Real.exp (kurtzDriftLip v eps M * T)) Q * r ^ 2)) :=
  sectionFour_U_tail_kurtz heps hM hf0 hfB h319 hQ hQpos
    (continuous_kurtzFluidLimit heps hM hf0 hfB h319 x0)
    (fun t _ => kurtzFluidLimit_eq heps hM hf0 hfB h319 x0 t) hZa hSDE

end Tail

end Ripple.Kurtz.StrongApprox

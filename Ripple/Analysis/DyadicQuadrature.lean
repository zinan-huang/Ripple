import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Ripple.Analysis.BVQuadrature

/-!
# Uniform left endpoint quadrature

Left endpoint sums with equal subintervals, with an explicit Lipschitz error
bound. Only regularity on the interval is used.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval BigOperators NNReal

namespace Ripple.Analysis.DyadicQuadrature

/-- Left endpoint sum with `n` equal subintervals. -/
def leftSum (f : ℝ → ℝ) (H : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, f ((k : ℝ) * (H / n)) * (H / n)

/-- A Lipschitz integrand has quadrature error at most `K * H * mesh`. -/
theorem norm_leftSum_sub_integral_le
    {f : ℝ → ℝ} {H : ℝ} {K : ℝ≥0} (hH : 0 ≤ H)
    (hf : LipschitzOnWith K f (Icc 0 H)) {n : ℕ} (hn : 0 < n) :
    ‖leftSum f H n - ∫ s in (0 : ℝ)..H, f s‖ ≤ (K : ℝ) * H * (H / n) := by
  let δ : ℝ := H / n
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 ≤ δ := div_nonneg hH hnreal.le
  have hnδ : (n : ℝ) * δ = H := by dsimp [δ]; field_simp
  have hnode (k : ℕ) (hk : k ≤ n) : (k : ℝ) * δ ∈ Icc 0 H := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hδ, ?_⟩
    calc
      (k : ℝ) * δ ≤ (n : ℝ) * δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hδ
      _ = H := hnδ
  have horder (k : ℕ) : (k : ℝ) * δ ≤ ((k + 1 : ℕ) : ℝ) * δ := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hδ
  have hcell (k : ℕ) (hk : k < n) :
      IntervalIntegrable f volume ((k : ℝ) * δ) (((k + 1 : ℕ) : ℝ) * δ) := by
    exact (hf.continuousOn.mono
      (uIcc_subset_Icc (hnode k hk.le) (hnode (k + 1) hk))).intervalIntegrable
  have htel : (∑ k ∈ Finset.range n,
      ∫ s in (k : ℝ) * δ..((k + 1 : ℕ) : ℝ) * δ, f s) =
      ∫ s in (0 : ℝ)..H, f s := by
    simpa [hnδ] using intervalIntegral.sum_integral_adjacent_intervals hcell
  have herror (k : ℕ) (hk : k < n) :
      ‖f ((k : ℝ) * δ) * δ -
        ∫ s in (k : ℝ) * δ..((k + 1 : ℕ) : ℝ) * δ, f s‖ ≤
        (K : ℝ) * δ * δ := by
    have hwidth : ((k + 1 : ℕ) : ℝ) * δ - (k : ℝ) * δ = δ := by push_cast; ring
    have heq : f ((k : ℝ) * δ) * δ -
        (∫ s in (k : ℝ) * δ..((k + 1 : ℕ) : ℝ) * δ, f s) =
        ∫ s in (k : ℝ) * δ..((k + 1 : ℕ) : ℝ) * δ, f ((k : ℝ) * δ) - f s := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hcell k hk),
        intervalIntegral.integral_const, hwidth]
      simp only [smul_eq_mul]
      ring
    rw [heq]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (k : ℝ) * δ) (b := ((k + 1 : ℕ) : ℝ) * δ)
      (C := (K : ℝ) * δ) (f := fun s => f ((k : ℝ) * δ) - f s)
      (fun s hs => by
        rw [uIoc_of_le (horder k)] at hs
        have hsH : s ∈ Icc 0 H :=
          ⟨(hnode k hk.le).1.trans hs.1.le, hs.2.trans (hnode (k + 1) hk).2⟩
        have hdist : ‖(k : ℝ) * δ - s‖ ≤ δ := by
          rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hs.1])]
          linarith [hs.2, hwidth]
        exact (hf.norm_sub_le (hnode k hk.le) hsH).trans
          (mul_le_mul_of_nonneg_left hdist K.coe_nonneg))
    have hwidth' : ((k : ℝ) + 1) * δ - (k : ℝ) * δ = δ := by ring
    simpa [hwidth, hwidth', abs_of_nonneg hδ] using hb
  calc
    ‖leftSum f H n - ∫ s in (0 : ℝ)..H, f s‖ =
        ‖∑ k ∈ Finset.range n, (f ((k : ℝ) * δ) * δ -
          ∫ s in (k : ℝ) * δ..((k + 1 : ℕ) : ℝ) * δ, f s)‖ := by
      rw [Finset.sum_sub_distrib, htel]
      rfl
    _ ≤ ∑ k ∈ Finset.range n, ‖f ((k : ℝ) * δ) * δ -
          ∫ s in (k : ℝ) * δ..((k + 1 : ℕ) : ℝ) * δ, f s‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, (K : ℝ) * δ * δ := by
      exact Finset.sum_le_sum fun k hk => herror k (Finset.mem_range.mp hk)
    _ = (K : ℝ) * H * (H / n) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      change (n : ℝ) * ((K : ℝ) * δ * δ) = (K : ℝ) * H * δ
      calc
        (n : ℝ) * ((K : ℝ) * δ * δ) = (K : ℝ) * ((n : ℝ) * δ) * δ := by ring
        _ = (K : ℝ) * H * δ := by rw [hnδ]

/-- Squaring a bounded Lipschitz function preserves interval Lipschitz regularity. -/
theorem lipschitzOnWith_sq
    {a : ℝ → ℝ} {H : ℝ} {L : ℝ≥0} (ha : LipschitzOnWith L a (Icc 0 H))
    {M : ℝ≥0} (hM : ∀ t ∈ Icc 0 H, ‖a t‖ ≤ M) :
    LipschitzOnWith (2 * M * L) (fun t => a t ^ 2) (Icc 0 H) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq]
  have hdiff := ha.dist_le_mul x hx y hy
  rw [Real.dist_eq, Real.dist_eq] at hdiff
  have hsum : |a x + a y| ≤ 2 * (M : ℝ) := by
    exact (abs_add_le _ _).trans (by simpa [Real.norm_eq_abs, two_mul] using add_le_add (hM x hx) (hM y hy))
  calc
    |a x ^ 2 - a y ^ 2| = |a x - a y| * |a x + a y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ ((L : ℝ) * |x - y|) * (2 * (M : ℝ)) :=
      mul_le_mul hdiff hsum (abs_nonneg _) (by positivity)
    _ = ((2 * M * L : ℝ≥0) : ℝ) * |x - y| := by push_cast; ring

/-- Dyadic left endpoint sums converge to the integral of the squared coefficient.
Only Lipschitz regularity on `[0,H]` is required. -/
theorem tendsto_dyadic_variance
    {a : ℝ → ℝ} {H : ℝ} {L : ℝ≥0}
    (ha : LipschitzOnWith L a (Icc 0 H)) (hH : 0 ≤ H) :
    Tendsto (fun m : ℕ => ∑ k : Fin (2 ^ m),
      a (H * (k : ℝ) / ((2 : ℝ) ^ m)) ^ 2 * (H / ((2 : ℝ) ^ m)))
      atTop (𝓝 (∫ s in (0 : ℝ)..H, a s ^ 2)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuousOn
  have hMnonneg : 0 ≤ M := (norm_nonneg (a 0)).trans (hM 0 ⟨le_rfl, hH⟩)
  let Mn : ℝ≥0 := ⟨M, hMnonneg⟩
  let K : ℝ≥0 := 2 * Mn * L
  have hsq : LipschitzOnWith K (fun t => a t ^ 2) (Icc 0 H) := lipschitzOnWith_sq (M := Mn) ha hM
  have hzero : Tendsto (fun m : ℕ => (K : ℝ) * H * (H / ((2 : ℝ) ^ m))) atTop (𝓝 0) := by
    have hp : Tendsto (fun m : ℕ => (2 : ℝ) ^ m) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hdiv : Tendsto (fun m : ℕ => H / ((2 : ℝ) ^ m)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hp
    simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (K : ℝ) * H) atTop (𝓝 ((K : ℝ) * H))).mul hdiv
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hzero.eventually (gt_mem_nhds hε)] with m hm
  have he := norm_leftSum_sub_integral_le (n := 2 ^ m) hH hsq
    (pow_pos (by norm_num : 0 < (2 : ℕ)) m)
  have hsum : (∑ k : Fin (2 ^ m),
      a (H * (k : ℝ) / ((2 : ℝ) ^ m)) ^ 2 * (H / ((2 : ℝ) ^ m))) =
      leftSum (fun t => a t ^ 2) H (2 ^ m) := by
    rw [leftSum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    congr 2
    ring
  rw [dist_eq_norm, hsum]
  exact lt_of_le_of_lt he (by simpa using hm)

/-- Cell estimate with the Lipschitz constant measured only on the ambient interval. -/
theorem norm_cell_error_le
    {f : ℝ → ℝ} {H x y : ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc 0 H))
    (hx : x ∈ Icc 0 H) (hy : y ∈ Icc 0 H) (hxy : x ≤ y) :
    ‖f x * (y - x) - ∫ s in x..y, f s‖ ≤ (K : ℝ) * (y - x) * (y - x) := by
  have hi : IntervalIntegrable f volume x y :=
    (hf.continuousOn.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  have heq : f x * (y - x) - (∫ s in x..y, f s) = ∫ s in x..y, f x - f s := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := x) (b := y) (C := (K : ℝ) * (y - x)) (f := fun s => f x - f s)
    (fun s hs => by
      rw [uIoc_of_le hxy] at hs
      have hsH : s ∈ Icc 0 H := ⟨hx.1.trans hs.1.le, hs.2.trans hy.2⟩
      have hdist : ‖x - s‖ ≤ y - x := by
        rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hs.1])]
        linarith [hs.2]
      exact (hf.norm_sub_le hx hsH).trans
        (mul_le_mul_of_nonneg_left hdist K.coe_nonneg))
  simpa [abs_of_nonneg (sub_nonneg.mpr hxy)] using hb

/-- Cutoff left endpoint quadrature; the entire cell is included when its left endpoint is
strictly before the cutoff time. -/
def cutoffLeftSum (f : ℝ → ℝ) (H t : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, if (k : ℝ) * (H / n) < t then f ((k : ℝ) * (H / n)) * (H / n) else 0

/-- The unique cell crossing the cutoff time costs at most two sup bounds times the mesh. -/
theorem norm_cutoffLeftSum_sub_integral_le
    {f : ℝ → ℝ} {H t M : ℝ} {K : ℝ≥0}
    (ht : t ∈ Icc 0 H) (hf : LipschitzOnWith K f (Icc 0 H))
    (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc 0 H, ‖f s‖ ≤ M)
    {n : ℕ} (hn : 0 < n) :
    ‖cutoffLeftSum f H t n - ∫ s in (0 : ℝ)..t, f s‖ ≤
      ((K : ℝ) * H + 2 * M) * (H / n) := by
  classical
  let δ : ℝ := H / n
  let p : ℕ → ℝ := fun k => (k : ℝ) * δ
  let q : ℕ → ℝ := fun k => min (p k) t
  let cross : ℕ → Prop := fun k => p k < t ∧ t < p (k + 1)
  have hH : 0 ≤ H := ht.1.trans ht.2
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 ≤ δ := div_nonneg hH hnreal.le
  have hpn : p n = H := by dsimp [p, δ]; field_simp
  have hp : Monotone p := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδ
  have hpmem (k : ℕ) (hk : k ≤ n) : p k ∈ Icc 0 H :=
    ⟨mul_nonneg (Nat.cast_nonneg _) hδ, (hp hk).trans_eq hpn⟩
  have hqmem (k : ℕ) (hk : k ≤ n) : q k ∈ Icc 0 H :=
    ⟨le_min (hpmem k hk).1 ht.1, (min_le_right _ _).trans ht.2⟩
  have hq : Monotone q := fun i j hij => min_le_min (hp hij) le_rfl
  have hwidth (k : ℕ) : p (k + 1) - p k = δ := by dsimp [p]; push_cast; ring
  have hi (k : ℕ) (hk : k < n) : IntervalIntegrable f volume (q k) (q (k + 1)) :=
    (hf.continuousOn.mono (uIcc_subset_Icc (hqmem k hk.le) (hqmem (k + 1) hk))).intervalIntegrable
  have htel : (∑ k ∈ Finset.range n, ∫ s in q k..q (k + 1), f s) =
      ∫ s in (0 : ℝ)..t, f s := by
    have hqzero : q 0 = 0 := by simp [q, p, ht.1]
    have hqn : q n = t := by dsimp [q]; rw [hpn, min_eq_right ht.2]
    simpa [hqzero, hqn] using intervalIntegral.sum_integral_adjacent_intervals hi
  have hcrossSum : (∑ k ∈ Finset.range n, if cross k then 2 * M * δ else 0) ≤ 2 * M * δ := by
    by_cases hex : ∃ j ∈ Finset.range n, cross j
    · obtain ⟨j, hj, hcj⟩ := hex
      rw [Finset.sum_eq_single j]
      · simp [hcj]
      · intro k hk hkj
        have hkc : ¬cross k := by
          intro hck
          exact hkj (BVIntegrationByParts.crossing_unique hp hck hcj)
        simp [hkc]
      · simp [hj]
    · have hnone : ∀ k ∈ Finset.range n, ¬cross k := by
        intro k hk hck
        exact hex ⟨k, hk, hck⟩
      have hz : (∑ k ∈ Finset.range n, if cross k then 2 * M * δ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp [hnone k hk]
      rw [hz]
      positivity
  have herror (k : ℕ) (hk : k < n) :
      ‖(if p k < t then f (p k) * δ else 0) - ∫ s in q k..q (k + 1), f s‖ ≤
        (K : ℝ) * δ * δ + if cross k then 2 * M * δ else 0 := by
    by_cases hbefore : p k < t
    · rw [if_pos hbefore]
      by_cases hafter : t < p (k + 1)
      · have hqk : q k = p k := min_eq_left hbefore.le
        have hqnext : q (k + 1) = t := min_eq_right hafter.le
        have hb : ‖∫ s in p k..t, f s‖ ≤ M * (t - p k) := by
          have h := intervalIntegral.norm_integral_le_of_norm_le_const
            (a := p k) (b := t) (C := M) (f := f)
            (fun s hs => by
              rw [uIoc_of_le hbefore.le] at hs
              exact hbound s ⟨(hpmem k hk.le).1.trans hs.1.le, hs.2.trans ht.2⟩)
          simpa [abs_of_nonneg (sub_nonneg.mpr hbefore.le)] using h
        rw [hqk, hqnext, if_pos (show cross k from ⟨hbefore, hafter⟩)]
        have hfpk := hbound (p k) (hpmem k hk.le)
        have htd : t - p k ≤ δ := by linarith [hwidth k]
        calc
          ‖f (p k) * δ - ∫ s in p k..t, f s‖ ≤ ‖f (p k) * δ‖ + ‖∫ s in p k..t, f s‖ := norm_sub_le _ _
          _ ≤ M * δ + M * δ := by
            apply add_le_add
            · simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg hδ] using
                mul_le_mul_of_nonneg_right hfpk hδ
            · exact hb.trans (mul_le_mul_of_nonneg_left htd hM)
          _ ≤ (K : ℝ) * δ * δ + 2 * M * δ := by nlinarith [mul_nonneg (mul_nonneg K.coe_nonneg hδ) hδ]
      · have hqk : q k = p k := min_eq_left hbefore.le
        have hqnext : q (k + 1) = p (k + 1) := min_eq_left (le_of_not_gt hafter)
        rw [hqk, hqnext, if_neg (show ¬cross k from fun h => hafter h.2)]
        simpa only [hwidth, add_zero] using norm_cell_error_le hf (hpmem k hk.le) (hpmem (k + 1) hk)
          (hp (Nat.le_succ k))
    · have hqk : q k = t := min_eq_right (le_of_not_gt hbefore)
      have hqnext : q (k + 1) = t := min_eq_right ((le_of_not_gt hbefore).trans (hp (Nat.le_succ k)))
      rw [if_neg hbefore, hqk, hqnext, intervalIntegral.integral_same, sub_zero, norm_zero,
        if_neg (show ¬cross k from fun h => hbefore h.1)]
      positivity
  calc
    ‖cutoffLeftSum f H t n - ∫ s in (0 : ℝ)..t, f s‖ =
      ‖∑ k ∈ Finset.range n,
        ((if p k < t then f (p k) * δ else 0) - ∫ s in q k..q (k + 1), f s)‖ := by
      rw [Finset.sum_sub_distrib, htel]
      rfl
    _ ≤ ∑ k ∈ Finset.range n,
      ‖(if p k < t then f (p k) * δ else 0) - ∫ s in q k..q (k + 1), f s‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n,
        ((K : ℝ) * δ * δ + if cross k then 2 * M * δ else 0) :=
      Finset.sum_le_sum fun k hk => herror k (Finset.mem_range.mp hk)
    _ ≤ (n : ℝ) * ((K : ℝ) * δ * δ) + 2 * M * δ := by
      rw [Finset.sum_add_distrib]
      simpa using add_le_add_left hcrossSum ((n : ℝ) * ((K : ℝ) * δ * δ))
    _ = ((K : ℝ) * H + 2 * M) * (H / n) := by
      change (n : ℝ) * ((K : ℝ) * δ * δ) + 2 * M * δ = ((K : ℝ) * H + 2 * M) * δ
      calc
        _ = ((K : ℝ) * ((n : ℝ) * δ) + 2 * M) * δ := by ring
        _ = _ := by rw [show (n : ℝ) * δ = H from hpn]

/-- Cutoff quadrature on a fixed interval converges to the integral up to any cutoff time. -/
theorem tendsto_cutoffLeftSum
    {f : ℝ → ℝ} {H t M : ℝ} {K : ℝ≥0}
    (ht : t ∈ Icc 0 H) (hf : LipschitzOnWith K f (Icc 0 H))
    (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc 0 H, ‖f s‖ ≤ M) :
    Tendsto (fun m : ℕ => cutoffLeftSum f H t (2 ^ m)) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, f s)) := by
  have hp : Tendsto (fun m : ℕ => (2 : ℝ) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hdiv : Tendsto (fun m : ℕ => H / ((2 : ℝ) ^ m)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hp
  have hzero : Tendsto (fun m : ℕ => ((K : ℝ) * H + 2 * M) * (H / ((2 : ℝ) ^ m)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (K : ℝ) * H + 2 * M) atTop (𝓝 ((K : ℝ) * H + 2 * M))).mul hdiv
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hzero.eventually (gt_mem_nhds hε)] with m hm
  rw [dist_eq_norm]
  exact lt_of_le_of_lt
    (norm_cutoffLeftSum_sub_integral_le (n := 2 ^ m) ht hf hM hbound
      (pow_pos (by norm_num : 0 < (2 : ℕ)) m)) (by simpa using hm)

/-- The variance sum on the fixed Brownian grid of `[0,H]`, cut off by the strict left endpoint
condition at `t`, converges to the variance integral on `[0,t]`. -/
theorem tendsto_cutoff_dyadic_variance
    {a : ℝ → ℝ} {H t : ℝ} {L : ℝ≥0}
    (ha : LipschitzOnWith L a (Icc 0 H)) (ht : t ∈ Icc 0 H) :
    Tendsto (fun m : ℕ => ∑ k : Fin (2 ^ m),
      (if H * (k : ℝ) / ((2 : ℝ) ^ m) < t then
        a (H * (k : ℝ) / ((2 : ℝ) ^ m)) ^ 2 else 0) * (H / ((2 : ℝ) ^ m)))
      atTop (𝓝 (∫ s in (0 : ℝ)..t, a s ^ 2)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuousOn
  have hMnonneg : 0 ≤ M := (norm_nonneg (a 0)).trans (hM 0 ⟨le_rfl, ht.1.trans ht.2⟩)
  let Mn : ℝ≥0 := ⟨M, hMnonneg⟩
  let K : ℝ≥0 := 2 * Mn * L
  have hsq : LipschitzOnWith K (fun s => a s ^ 2) (Icc 0 H) :=
    lipschitzOnWith_sq (M := Mn) ha hM
  have hsquare : ∀ s ∈ Icc 0 H, ‖a s ^ 2‖ ≤ M ^ 2 := by
    intro s hs
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM s hs) 2
  have h := tendsto_cutoffLeftSum ht hsq (sq_nonneg M) hsquare
  have heq (m : ℕ) : (∑ k : Fin (2 ^ m),
      (if H * (k : ℝ) / ((2 : ℝ) ^ m) < t then
        a (H * (k : ℝ) / ((2 : ℝ) ^ m)) ^ 2 else 0) * (H / ((2 : ℝ) ^ m))) =
      cutoffLeftSum (fun s => a s ^ 2) H t (2 ^ m) := by
    rw [cutoffLeftSum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    have hnode : H * (k : ℝ) / ((2 : ℝ) ^ m) = (k : ℝ) * (H / ((2 : ℝ) ^ m)) := by ring
    rw [hnode]
    split_ifs <;> simp_all
  exact h.congr' (Eventually.of_forall fun m => (heq m).symm)

end Ripple.Analysis.DyadicQuadrature

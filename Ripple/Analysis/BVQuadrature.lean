import Ripple.Analysis.BVIntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
Left endpoint sums converge to the integration-by-parts functional. The
coefficient increment on each cell is the integral of its derivative by the
fundamental theorem for absolutely continuous functions. Discrete summation by
parts then leaves an error bounded by the oscillation of the continuous path
on a cell times the Lipschitz constant times the interval length.
-/

open Set MeasureTheory Filter
open scoped Topology Interval NNReal

namespace Ripple.Analysis.BVIntegrationByParts

/-- Left endpoint sums over the first `n` cells of a partition. -/
noncomputable def leftSum (a w : ℝ → ℝ) (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, a (p i) * (w (p (i + 1)) - w (p i))

/-- A Lipschitz coefficient is absolutely continuous on its interval. -/
theorem coefficient_absolutelyContinuous {a : ℝ → ℝ} {u v : ℝ} {K : ℝ≥0}
    (huv : u ≤ v) (ha : LipschitzOnWith K a (Icc u v)) :
    AbsolutelyContinuousOnInterval a u v := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le huv] using ha

/-- The derivative has exactly the required coefficient increment on every cell. -/
theorem integral_deriv_eq_increment {a : ℝ → ℝ} {u v : ℝ} {K : ℝ≥0}
    (huv : u ≤ v) (ha : LipschitzOnWith K a (Icc u v)) :
    ∫ s in u..v, deriv a s = a v - a u :=
  (coefficient_absolutelyContinuous huv ha).integral_deriv_eq_sub

/-- Algebraic summation by parts, using right endpoints for the coefficient
increments in the remainder. -/
theorem leftSum_eq_boundary_sub (a w : ℝ → ℝ) (p : ℕ → ℝ) (n : ℕ) :
    leftSum a w p n = a (p n) * w (p n) - a (p 0) * w (p 0) -
      ∑ i ∈ Finset.range n, w (p (i + 1)) * (a (p (i + 1)) - a (p i)) := by
  induction n with
  | zero => simp [leftSum]
  | succ n ih =>
    simp only [leftSum] at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- Local derivative-weighted integral estimate on an arbitrary cell. -/
theorem abs_integral_mul_deriv_le_interval {a f : ℝ → ℝ} {u v M : ℝ} {K : ℝ≥0}
    (huv : u ≤ v) (ha : LipschitzOnWith K a (Icc u v))
    (hM : 0 ≤ M) (hf : ∀ s ∈ Icc u v, |f s| ≤ M) :
    |∫ s in u..v, f s * deriv a s| ≤ M * (K : ℝ) * (v - u) := by
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := ae_iff.mpr (by simp)
  have hb : ∀ᵐ s : ℝ ∂volume, s ∈ Ι u v →
      ‖f s * deriv a s‖ ≤ M * (K : ℝ) := by
    filter_upwards [hne] with s hsv hs
    have hs' : s ∈ Ioc u v := by simpa only [uIoc_of_le huv] using hs
    have hd : ‖deriv a s‖ ≤ (K : ℝ) :=
      norm_deriv_le_of_lipschitzOn
        (Icc_mem_nhds hs'.1 (lt_of_le_of_ne hs'.2 hsv)) ha
    rw [norm_mul, Real.norm_eq_abs (f s)]
    exact mul_le_mul (hf s ⟨hs'.1.le, hs'.2⟩) hd (norm_nonneg _) hM
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] using
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hb

/-- The exact error identity behind the convergence theorem. -/
theorem leftSum_sub_J_eq_sum_integral {a w : ℝ → ℝ} {T : ℝ} {K : ℝ≥0}
    {p : ℕ → ℝ} {n : ℕ}
    (ha : LipschitzOnWith K a (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hwzero : w 0 = 0) (hp : Monotone p) (hpzero : p 0 = 0) (hpn : p n = T) :
    leftSum a w p n - J a w T =
      ∑ i ∈ Finset.range n,
        ∫ s in p i..p (i + 1), (w s - w (p (i + 1))) * deriv a s := by
  have hsub (i : ℕ) (hi : i < n) : Icc (p i) (p (i + 1)) ⊆ Icc 0 T := by
    intro s hs
    constructor
    · calc
        0 = p 0 := hpzero.symm
        _ ≤ p i := hp (Nat.zero_le _)
        _ ≤ s := hs.1
    · calc
        s ≤ p (i + 1) := hs.2
        _ ≤ p n := hp (Nat.succ_le_of_lt hi)
        _ = T := hpn
  have hac (i : ℕ) (hi : i < n) : AbsolutelyContinuousOnInterval a (p i) (p (i + 1)) :=
    coefficient_absolutelyContinuous (hp (Nat.le_succ i)) (ha.mono (hsub i hi))
  have hiw (i : ℕ) (hi : i < n) :
      IntervalIntegrable (fun s => w s * deriv a s) volume (p i) (p (i + 1)) := by
    apply (hac i hi).intervalIntegrable_deriv.continuousOn_mul
    simpa only [uIcc_of_le (hp (Nat.le_succ i))] using hw.mono (hsub i hi)
  have hcell (i : ℕ) (hi : i < n) :
      (∫ s in p i..p (i + 1), (w s - w (p (i + 1))) * deriv a s) =
        (∫ s in p i..p (i + 1), w s * deriv a s) -
          w (p (i + 1)) * (a (p (i + 1)) - a (p i)) := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (hiw i hi)
      ((hac i hi).intervalIntegrable_deriv.const_mul _),
      intervalIntegral.integral_const_mul, (hac i hi).integral_deriv_eq_sub]
  have hsum : (∑ i ∈ Finset.range n, ∫ s in p i..p (i + 1), w s * deriv a s) =
      ∫ s in 0..T, w s * deriv a s := by
    simpa only [hpzero, hpn] using intervalIntegral.sum_integral_adjacent_intervals hiw
  have herr : (∑ i ∈ Finset.range n,
      ∫ s in p i..p (i + 1), (w s - w (p (i + 1))) * deriv a s) =
        (∫ s in 0..T, w s * deriv a s) -
          ∑ i ∈ Finset.range n, w (p (i + 1)) * (a (p (i + 1)) - a (p i)) := by
    calc
      _ = ∑ i ∈ Finset.range n, ((∫ s in p i..p (i + 1), w s * deriv a s) -
          w (p (i + 1)) * (a (p (i + 1)) - a (p i))) :=
        Finset.sum_congr rfl (fun i hi => hcell i (Finset.mem_range.mp hi))
      _ = _ := by rw [Finset.sum_sub_distrib, hsum]
  rw [herr, leftSum_eq_boundary_sub, hpzero, hpn, hwzero]
  simp only [J, mul_zero]
  ring

/-- Quantitative quadrature bound in terms of the path oscillation on each cell. -/
theorem abs_leftSum_sub_J_le {a w : ℝ → ℝ} {T M : ℝ} {K : ℝ≥0}
    {p : ℕ → ℝ} {n : ℕ}
    (ha : LipschitzOnWith K a (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hwzero : w 0 = 0) (hp : Monotone p) (hpzero : p 0 = 0) (hpn : p n = T)
    (hM : 0 ≤ M)
    (hosc : ∀ i < n, ∀ s ∈ Icc (p i) (p (i + 1)), |w s - w (p (i + 1))| ≤ M) :
    |leftSum a w p n - J a w T| ≤ M * (K : ℝ) * T := by
  rw [leftSum_sub_J_eq_sum_integral ha hw hwzero hp hpzero hpn]
  calc
    |∑ i ∈ Finset.range n, ∫ s in p i..p (i + 1), (w s - w (p (i + 1))) * deriv a s|
        ≤ ∑ i ∈ Finset.range n,
          |∫ s in p i..p (i + 1), (w s - w (p (i + 1))) * deriv a s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, M * (K : ℝ) * (p (i + 1) - p i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      apply abs_integral_mul_deriv_le_interval (hp (Nat.le_succ i)) _ hM (hosc i hin)
      apply ha.mono
      intro s hs
      constructor
      · calc
          0 = p 0 := hpzero.symm
          _ ≤ p i := hp (Nat.zero_le _)
          _ ≤ s := hs.1
      · calc
          s ≤ p (i + 1) := hs.2
          _ ≤ p n := hp (Nat.succ_le_of_lt hin)
          _ = T := hpn
    _ = M * (K : ℝ) * T := by
      rw [← Finset.mul_sum, Finset.sum_range_sub, hpzero, hpn, sub_zero]

/-- Any sequence of increasing partitions with mesh tending to zero gives the
integration-by-parts integral for a continuous zero-start path. -/
theorem leftSum_tendsto_J {a w : ℝ → ℝ} {T : ℝ} {K : ℝ≥0}
    {p : ℕ → ℕ → ℝ} {n : ℕ → ℕ} {mesh : ℕ → ℝ}
    (hT : 0 ≤ T) (ha : LipschitzOnWith K a (Icc 0 T))
    (hw : ContinuousOn w (Icc 0 T)) (hwzero : w 0 = 0)
    (hp : ∀ m, Monotone (p m)) (hpzero : ∀ m, p m 0 = 0)
    (hpn : ∀ m, p m (n m) = T)
    (hcell : ∀ m i, i < n m → p m (i + 1) - p m i ≤ mesh m)
    (hmesh : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun m => leftSum a w (p m) (n m)) atTop (𝓝 (J a w T)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / ((K : ℝ) * T + 1)
  have hden : 0 < (K : ℝ) * T + 1 := by positivity
  have hη : 0 < η := div_pos hε hden
  have hηeq : η * ((K : ℝ) * T + 1) = ε := by
    dsimp only [η]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hw) η hη
  filter_upwards [(tendsto_order.1 hmesh).2 δ hδ] with m hm
  have hb : |leftSum a w (p m) (n m) - J a w T| ≤ η * (K : ℝ) * T := by
    apply abs_leftSum_sub_J_le ha hw hwzero (hp m) (hpzero m) (hpn m) hη.le
    intro i hi s hs
    have hsall : s ∈ Icc 0 T := by
      constructor
      · calc
          0 = p m 0 := (hpzero m).symm
          _ ≤ p m i := hp m (Nat.zero_le _)
          _ ≤ s := hs.1
      · calc
          s ≤ p m (i + 1) := hs.2
          _ ≤ p m (n m) := hp m (Nat.succ_le_of_lt hi)
          _ = T := hpn m
    have hrall : p m (i + 1) ∈ Icc 0 T := by
      constructor
      · calc
          0 = p m 0 := (hpzero m).symm
          _ ≤ p m (i + 1) := hp m (Nat.zero_le _)
      · calc
          p m (i + 1) ≤ p m (n m) := hp m (Nat.succ_le_of_lt hi)
          _ = T := hpn m
    have hdist : dist s (p m (i + 1)) < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
      linarith [hcell m i hi, hs.1]
    simpa only [Real.dist_eq] using (huc s hsall (p m (i + 1)) hrall hdist).le
  rw [Real.dist_eq]
  exact hb.trans_lt (by nlinarith [hηeq])

/-- Dyadic left sums at the terminal time, in the same finite-index shape as
Brownian dyadic sums. -/
theorem dyadic_leftSum_tendsto_J {a w : ℝ → ℝ} {T : ℝ} {K : ℝ≥0}
    (hT : 0 ≤ T) (ha : LipschitzOnWith K a (Icc 0 T))
    (hw : ContinuousOn w (Icc 0 T)) (hwzero : w 0 = 0) :
    Tendsto (fun m => ∑ k : Fin (2 ^ m),
      a (T * k.val / (2 : ℝ) ^ m) *
        (w (T * (k.val + 1) / (2 : ℝ) ^ m) - w (T * k.val / (2 : ℝ) ^ m)))
      atTop (𝓝 (J a w T)) := by
  have hp (m : ℕ) : Monotone (fun k : ℕ => T * k / (2 : ℝ) ^ m) := by
    intro i j hij
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hT) (by positivity)
  have hpn (m : ℕ) : T * (↑(2 ^ m : ℕ) : ℝ) / (2 : ℝ) ^ m = T := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact mul_div_cancel_right₀ _ (by positivity)
  have hcell (m i : ℕ) :
      T * (↑(i + 1) : ℝ) / (2 : ℝ) ^ m - T * i / (2 : ℝ) ^ m = T / (2 : ℝ) ^ m := by
    push_cast
    ring
  have hmesh : Tendsto (fun m : ℕ => T / (2 : ℝ) ^ m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have h := leftSum_tendsto_J (p := fun m k => T * k / (2 : ℝ) ^ m)
    (n := fun m => 2 ^ m) (mesh := fun m => T / (2 : ℝ) ^ m)
    hT ha hw hwzero hp (fun _ => by simp) hpn (fun m i _ => (hcell m i).le) hmesh
  refine Tendsto.congr (fun m => ?_) h
  simp only [leftSum, Nat.cast_add, Nat.cast_one]
  exact (Fin.sum_univ_eq_sum_range (fun k : ℕ => a (T * (k : ℝ) / (2 : ℝ) ^ m) *
    (w (T * ((k : ℝ) + 1) / (2 : ℝ) ^ m) - w (T * (k : ℝ) / (2 : ℝ) ^ m))) (2 ^ m)).symm

/-- A monotone grid has at most one cell strictly crossing a fixed time. -/
theorem crossing_unique {p : ℕ → ℝ} (hp : Monotone p) {t : ℝ} {i j : ℕ}
    (hi : p i < t ∧ t < p (i + 1)) (hj : p j < t ∧ t < p (j + 1)) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hle := hp (Nat.succ_le_of_lt hij)
    linarith
  · have hle := hp (Nat.succ_le_of_lt hji)
    linarith

/-- Left sums on the original grid with coefficients cut off at time `t`. -/
noncomputable def cutoffLeftSum (a w : ℝ → ℝ) (p : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (if p i < t then a (p i) else 0) *
    (w (p (i + 1)) - w (p i))

/-- Only the crossing cell contributes to the difference between a cutoff
coefficient and a stopped grid. -/
theorem abs_cutoffLeftSum_sub_stopped_le {a w : ℝ → ℝ} {p : ℕ → ℝ}
    {n : ℕ} {t B η : ℝ} (hp : Monotone p) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (ha : ∀ i < n, p i < t → |a (p i)| ≤ B)
    (hw : ∀ i < n, p i < t ∧ t < p (i + 1) → |w (p (i + 1)) - w t| ≤ η) :
    |cutoffLeftSum a w p n t - leftSum a w (fun k => min (p k) t) n| ≤ B * η := by
  let e (i : ℕ) : ℝ := (if p i < t then a (p i) else 0) *
    (w (p (i + 1)) - w (p i)) -
      a (min (p i) t) * (w (min (p (i + 1)) t) - w (min (p i) t))
  have heq : cutoffLeftSum a w p n t - leftSum a w (fun k => min (p k) t) n =
      ∑ i ∈ Finset.range n, e i := by
    simp only [cutoffLeftSum, leftSum, e, Finset.sum_sub_distrib]
  have hezero (i : ℕ) (hi : ¬ (p i < t ∧ t < p (i + 1))) : e i = 0 := by
    by_cases hleft : p i < t
    · have hright : p (i + 1) ≤ t := le_of_not_gt (fun h => hi ⟨hleft, h⟩)
      simp only [e, if_pos hleft, min_eq_left hleft.le, min_eq_left hright, sub_self]
    · have hleft' : t ≤ p i := le_of_not_gt hleft
      have hright' : t ≤ p (i + 1) := hleft'.trans (hp (Nat.le_succ _))
      simp only [e, if_neg hleft, min_eq_right hleft', min_eq_right hright',
        zero_mul, sub_self, mul_zero]
  have hecross (i : ℕ) (hi : p i < t ∧ t < p (i + 1)) :
      e i = a (p i) * (w (p (i + 1)) - w t) := by
    simp only [e, if_pos hi.1, min_eq_left hi.1.le, min_eq_right hi.2.le]
    ring
  rw [heq]
  by_cases hex : ∃ i ∈ Finset.range n, p i < t ∧ t < p (i + 1)
  · obtain ⟨i, hin, hicross⟩ := hex
    rw [Finset.sum_eq_single i]
    · rw [hecross i hicross, abs_mul]
      exact mul_le_mul (ha i (Finset.mem_range.mp hin) hicross.1)
        (hw i (Finset.mem_range.mp hin) hicross) (abs_nonneg _) hB
    · intro j hj hji
      apply hezero
      intro hjcross
      exact hji (crossing_unique hp hjcross hicross)
    · intro hnot
      exact (hnot hin).elim
  · have hz : ∀ i ∈ Finset.range n, e i = 0 := by
      intro i hi
      apply hezero
      intro hicross
      exact hex ⟨i, hi, hicross⟩
    rw [Finset.sum_eq_zero hz, abs_zero]
    exact mul_nonneg hB hη

/-- Stopping a dyadic grid at an arbitrary time gives a convergent partition. -/
theorem dyadic_stopped_leftSum_tendsto_J {a w : ℝ → ℝ} {H t : ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 H)) (hw : ContinuousOn w (Icc 0 H))
    (hwzero : w 0 = 0) (ht : t ∈ Icc 0 H) :
    Tendsto (fun m => leftSum a w (fun k => min (H * k / (2 : ℝ) ^ m) t) (2 ^ m))
      atTop (𝓝 (J a w t)) := by
  have hH : 0 ≤ H := ht.1.trans ht.2
  have hp (m : ℕ) : Monotone (fun k : ℕ => H * k / (2 : ℝ) ^ m) := by
    intro i j hij
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hH) (by positivity)
  have hlast (m : ℕ) : H * (↑(2 ^ m : ℕ) : ℝ) / (2 : ℝ) ^ m = H := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact mul_div_cancel_right₀ _ (by positivity)
  have hcell (m i : ℕ) :
      H * (↑(i + 1) : ℝ) / (2 : ℝ) ^ m - H * i / (2 : ℝ) ^ m = H / (2 : ℝ) ^ m := by
    push_cast
    ring
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 H := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  apply leftSum_tendsto_J (mesh := fun m => H / (2 : ℝ) ^ m)
    ht.1 (ha.mono hsub) (hw.mono hsub) hwzero
  · intro m i j hij
    exact min_le_min (hp m hij) le_rfl
  · intro m
    simp only [Nat.cast_zero, mul_zero, zero_div, min_eq_left ht.1]
  · intro m
    rw [hlast, min_eq_right ht.2]
  · intro m i hi
    by_cases hleft : H * (i : ℝ) / (2 : ℝ) ^ m ≤ t
    · rw [min_eq_left hleft]
      calc
        min (H * (↑(i + 1) : ℝ) / (2 : ℝ) ^ m) t - H * i / (2 : ℝ) ^ m
            ≤ H * (↑(i + 1) : ℝ) / (2 : ℝ) ^ m - H * i / (2 : ℝ) ^ m :=
          sub_le_sub_right (min_le_left _ _) _
        _ = H / (2 : ℝ) ^ m := hcell m i
    · have hr : t ≤ H * (↑(i + 1) : ℝ) / (2 : ℝ) ^ m :=
        (lt_of_not_ge hleft).le.trans (hp m (Nat.le_succ _))
      rw [min_eq_right (lt_of_not_ge hleft).le, min_eq_right hr, sub_self]
      positivity
  · exact tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- The original dyadic increments with left coefficients cut off at `t`
converge to J at that time. The single cell straddling `t` has vanishing error. -/
theorem dyadic_cutoff_leftSum_tendsto_J {a w : ℝ → ℝ} {H t : ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 H)) (hw : ContinuousOn w (Icc 0 H))
    (hwzero : w 0 = 0) (ht : t ∈ Icc 0 H) :
    Tendsto (fun m => ∑ k : Fin (2 ^ m),
      (if H * k.val / (2 : ℝ) ^ m < t then a (H * k.val / (2 : ℝ) ^ m) else 0) *
        (w (H * (k.val + 1) / (2 : ℝ) ^ m) - w (H * k.val / (2 : ℝ) ^ m)))
      atTop (𝓝 (J a w t)) := by
  let p (m k : ℕ) : ℝ := H * k / (2 : ℝ) ^ m
  have hH : 0 ≤ H := ht.1.trans ht.2
  have hp (m : ℕ) : Monotone (p m) := by
    intro i j hij
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hH) (by positivity)
  have hpzero (m : ℕ) : p m 0 = 0 := by simp [p]
  have hlast (m : ℕ) : p m (2 ^ m) = H := by
    dsimp only [p]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact mul_div_cancel_right₀ _ (by positivity)
  have hcell (m i : ℕ) : p m (i + 1) - p m i = H / (2 : ℝ) ^ m := by
    dsimp only [p]
    push_cast
    ring
  have hpoint (m i : ℕ) (hi : i ≤ 2 ^ m) : p m i ∈ Icc 0 H := by
    constructor
    · calc
        0 = p m 0 := (hpzero m).symm
        _ ≤ p m i := hp m (Nat.zero_le _)
    · calc
        p m i ≤ p m (2 ^ m) := hp m hi
        _ = H := hlast m
  obtain ⟨C, hC⟩ : BddAbove ((fun s => |a s|) '' Icc 0 H) :=
    (isCompact_Icc.image_of_continuousOn ha.continuousOn.abs).bddAbove
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have habound (s : ℝ) (hs : s ∈ Icc 0 H) : |a s| ≤ B :=
    (hC (mem_image_of_mem _ hs)).trans (le_max_left _ _)
  have hmesh : Tendsto (fun m : ℕ => H / (2 : ℝ) ^ m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have herror : Tendsto (fun m => cutoffLeftSum a w (p m) (2 ^ m) t -
      leftSum a w (fun k => min (p m k) t) (2 ^ m)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let η : ℝ := ε / (B + 1)
    have hden : 0 < B + 1 := by linarith
    have hη : 0 < η := div_pos hε hden
    have hηeq : η * (B + 1) = ε := by
      dsimp only [η]
      exact div_mul_cancel₀ _ (ne_of_gt hden)
    obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hw) η hη
    filter_upwards [(tendsto_order.1 hmesh).2 δ hδ] with m hm
    have hb : |cutoffLeftSum a w (p m) (2 ^ m) t -
        leftSum a w (fun k => min (p m k) t) (2 ^ m)| ≤ B * η := by
      apply abs_cutoffLeftSum_sub_stopped_le (hp m) hB hη.le
      · intro i hi hit
        exact habound _ (hpoint m i (Nat.le_of_lt hi))
      · intro i hi hcross
        have hdist : dist (p m (i + 1)) t < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hcross.2.le)]
          linarith [hcell m i, hcross.1]
        simpa only [Real.dist_eq] using
          (huc (p m (i + 1)) (hpoint m (i + 1) (Nat.succ_le_of_lt hi)) t ht hdist).le
    rw [Real.dist_eq, sub_zero]
    exact hb.trans_lt (by nlinarith [hηeq])
  have hstop := dyadic_stopped_leftSum_tendsto_J ha hw hwzero ht
  have h := herror.add hstop
  have hfinal : Tendsto (fun m => cutoffLeftSum a w (p m) (2 ^ m) t)
      atTop (𝓝 (J a w t)) := by
    simpa only [p, sub_add_cancel, zero_add] using h
  refine Tendsto.congr (fun m => ?_) hfinal
  simp only [cutoffLeftSum, p, Nat.cast_add, Nat.cast_one]
  exact (Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    (if H * (k : ℝ) / (2 : ℝ) ^ m < t then a (H * (k : ℝ) / (2 : ℝ) ^ m) else 0) *
      (w (H * ((k : ℝ) + 1) / (2 : ℝ) ^ m) - w (H * (k : ℝ) / (2 : ℝ) ^ m))) (2 ^ m)).symm

end Ripple.Analysis.BVIntegrationByParts

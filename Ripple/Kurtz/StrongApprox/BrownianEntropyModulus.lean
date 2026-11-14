-- Ripple/Kurtz/StrongApprox/BrownianEntropyModulus.lean
import Mathlib
import Ripple.Kurtz.StrongApprox.GaussianBlockSum

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology

/-- Absolute modulus constant used by this file. -/
def brownianEntropyConstant : ℝ := 256

/-- Absolute tail prefactor in the all-`a ≥ 0` theorem. -/
def brownianEntropyTailConstant : ℝ := Real.exp 2

/-- Safe entropy core.  The diagonal is explicitly assigned value zero. -/
def brownianEntropyCore (H a h : ℝ) : ℝ :=
  if h = 0 then 0 else Real.sqrt (h * (Real.log (H / h) + a))

/-- The entropy modulus with explicit constant `256`. -/
def brownianEntropyBound (H a h : ℝ) : ℝ :=
  brownianEntropyConstant * brownianEntropyCore H a h +
    brownianEntropyConstant * (1 + a)

/-- Length of a level-`m` dyadic cell in `[0,H]`. -/
def brownianDyadicMesh (H : ℝ) (m : ℕ) : ℝ := H / (2 : ℝ) ^ m

/-- The `k`-th point of the level-`m` dyadic grid of `[0,H]`. -/
def brownianDyadicPoint (H : ℝ) (m k : ℕ) : ℝ :=
  H * k / (2 : ℝ) ^ m

/-- Cell threshold used in the chaining proof. -/
def brownianDyadicThreshold (H a : ℝ) (m : ℕ) : ℝ :=
  8 * Real.sqrt (brownianDyadicMesh H m * (a + m + 1))

/-- All adjacent increments on every dyadic level satisfy their threshold. -/
def BrownianDyadicCellControl
    (w : ℝ → ℝ) (H a : ℝ) : Prop :=
  ∀ m k : ℕ, k < 2 ^ m →
    |w (brownianDyadicPoint H m (k + 1)) -
      w (brownianDyadicPoint H m k)| ≤
      brownianDyadicThreshold H a m

private theorem dyadicMesh_pos {H : ℝ} (hH : 0 < H) (m : ℕ) :
    0 < brownianDyadicMesh H m := by
  unfold brownianDyadicMesh
  positivity

private theorem dyadicMesh_succ (H : ℝ) (m : ℕ) :
    brownianDyadicMesh H (m + 1) = brownianDyadicMesh H m / 2 := by
  unfold brownianDyadicMesh
  rw [pow_succ]
  ring

/-- Lower dyadic approximation of `u`. -/
def brownianDyadicIndex (H : ℝ) (m : ℕ) (u : ℝ) : ℕ :=
  Nat.floor (((2 : ℝ) ^ m * u) / H)

/-- Lower dyadic approximation as a point of `[0,H]`. -/
def brownianDyadicFloor (H : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  brownianDyadicPoint H m (brownianDyadicIndex H m u)

private theorem dyadicIndex_le_x
    {H u : ℝ} (hH : 0 < H) (hu0 : 0 ≤ u) (m : ℕ) :
    ((brownianDyadicIndex H m u : ℕ) : ℝ) ≤ ((2 : ℝ) ^ m * u) / H := by
  have hx0 : 0 ≤ ((2 : ℝ) ^ m * u) / H := by positivity
  exact Nat.floor_le hx0

private theorem dyadicIndex_lt_x
    {H u : ℝ} (m : ℕ) :
    ((2 : ℝ) ^ m * u) / H < ((brownianDyadicIndex H m u : ℕ) : ℝ) + 1 :=
  Nat.lt_floor_add_one _

private theorem dyadicFloor_index_le
    {H u : ℝ} (hH : 0 < H) (hu : u ∈ Icc (0 : ℝ) H) (m : ℕ) :
    brownianDyadicIndex H m u ≤ 2 ^ m := by
  have hu0 := hu.1
  have hf := dyadicIndex_le_x hH hu0 m
  have hxH : ((2 : ℝ) ^ m * u) / H ≤ (2 : ℝ) ^ m := by
    rw [div_le_iff₀ hH]
    nlinarith [hu.2, pow_pos (by norm_num : (0 : ℝ) < 2) m]
  have h2 : ((brownianDyadicIndex H m u : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    push_cast
    exact hf.trans hxH
  exact_mod_cast h2

private theorem dyadicFloor_le
    {H u : ℝ} (hH : 0 < H) (hu0 : 0 ≤ u) (m : ℕ) :
    brownianDyadicFloor H m u ≤ u := by
  have hf := dyadicIndex_le_x hH hu0 m
  have hp : (0 : ℝ) < (2 : ℝ) ^ m := pow_pos (by norm_num) _
  rw [le_div_iff₀ hH] at hf
  unfold brownianDyadicFloor brownianDyadicPoint
  rw [div_le_iff₀ hp]
  nlinarith

private theorem lt_dyadicFloor_add_mesh
    {H u : ℝ} (hH : 0 < H) (hu0 : 0 ≤ u) (m : ℕ) :
    u < brownianDyadicFloor H m u + brownianDyadicMesh H m := by
  have hf := dyadicIndex_lt_x (H := H) (u := u) m
  have hp : (0 : ℝ) < (2 : ℝ) ^ m := pow_pos (by norm_num) _
  rw [div_lt_iff₀ hH] at hf
  unfold brownianDyadicFloor brownianDyadicPoint brownianDyadicMesh
  rw [← add_div, lt_div_iff₀ hp]
  nlinarith

private theorem dyadicFloor_mem
    {H u : ℝ} (hH : 0 < H) (hu : u ∈ Icc (0 : ℝ) H) (m : ℕ) :
    brownianDyadicFloor H m u ∈ Icc (0 : ℝ) H := by
  constructor
  · unfold brownianDyadicFloor brownianDyadicPoint
    positivity
  · exact (dyadicFloor_le hH hu.1 m).trans hu.2

/-- A refinement either keeps the lower endpoint or moves one child cell right. -/
private theorem dyadicIndex_refine
    {H u : ℝ} (hH : 0 < H) (hu0 : 0 ≤ u) (m : ℕ) :
    brownianDyadicIndex H (m + 1) u = 2 * brownianDyadicIndex H m u ∨
      brownianDyadicIndex H (m + 1) u = 2 * brownianDyadicIndex H m u + 1 := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((2 : ℝ) ^ m * u) / H := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have htwo : ((2 : ℝ) ^ (m + 1) * u) / H = 2 * x := by
    rw [hx, pow_succ]
    ring
  have hlo : 2 * Nat.floor x ≤ Nat.floor (2 * x) := by
    apply Nat.le_floor
    have hf := Nat.floor_le hx0
    push_cast
    linarith
  have hhi : Nat.floor (2 * x) < 2 * Nat.floor x + 2 := by
    rw [Nat.floor_lt (mul_nonneg (by norm_num) hx0)]
    have hf := Nat.lt_floor_add_one x
    push_cast
    linarith
  unfold brownianDyadicIndex
  rw [htwo, ← hx]
  omega

private theorem dyadicFloor_refine_increment
    {H u : ℝ} (hH : 0 < H) (hu0 : 0 ≤ u) (huH : u ≤ H) (m : ℕ) :
    brownianDyadicFloor H (m + 1) u = brownianDyadicFloor H m u ∨
      ∃ k < 2 ^ (m + 1),
        brownianDyadicFloor H m u = brownianDyadicPoint H (m + 1) k ∧
        brownianDyadicFloor H (m + 1) u =
          brownianDyadicPoint H (m + 1) (k + 1) := by
  rcases dyadicIndex_refine hH hu0 m with hsame | hright
  · left
    unfold brownianDyadicFloor brownianDyadicPoint
    rw [hsame, pow_succ]
    push_cast
    field_simp
  · right
    have hk : 2 * brownianDyadicIndex H m u < 2 ^ (m + 1) := by
      have hindex : brownianDyadicIndex H m u ≤ 2 ^ m :=
        dyadicFloor_index_le hH ⟨hu0, huH⟩ m
      have hnext : brownianDyadicIndex H (m + 1) u ≤ 2 ^ (m + 1) :=
        dyadicFloor_index_le hH ⟨hu0, huH⟩ (m + 1)
      rw [hright, pow_succ] at hnext
      rw [pow_succ]
      omega
    refine ⟨2 * brownianDyadicIndex H m u, hk, ?_, ?_⟩
    · unfold brownianDyadicFloor brownianDyadicPoint
      rw [pow_succ]
      push_cast
      field_simp
    · unfold brownianDyadicFloor
      rw [hright]

private theorem dyadicFloor_tendsto
    {H u : ℝ} (hH : 0 < H) (hu0 : 0 ≤ u) :
    Tendsto (fun m => brownianDyadicFloor H m u) atTop (𝓝 u) := by
  have hmesh : Tendsto (fun m => brownianDyadicMesh H m) atTop (𝓝 0) := by
    have hhalf : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h := hhalf.const_mul H
    rw [mul_zero] at h
    refine h.congr fun m => ?_
    unfold brownianDyadicMesh
    rw [div_pow, one_pow]
    field_simp
  have hlow : Tendsto (fun m => u - brownianDyadicMesh H m) atTop (𝓝 (u - 0)) :=
    tendsto_const_nhds.sub hmesh
  rw [sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun m => ?_) (fun m => dyadicFloor_le hH hu0 m)
  have := lt_dyadicFloor_add_mesh hH hu0 m
  linarith

private theorem dyadicThreshold_nonneg
    {H a : ℝ} (hH : 0 ≤ H) (ha : 0 ≤ a) (m : ℕ) :
    0 ≤ brownianDyadicThreshold H a m := by
  unfold brownianDyadicThreshold brownianDyadicMesh
  positivity

/-- For `a ≥ 2`, thresholds decay geometrically by a factor at most `5/6`. -/
private theorem dyadicThreshold_succ_le
    {H a : ℝ} (hH : 0 ≤ H) (ha : 2 ≤ a) (m : ℕ) :
    brownianDyadicThreshold H a (m + 1) ≤
      (5 / 6 : ℝ) * brownianDyadicThreshold H a m := by
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hleft0 : 0 ≤ brownianDyadicMesh H (m + 1) * (a + (m + 1 : ℕ) + 1) := by
    apply mul_nonneg
    · unfold brownianDyadicMesh; positivity
    · push_cast; linarith
  have hright0 : 0 ≤ brownianDyadicMesh H m * (a + m + 1) := by
    apply mul_nonneg
    · unfold brownianDyadicMesh; positivity
    · linarith
  have hratio :
      brownianDyadicMesh H (m + 1) * (a + (m + 1 : ℕ) + 1) ≤
        (25 / 36 : ℝ) *
          (brownianDyadicMesh H m * (a + m + 1)) := by
    rw [dyadicMesh_succ]
    push_cast
    have hbase : 3 ≤ a + (m : ℝ) + 1 := by linarith
    nlinarith
  unfold brownianDyadicThreshold
  have hsqrt := Real.sqrt_le_sqrt hratio
  have h56 : Real.sqrt ((25 / 36 : ℝ) * (brownianDyadicMesh H m * (a + m + 1))) =
      5 / 6 * Real.sqrt (brownianDyadicMesh H m * (a + m + 1)) := by
    rw [Real.sqrt_mul (by norm_num), show (25 / 36 : ℝ) = (5 / 6) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [h56] at hsqrt
  linarith

private theorem dyadicThreshold_iterate_le
    {H a : ℝ} (hH : 0 ≤ H) (ha : 2 ≤ a) (m r : ℕ) :
    brownianDyadicThreshold H a (m + r) ≤
      (5 / 6 : ℝ) ^ r * brownianDyadicThreshold H a m := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.add_succ]
      calc
        brownianDyadicThreshold H a (m + r + 1) ≤
            (5 / 6 : ℝ) * brownianDyadicThreshold H a (m + r) :=
          dyadicThreshold_succ_le hH ha (m + r)
        _ ≤ (5 / 6 : ℝ) *
            ((5 / 6 : ℝ) ^ r * brownianDyadicThreshold H a m) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (5 / 6 : ℝ) ^ (r + 1) *
            brownianDyadicThreshold H a m := by ring

private theorem dyadicThreshold_tail_sum_le
    {H a : ℝ} (hH : 0 ≤ H) (ha : 2 ≤ a) (m r : ℕ) :
    ∑ j ∈ Finset.range r, brownianDyadicThreshold H a (m + j) ≤
      6 * brownianDyadicThreshold H a m := by
  have hgeo : Summable (fun j : ℕ => (5 / 6 : ℝ) ^ j) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  calc
    ∑ j ∈ Finset.range r, brownianDyadicThreshold H a (m + j) ≤
        ∑ j ∈ Finset.range r,
          (5 / 6 : ℝ) ^ j * brownianDyadicThreshold H a m := by
      exact Finset.sum_le_sum fun j _ => dyadicThreshold_iterate_le hH ha m j
    _ ≤ ∑' j : ℕ,
          (5 / 6 : ℝ) ^ j * brownianDyadicThreshold H a m := by
      exact Summable.sum_le_tsum _
        (fun j _ => mul_nonneg (by positivity)
          (dyadicThreshold_nonneg hH (by linarith) m))
        (hgeo.mul_right (brownianDyadicThreshold H a m))
    _ = 6 * brownianDyadicThreshold H a m := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring

private theorem path_to_floor_le
    {w : ℝ → ℝ} {H a u : ℝ}
    (hH : 0 < H) (ha : 2 ≤ a) (hu : u ∈ Icc (0 : ℝ) H)
    (hcont : Continuous w) (hcell : BrownianDyadicCellControl w H a)
    (m : ℕ) :
    |w u - w (brownianDyadicFloor H m u)| ≤
      6 * brownianDyadicThreshold H a (m + 1) := by
  have hfinite : ∀ r : ℕ,
      |w (brownianDyadicFloor H (m + r) u) -
        w (brownianDyadicFloor H m u)| ≤
      ∑ j ∈ Finset.range r,
        brownianDyadicThreshold H a (m + j + 1) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        have hstep :
            |w (brownianDyadicFloor H (m + r + 1) u) -
              w (brownianDyadicFloor H (m + r) u)| ≤
              brownianDyadicThreshold H a (m + r + 1) := by
          rcases dyadicFloor_refine_increment hH hu.1 hu.2 (m + r) with hsame | hmove
          · rw [hsame]
            simp [dyadicThreshold_nonneg hH.le (by linarith : (0:ℝ) ≤ a)]
          · obtain ⟨k, hk, hleft, hright⟩ := hmove
            rw [hleft, hright]
            exact hcell (m + r + 1) k hk
        calc
          |w (brownianDyadicFloor H (m + (r + 1)) u) -
              w (brownianDyadicFloor H m u)| ≤
            |w (brownianDyadicFloor H (m + r + 1) u) -
              w (brownianDyadicFloor H (m + r) u)| +
            |w (brownianDyadicFloor H (m + r) u) -
              w (brownianDyadicFloor H m u)| := by
                rw [Nat.add_succ]
                exact abs_sub_le _ _ _
          _ ≤ brownianDyadicThreshold H a (m + r + 1) +
              ∑ j ∈ Finset.range r,
                brownianDyadicThreshold H a (m + j + 1) :=
            add_le_add hstep ih
          _ = ∑ j ∈ Finset.range (r + 1),
                brownianDyadicThreshold H a (m + j + 1) := by
            rw [sum_range_succ]
            ring
  have hbound : ∀ r : ℕ,
      |w (brownianDyadicFloor H (m + r) u) -
        w (brownianDyadicFloor H m u)| ≤
        6 * brownianDyadicThreshold H a (m + 1) := by
    intro r
    exact (hfinite r).trans
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        dyadicThreshold_tail_sum_le hH.le ha (m + 1) r)
  have hfloorT : Tendsto
      (fun r => brownianDyadicFloor H (m + r) u) atTop (𝓝 u) :=
    (dyadicFloor_tendsto hH hu.1).comp
      (tendsto_atTop_mono (fun r : ℕ => Nat.le_add_left r m) tendsto_id)
  have hwT : Tendsto
      (fun r => |w (brownianDyadicFloor H (m + r) u) -
        w (brownianDyadicFloor H m u)|) atTop
      (𝓝 |w u - w (brownianDyadicFloor H m u)|) := by
    exact (continuous_abs.tendsto _).comp
      ((hcont.continuousAt.tendsto.comp hfloorT).sub tendsto_const_nhds)
  exact le_of_tendsto hwT (Filter.Eventually.of_forall hbound)

private theorem exists_dyadic_scale
    {H h : ℝ} (hH : 0 < H) (hh : h ∈ Ioc (0 : ℝ) H) :
    ∃ m : ℕ,
      brownianDyadicMesh H (m + 1) < h ∧
        h ≤ brownianDyadicMesh H m := by
  have hmesh : Tendsto (fun m => brownianDyadicMesh H (m + 1)) atTop (𝓝 0) := by
    have hhalf : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    have h := hhalf.const_mul H
    rw [mul_zero] at h
    refine h.congr fun m => ?_
    unfold brownianDyadicMesh
    rw [div_pow, one_pow]
    field_simp
  have hex : ∃ m, brownianDyadicMesh H (m + 1) < h := by
    have hev := hmesh.eventually (Iio_mem_nhds hh.1)
    exact Filter.Eventually.exists hev
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.find hex := ⟨_, rfl⟩
  have hspec : brownianDyadicMesh H (m + 1) < h := by
    rw [hm]; exact Nat.find_spec hex
  refine ⟨m, hspec, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · rw [hm0]
    simpa [brownianDyadicMesh] using hh.2
  · have hminimal : ¬ brownianDyadicMesh H (m - 1 + 1) < h :=
      Nat.find_min hex (by rw [← hm]; omega)
    have hmEq : m - 1 + 1 = m := by omega
    rw [hmEq] at hminimal
    exact le_of_not_gt hminimal

private theorem nearby_floor_cells
    {H u v : ℝ} (hH : 0 < H)
    (hu : u ∈ Icc (0 : ℝ) H) (hv : v ∈ Icc (0 : ℝ) H)
    {m : ℕ} (hnear : |u - v| ≤ brownianDyadicMesh H m) :
    brownianDyadicIndex H m u = brownianDyadicIndex H m v ∨
      brownianDyadicIndex H m u + 1 = brownianDyadicIndex H m v ∨
      brownianDyadicIndex H m v + 1 = brownianDyadicIndex H m u := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ m := pow_pos (by norm_num) _
  have hnear' : |((2 : ℝ) ^ m * u) / H - ((2 : ℝ) ^ m * v) / H| ≤ 1 := by
    rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos hp, abs_of_pos hH,
      div_le_one hH]
    unfold brownianDyadicMesh at hnear
    rw [le_div_iff₀ hp] at hnear
    nlinarith
  rw [abs_le] at hnear'
  have a1 := dyadicIndex_le_x hH hu.1 m
  have a2 := dyadicIndex_lt_x (H := H) (u := u) m
  have b1 := dyadicIndex_le_x hH hv.1 m
  have b2 := dyadicIndex_lt_x (H := H) (u := v) m
  have c1 : ((brownianDyadicIndex H m u : ℕ) : ℝ) <
      (brownianDyadicIndex H m v : ℕ) + 2 := by linarith
  have c2 : ((brownianDyadicIndex H m v : ℕ) : ℝ) <
      (brownianDyadicIndex H m u : ℕ) + 2 := by linarith
  have d1 : brownianDyadicIndex H m u < brownianDyadicIndex H m v + 2 := by
    exact_mod_cast c1
  have d2 : brownianDyadicIndex H m v < brownianDyadicIndex H m u + 2 := by
    exact_mod_cast c2
  omega

private theorem coarse_floor_increment_le
    {w : ℝ → ℝ} {H a u v : ℝ}
    (hH : 0 < H)
    (hu : u ∈ Icc (0 : ℝ) H) (hv : v ∈ Icc (0 : ℝ) H)
    (hcell : BrownianDyadicCellControl w H a)
    {m : ℕ} (hnear : |u - v| ≤ brownianDyadicMesh H m) :
    |w (brownianDyadicFloor H m u) -
      w (brownianDyadicFloor H m v)| ≤
      brownianDyadicThreshold H a m := by
  rcases nearby_floor_cells hH hu hv hnear with heq | hright | hleft
  · unfold brownianDyadicFloor
    rw [heq, sub_self, abs_zero]
    unfold brownianDyadicThreshold
    positivity
  · have hk := dyadicFloor_index_le hH hv m
    have hc := hcell m (brownianDyadicIndex H m u) (by omega)
    rw [hright] at hc
    unfold brownianDyadicFloor
    rw [abs_sub_comm]
    exact hc
  · have hk := dyadicFloor_index_le hH hu m
    have hc := hcell m (brownianDyadicIndex H m v) (by omega)
    rw [hleft] at hc
    unfold brownianDyadicFloor
    exact hc

private theorem threshold_le_entropyCore
    {H a h : ℝ} (hH : 0 < H) (ha : 2 ≤ a)
    (hh : h ∈ Ioc (0 : ℝ) H) {m : ℕ}
    (hscale : brownianDyadicMesh H (m + 1) < h ∧
      h ≤ brownianDyadicMesh H m) :
    11 * brownianDyadicThreshold H a m ≤
      brownianEntropyConstant * brownianEntropyCore H a h := by
  have hratio : 1 ≤ H / h := (le_div_iff₀ hh.1).2 (by rw [one_mul]; exact hh.2)
  have hlog0 : 0 ≤ Real.log (H / h) := Real.log_nonneg hratio
  have hpow : (2 : ℝ) ^ m ≤ H / h := by
    have := hscale.2
    unfold brownianDyadicMesh at this
    rw [le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) m)] at this
    exact (le_div_iff₀ hh.1).2 (by nlinarith)
  have hlogPow : (m : ℝ) * Real.log 2 ≤ Real.log (H / h) := by
    calc
      (m : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ m) := by
        rw [Real.log_pow]
      _ ≤ Real.log (H / h) := Real.log_le_log (by positivity) hpow
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hm : (m : ℝ) ≤ 2 * Real.log (H / h) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sub_nonneg.2 hlogTwo.le)]
  have hbudget : a + (m : ℝ) + 1 ≤
      2 * (Real.log (H / h) + a) := by
    nlinarith
  have hmesh : brownianDyadicMesh H m < 2 * h := by
    rw [dyadicMesh_succ] at hscale
    nlinarith
  have hprod :
      brownianDyadicMesh H m * (a + (m : ℝ) + 1) ≤
        4 * (h * (Real.log (H / h) + a)) := by
    have hleft0 : 0 ≤ brownianDyadicMesh H m := (dyadicMesh_pos hH m).le
    have hright0 : 0 ≤ Real.log (H / h) + a := by linarith
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hprod
  have h4 : Real.sqrt (4 * (h * (Real.log (H / h) + a))) =
      2 * Real.sqrt (h * (Real.log (H / h) + a)) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [h4] at hsqrt
  have hcore : brownianEntropyCore H a h =
      Real.sqrt (h * (Real.log (H / h) + a)) := by
    simp [brownianEntropyCore, ne_of_gt hh.1]
  unfold brownianDyadicThreshold brownianEntropyConstant
  rw [hcore]
  have hsqrt0 := Real.sqrt_nonneg (h * (Real.log (H / h) + a))
  nlinarith

-- scoped heartbeat allowance (<= 800000): long deterministic chaining calc
set_option maxHeartbeats 700000 in
/-- Deterministic dyadic chaining.  The large constant `256` leaves ample
room for the two approximation tails and the one coarse cell. -/
theorem brownianEntropyBound_of_dyadicCellControl
    {w : ℝ → ℝ} {H a : ℝ}
    (hH : 0 < H) (ha : 2 ≤ a)
    (hcont : Continuous w)
    (hcell : BrownianDyadicCellControl w H a) :
    ∀ u ∈ Icc (0 : ℝ) H, ∀ v ∈ Icc (0 : ℝ) H,
      |w u - w v| ≤ brownianEntropyBound H a |u - v| := by
  intro u hu v hv
  by_cases huv : u = v
  · subst v
    have h1a : (0 : ℝ) ≤ 1 + a := by linarith
    simp [brownianEntropyBound, brownianEntropyCore,
      brownianEntropyConstant, h1a]
  have hhpos : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
  have hhH : |u - v| ≤ H := by
    rw [abs_le]
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  obtain ⟨m, hscale⟩ := exists_dyadic_scale hH ⟨hhpos, hhH⟩
  have hleft := path_to_floor_le hH ha hu hcont hcell m
  have hright := path_to_floor_le hH ha hv hcont hcell m
  have hcoarse := coarse_floor_increment_le hH hu hv hcell hscale.2
  have hratio := dyadicThreshold_succ_le hH.le ha m
  have hsum : |w u - w v| ≤ 11 * brownianDyadicThreshold H a m := by
    calc
      |w u - w v| ≤
          |w u - w (brownianDyadicFloor H m u)| +
          |w (brownianDyadicFloor H m u) -
            w (brownianDyadicFloor H m v)| +
          |w (brownianDyadicFloor H m v) - w v| := by
            nlinarith [abs_sub_le (w u) (w (brownianDyadicFloor H m u))
              (w (brownianDyadicFloor H m v)),
              abs_sub_le (w u) (w (brownianDyadicFloor H m v)) (w v)]
      _ ≤ 6 * brownianDyadicThreshold H a (m + 1) +
          brownianDyadicThreshold H a m +
          6 * brownianDyadicThreshold H a (m + 1) := by
            gcongr
            simpa [abs_sub_comm] using hright
      _ ≤ 11 * brownianDyadicThreshold H a m := by
        nlinarith
  calc
    |w u - w v| ≤ 11 * brownianDyadicThreshold H a m := hsum
    _ ≤ brownianEntropyConstant * brownianEntropyCore H a |u - v| :=
      threshold_le_entropyCore hH ha ⟨hhpos, hhH⟩ hscale
    _ ≤ brownianEntropyBound H a |u - v| := by
      unfold brownianEntropyBound
      have hnonneg : 0 ≤ brownianEntropyConstant * (1 + a) := by
        unfold brownianEntropyConstant
        positivity
      linarith

/-! ## Probabilistic interface -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Abstract Brownian input on `[0,H]`.

The independence field records exactly the requested finite-grid interface.
The entropy proof only uses the marginal cell laws: independence is stronger
than a union bound needs, but is retained so this structure can also serve the
future Wiener construction. -/
structure DyadicBrownianOn
    (P : Measure Ω) (W : ℝ → Ω → ℝ) (H : ℝ) : Prop where
  eval_measurable : ∀ t, Measurable (W t)
  continuous_ae : ∀ᵐ omega ∂P, Continuous (fun t => W t omega)
  cell_law : ∀ m : ℕ, ∀ k : Fin (2 ^ m),
    P.map (fun omega =>
      W (brownianDyadicPoint H m (k.val + 1)) omega -
        W (brownianDyadicPoint H m k.val) omega) =
      gaussianReal 0 (Real.toNNReal (brownianDyadicMesh H m))
  cell_independent : ∀ m : ℕ,
    iIndepFun (fun (k : Fin (2 ^ m)) omega =>
      W (brownianDyadicPoint H m (k.val + 1)) omega -
        W (brownianDyadicPoint H m k.val) omega) P

private theorem integrable_exp_mul_of_gaussian_variance
    {P : Measure Ω} {X : Ω → ℝ} {variance : ℝ≥0}
    (hX : Measurable X)
    (hlaw : P.map X = gaussianReal 0 variance) (theta : ℝ) :
    Integrable (fun omega => Real.exp (theta * X omega)) P := by
  have h := integrable_exp_mul_gaussianReal
    (μ := 0) (v := variance) theta
  rw [← hlaw] at h
  exact h.comp_measurable hX

/-- Two-sided Gaussian tail with variance parameter `variance`. -/
theorem gaussian_abs_tail_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {variance : ℝ≥0} {x : ℝ}
    (hX : Measurable X) (hlaw : P.map X = gaussianReal 0 variance)
    (hvariance : 0 < (variance : ℝ)) (hx : 0 ≤ x) :
    P {omega | x < |X omega|} ≤
      ENNReal.ofReal (2 * Real.exp (-(x ^ 2) / (2 * variance))) := by
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)]
  let upper : Set Ω := {omega | x ≤ X omega}
  let lower : Set Ω := {omega | X omega ≤ -x}
  have hsub : {omega | x < |X omega|} ⊆ upper ∪ lower := by
    intro omega homega
    have homega' : x < |X omega| := homega
    rcases lt_abs.mp homega' with h | h
    · exact Or.inl h.le
    · exact Or.inr (show X omega ≤ -x by linarith)
  have hu := measure_ge_le_exp_mul_mgf
    (μ := P) (X := X) (t := x / variance) x
    (div_nonneg hx hvariance.le)
    (integrable_exp_mul_of_gaussian_variance hX hlaw (x / variance))
  have hl := measure_le_le_exp_mul_mgf
    (μ := P) (X := X) (t := -(x / variance)) (-x)
    (neg_nonpos.2 (div_nonneg hx hvariance.le))
    (integrable_exp_mul_of_gaussian_variance hX hlaw (-(x / variance)))
  rw [mgf_gaussianReal hlaw] at hu hl
  have hu' : P.real upper ≤ Real.exp (-(x ^ 2) / (2 * variance)) := by
    dsimp [upper]
    refine hu.trans_eq ?_
    rw [← Real.exp_add]
    congr 1
    field_simp [ne_of_gt hvariance]
    ring
  have hl' : P.real lower ≤ Real.exp (-(x ^ 2) / (2 * variance)) := by
    dsimp [lower]
    refine hl.trans_eq ?_
    rw [← Real.exp_add]
    congr 1
    field_simp [ne_of_gt hvariance]
    ring
  have hmono := measure_mono (μ := P) hsub
  have hunion := measure_union_le (μ := P) upper lower
  calc
    (P {omega | x < |X omega|}).toReal ≤ (P (upper ∪ lower)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hmono
    _ ≤ (P upper + P lower).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hunion
    _ = P.real upper + P.real lower := by
      rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      rfl
    _ ≤ 2 * Real.exp (-(x ^ 2) / (2 * variance)) := by linarith

/-- Failure of one dyadic level. -/
def brownianDyadicLevelFailure
    (W : ℝ → Ω → ℝ) (H a : ℝ) (m : ℕ) : Set Ω :=
  {omega | ∃ k < 2 ^ m,
    brownianDyadicThreshold H a m <
      |W (brownianDyadicPoint H m (k + 1)) omega -
        W (brownianDyadicPoint H m k) omega|}

/-- Failure of some dyadic cell. -/
def brownianDyadicFailure
    (W : ℝ → Ω → ℝ) (H a : ℝ) : Set Ω :=
  ⋃ m : ℕ, brownianDyadicLevelFailure W H a m

private theorem dyadicLevelFailure_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ → Ω → ℝ} {H a : ℝ}
    (hH : 0 < H) (ha : 0 ≤ a)
    (hW : DyadicBrownianOn P W H) (m : ℕ) :
    P (brownianDyadicLevelFailure W H a m) ≤
      ENNReal.ofReal (Real.exp (-a)) * (1 / 2 : ℝ≥0∞) ^ (m + 1) := by
  have hsub : brownianDyadicLevelFailure W H a m ⊆
      ⋃ k ∈ Finset.range (2 ^ m),
        {omega |
          brownianDyadicThreshold H a m <
            |W (brownianDyadicPoint H m (k + 1)) omega -
              W (brownianDyadicPoint H m k) omega|} := by
    rintro omega ⟨k, hk, hbad⟩
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq]
    exact ⟨k, hk, hbad⟩
  have hcell (k : ℕ) (hk : k < 2 ^ m) :
      P {omega |
          brownianDyadicThreshold H a m <
            |W (brownianDyadicPoint H m (k + 1)) omega -
              W (brownianDyadicPoint H m k) omega|} ≤
        ENNReal.ofReal
          (2 * Real.exp (-32 * (a + (m : ℝ) + 1))) := by
    let X : Ω → ℝ := fun omega =>
      W (brownianDyadicPoint H m (k + 1)) omega -
        W (brownianDyadicPoint H m k) omega
    have hXm : Measurable X :=
      (hW.eval_measurable _).sub (hW.eval_measurable _)
    have hlaw : P.map X =
        gaussianReal 0 (Real.toNNReal (brownianDyadicMesh H m)) := by
      simpa [X] using hW.cell_law m ⟨k, hk⟩
    have hmesh := dyadicMesh_pos hH m
    have hvariance :
        (Real.toNNReal (brownianDyadicMesh H m) : ℝ) =
          brownianDyadicMesh H m := Real.coe_toNNReal _ hmesh.le
    have htail := gaussian_abs_tail_le hXm hlaw
      (by simpa [hvariance] using hmesh)
      (dyadicThreshold_nonneg hH.le ha m)
    refine htail.trans_eq ?_
    congr 1
    rw [hvariance]
    unfold brownianDyadicThreshold
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [ne_of_gt hmesh]
    ring
  calc
    P (brownianDyadicLevelFailure W H a m) ≤
        P (⋃ k ∈ Finset.range (2 ^ m),
          {omega |
            brownianDyadicThreshold H a m <
              |W (brownianDyadicPoint H m (k + 1)) omega -
                W (brownianDyadicPoint H m k) omega|}) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range (2 ^ m),
        P {omega |
          brownianDyadicThreshold H a m <
            |W (brownianDyadicPoint H m (k + 1)) omega -
              W (brownianDyadicPoint H m k) omega|} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (2 ^ m),
        ENNReal.ofReal
          (2 * Real.exp (-32 * (a + (m : ℝ) + 1))) :=
      Finset.sum_le_sum fun k hk => hcell k (Finset.mem_range.mp hk)
    _ = (2 ^ m : ℝ≥0∞) *
        ENNReal.ofReal
          (2 * Real.exp (-32 * (a + (m : ℝ) + 1))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp
    _ ≤ ENNReal.ofReal (Real.exp (-a)) *
        (1 / 2 : ℝ≥0∞) ^ (m + 1) := by
      have h2m : (2 ^ m : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ m) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      have h12 : ENNReal.ofReal ((1 / 2 : ℝ) ^ (m + 1)) =
          (1 / 2 : ℝ≥0∞) ^ (m + 1) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        congr 1
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        simp
      rw [h2m, ← ENNReal.ofReal_mul (by positivity), ← h12,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      have hpow : ∀ n : ℕ, (2 : ℝ) ^ n ≤ Real.exp n := by
        intro n
        calc (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n :=
              pow_le_pow_left₀ (by norm_num) h2 n
          _ = Real.exp n := by rw [← Real.exp_nat_mul]; ring_nf
      have hhalf : Real.exp (-((m : ℝ) + 1)) ≤ (1 / 2 : ℝ) ^ (m + 1) := by
        have h := hpow (m + 1)
        push_cast at h
        rw [Real.exp_neg, one_div, inv_pow]
        exact inv_anti₀ (by positivity) h
      have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
      have hE : Real.exp ((m : ℝ) + 1) * Real.exp (-32 * (a + (m : ℝ) + 1)) ≤
          Real.exp (-a) * Real.exp (-((m : ℝ) + 1)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        (2 : ℝ) ^ m * (2 * Real.exp (-32 * (a + (m : ℝ) + 1))) ≤
            Real.exp (m : ℝ) * (Real.exp 1 * Real.exp (-32 * (a + (m : ℝ) + 1))) := by
          have hE0 := Real.exp_nonneg (-32 * (a + (m : ℝ) + 1))
          have : (2 : ℝ) * Real.exp (-32 * (a + (m : ℝ) + 1)) ≤
              Real.exp 1 * Real.exp (-32 * (a + (m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right h2 hE0
          calc (2 : ℝ) ^ m * (2 * Real.exp (-32 * (a + (m : ℝ) + 1)))
              ≤ Real.exp (m : ℝ) * (2 * Real.exp (-32 * (a + (m : ℝ) + 1))) :=
                mul_le_mul_of_nonneg_right (hpow m) (by positivity)
            _ ≤ _ := mul_le_mul_of_nonneg_left this (Real.exp_nonneg _)
        _ = Real.exp ((m : ℝ) + 1) * Real.exp (-32 * (a + (m : ℝ) + 1)) := by
          rw [← mul_assoc, ← Real.exp_add]
        _ ≤ Real.exp (-a) * Real.exp (-((m : ℝ) + 1)) := hE
        _ ≤ Real.exp (-a) * (1 / 2 : ℝ) ^ (m + 1) :=
          mul_le_mul_of_nonneg_left hhalf (Real.exp_nonneg _)

/-- Sharp (`K = 1`) dyadic failure tail for `a ≥ 0`. -/
theorem law_brownianDyadicFailure_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ → Ω → ℝ} {H a : ℝ}
    (hH : 0 < H) (ha : 0 ≤ a)
    (hW : DyadicBrownianOn P W H) :
    P (brownianDyadicFailure W H a) ≤
      ENNReal.ofReal (Real.exp (-a)) := by
  calc
    P (brownianDyadicFailure W H a) ≤
        ∑' m : ℕ, P (brownianDyadicLevelFailure W H a m) := by
      exact measure_iUnion_le _
    _ ≤ ∑' m : ℕ,
        ENNReal.ofReal (Real.exp (-a)) *
          (1 / 2 : ℝ≥0∞) ^ (m + 1) := by
      exact ENNReal.tsum_le_tsum fun m => dyadicLevelFailure_le hH ha hW m
    _ = ENNReal.ofReal (Real.exp (-a)) := by
      have hs : ∑' m : ℕ, (1 / 2 : ℝ≥0∞) ^ (m + 1) = 1 := by
        simp only [pow_succ]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_div,
          ENNReal.one_sub_inv_two, inv_inv]
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      rw [ENNReal.tsum_mul_left, hs, mul_one]

/-- Failure of path continuity. -/
def brownianContinuityFailure (W : ℝ → Ω → ℝ) : Set Ω :=
  {omega | ¬ Continuous (fun t => W t omega)}

/-- The measurable certificate failure used by the proof. -/
def brownianEntropyCertificateFailure
    (W : ℝ → Ω → ℝ) (H a : ℝ) : Set Ω :=
  brownianContinuityFailure W ∪ brownianDyadicFailure W H a

/-- The literal all-pairs modulus failure event. -/
def brownianEntropyFailure
    (W : ℝ → Ω → ℝ) (H a : ℝ) : Set Ω :=
  {omega | ∃ u ∈ Icc (0 : ℝ) H, ∃ v ∈ Icc (0 : ℝ) H,
    brownianEntropyBound H a |u - v| < |W u omega - W v omega|}

private theorem entropyFailure_subset_certificateFailure
    {W : ℝ → Ω → ℝ} {H a : ℝ}
    (hH : 0 < H) (ha : 2 ≤ a) :
    brownianEntropyFailure W H a ⊆
      brownianEntropyCertificateFailure W H a := by
  intro omega hbad
  by_cases hcont : Continuous (fun t => W t omega)
  · right
    by_contra hnot
    have hcell : BrownianDyadicCellControl (fun t => W t omega) H a := by
      intro m k hk
      by_contra hfail
      apply hnot
      rw [brownianDyadicFailure, Set.mem_iUnion]
      refine ⟨m, ?_⟩
      exact ⟨k, hk, lt_of_not_ge hfail⟩
    obtain ⟨u, hu, v, hv, huv⟩ := hbad
    exact (not_lt_of_ge
      (brownianEntropyBound_of_dyadicCellControl hH ha hcont hcell u hu v hv)) huv
  · exact Or.inl hcont

/-- Nontrivial entropy-modulus tail. -/
theorem law_brownianEntropyFailure_le_of_two_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ → Ω → ℝ} {H a : ℝ}
    (hH : 0 < H) (ha : 2 ≤ a)
    (hW : DyadicBrownianOn P W H) :
    P (brownianEntropyFailure W H a) ≤
      ENNReal.ofReal (Real.exp (-a)) := by
  have hcontZero : P (brownianContinuityFailure W) = 0 := by
    have h := hW.continuous_ae
    rw [MeasureTheory.ae_iff] at h
    simpa [brownianContinuityFailure] using h
  calc
    P (brownianEntropyFailure W H a) ≤
        P (brownianEntropyCertificateFailure W H a) :=
      measure_mono (entropyFailure_subset_certificateFailure hH ha)
    _ ≤ P (brownianContinuityFailure W) +
        P (brownianDyadicFailure W H a) := measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal (Real.exp (-a)) := by
      exact add_le_add (le_of_eq hcontZero)
        (law_brownianDyadicFailure_le hH (by linarith) hW)
    _ = ENNReal.ofReal (Real.exp (-a)) := zero_add _

/-- The all-`a ≥ 0` statement with `C = 256`, `K = exp 2`. -/
theorem law_brownianEntropyFailure_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ → Ω → ℝ} {H a : ℝ}
    (hH : 1 ≤ H) (ha : 0 ≤ a)
    (hW : DyadicBrownianOn P W H) :
    P (brownianEntropyFailure W H a) ≤
      ENNReal.ofReal
        (brownianEntropyTailConstant * Real.exp (-a)) := by
  by_cases htwo : 2 ≤ a
  · refine (law_brownianEntropyFailure_le_of_two_le
      (lt_of_lt_of_le zero_lt_one hH) htwo hW).trans ?_
    apply ENNReal.ofReal_le_ofReal
    unfold brownianEntropyTailConstant
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · calc
      P (brownianEntropyFailure W H a) ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal
          (brownianEntropyTailConstant * Real.exp (-a)) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        unfold brownianEntropyTailConstant
        rw [← Real.exp_add]
        have : 0 ≤ 2 - a := by linarith
        simpa using Real.one_le_exp this

/-!
THEOREM LIST
* `brownianEntropyCore`, `brownianEntropyBound`
* `BrownianDyadicCellControl`
* `brownianEntropyBound_of_dyadicCellControl`
* `DyadicBrownianOn`
* `gaussian_abs_tail_le`
* `law_brownianDyadicFailure_le`
* `law_brownianEntropyFailure_le_of_two_le`
* `law_brownianEntropyFailure_le`

CLOSES
* Safe treatment of the diagonal `u = v`.
* Abstract-process interface with measurable evaluations, a.s. continuous
  paths, independent finite dyadic-grid increments, and exact Gaussian laws.
* Gaussian two-sided tail from Mathlib's exact MGF and Chernoff theorem.
* Infinite dyadic union bound and deterministic chaining to all real points.
* Explicit constants `C = 256`, `K = exp 2`.

UNFINISHED
* No mathematical premise is carried beyond the abstract process interface.
  The scoped heartbeat increase is only for the floor-grid chaining proof.
* No Mathlib-Brownian specialization is present because that structure is not
  available at Ripple's pinned Mathlib commit.
END
-/

end Ripple.Kurtz.StrongApprox

end

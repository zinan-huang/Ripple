-- Ripple/Kurtz/StrongApprox/DeterministicItoBridge.lean
import Ripple.Stochastic.FilteredItoIntegralProcessGeneral
import Ripple.Analysis.BVIntegrationByParts
import Ripple.Analysis.BVQuadrature
import Ripple.Kurtz.StrongApprox.SectionFourAssembly

/-!
# The filtered Ito integral of a deterministic integrand is the integration-by-parts functional

For a Lipschitz `a` and a filtered pre-Brownian motion `B` with continuous paths, the installed
filtered Ito integral process of the (deterministic, hence predictable) integrand
`1_{(0,T]} a` at time `t ≤ T` equals `J a (B ·) t` almost surely, where `J` is
`Ripple.Analysis.BVIntegrationByParts.J`.

Both sides are limits of the same dyadic Riemann-Stieltjes sums: the simple processes with dyadic
left endpoints on `[0,t]` and on `[t,T]` converge to the integrand in the predictable `L²` norm
(by the Lipschitz bound), so the Ito integrals converge in `L²`; the sums converge pathwise to `J`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Ripple.Kurtz.StrongApprox.DeterministicItoBridge

/-! ## Dyadic grids in `ℝ≥0` -/

/-- The `k`-th point of the level-`m` dyadic grid of `[u, v]`. -/
def gridPt (u v : ℝ≥0) (m k : ℕ) : ℝ≥0 := u + (v - u) * k / 2 ^ m

theorem gridPt_coe {u v : ℝ≥0} (huv : u ≤ v) (m k : ℕ) :
    (gridPt u v m k : ℝ) = (u : ℝ) + ((v : ℝ) - u) * k / 2 ^ m := by
  unfold gridPt
  push_cast [NNReal.coe_sub huv]
  ring

theorem gridPt_zero (u v : ℝ≥0) (m : ℕ) : gridPt u v m 0 = u := by
  simp [gridPt]

theorem gridPt_mono (u v : ℝ≥0) (m : ℕ) : Monotone (gridPt u v m) := by
  intro k k' h
  unfold gridPt
  gcongr

theorem gridPt_ge (u v : ℝ≥0) (m k : ℕ) : u ≤ gridPt u v m k := le_self_add

theorem gridPt_le {u v : ℝ≥0} (huv : u ≤ v) (m : ℕ) {k : ℕ} (hk : k ≤ 2 ^ m) :
    gridPt u v m k ≤ v := by
  rw [← NNReal.coe_le_coe, gridPt_coe huv]
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hk' : (k : ℝ) ≤ 2 ^ m := by exact_mod_cast hk
  have hd : (0 : ℝ) ≤ (v : ℝ) - u := sub_nonneg.2 (by exact_mod_cast huv)
  have : ((v : ℝ) - u) * k / 2 ^ m ≤ (v : ℝ) - u := by
    rw [div_le_iff₀ h2]
    nlinarith
  linarith

/-- Existence of the dyadic cell containing a point of `(u, u + δ]`. -/
theorem exists_cell {u δ s : ℝ} (hδ : 0 < δ) (h1 : u < s) (h2 : s ≤ u + δ) (m : ℕ) :
    ∃ k : ℕ, k < 2 ^ m ∧ u + δ * k / 2 ^ m < s ∧ s ≤ u + δ * (k + 1 : ℕ) / 2 ^ m := by
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  set r : ℝ := (s - u) / δ * 2 ^ m with hr
  have hrpos : 0 < r := by positivity
  have hrle : r ≤ 2 ^ m := by
    rw [hr]
    have : (s - u) / δ ≤ 1 := by rw [div_le_one hδ]; linarith
    nlinarith
  have hceil_pos : 0 < ⌈r⌉₊ := Nat.ceil_pos.2 hrpos
  refine ⟨⌈r⌉₊ - 1, ?_, ?_, ?_⟩
  · have : ⌈r⌉₊ ≤ 2 ^ m := Nat.ceil_le.2 (by exact_mod_cast hrle)
    omega
  · have hk : ((⌈r⌉₊ - 1 : ℕ) : ℝ) < r := by
      have := Nat.ceil_lt_add_one hrpos.le
      have h3 : ((⌈r⌉₊ - 1 : ℕ) : ℝ) = (⌈r⌉₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hceil_pos]; simp
      linarith
    rw [← sub_pos]
    have : s - (u + δ * ((⌈r⌉₊ - 1 : ℕ) : ℝ) / 2 ^ m) =
        δ / 2 ^ m * (r - ((⌈r⌉₊ - 1 : ℕ) : ℝ)) := by
      rw [hr]; field_simp; ring
    rw [this]
    exact mul_pos (by positivity) (by linarith)
  · have hk : r ≤ ((⌈r⌉₊ - 1 + 1 : ℕ) : ℝ) := by
      have : ⌈r⌉₊ - 1 + 1 = ⌈r⌉₊ := by omega
      rw [this]; exact Nat.le_ceil r
    rw [← sub_nonneg]
    have : u + δ * ((⌈r⌉₊ - 1 + 1 : ℕ) : ℝ) / 2 ^ m - s =
        δ / 2 ^ m * (((⌈r⌉₊ - 1 + 1 : ℕ) : ℝ) - r) := by
      rw [hr]; field_simp; ring
    rw [this]
    exact mul_nonneg (by positivity) (by linarith)

/-! ## Step functions -/

/-- The dyadic left-endpoint step function of `a` on `(u, v]` at level `m`. -/
def stepFn (a : ℝ → ℝ) (u v : ℝ≥0) (m : ℕ) (s : ℝ≥0) : ℝ :=
  ∑ k : Fin (2 ^ m), if s ∈ Ioc (gridPt u v m k.val) (gridPt u v m (k.val + 1))
    then a (gridPt u v m k.val) else 0

theorem stepFn_eq_zero {a : ℝ → ℝ} {u v : ℝ≥0} (huv : u ≤ v) (m : ℕ) {s : ℝ≥0}
    (hs : s ∉ Ioc u v) : stepFn a u v m s = 0 := by
  unfold stepFn
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [if_neg]
  intro hk
  apply hs
  exact ⟨lt_of_le_of_lt (gridPt_ge u v m _) hk.1,
    hk.2.trans (gridPt_le huv m (Nat.succ_le_of_lt k.2))⟩

theorem stepFn_eq_of_mem {a : ℝ → ℝ} {u v : ℝ≥0} (huv : u ≤ v) (m : ℕ) {s : ℝ≥0}
    (hs : s ∈ Ioc u v) :
    ∃ k : Fin (2 ^ m), s ∈ Ioc (gridPt u v m k.val) (gridPt u v m (k.val + 1)) ∧
      stepFn a u v m s = a (gridPt u v m k.val) := by
  have hlt : (u : ℝ) < v := lt_of_lt_of_le (by exact_mod_cast hs.1) (by exact_mod_cast hs.2)
  have hsv : (s : ℝ) ≤ v := by exact_mod_cast hs.2
  obtain ⟨k, hk, h1, h2⟩ := exists_cell (u := (u : ℝ)) (δ := (v : ℝ) - u) (s := (s : ℝ))
    (sub_pos.2 hlt) (by exact_mod_cast hs.1) (by linarith) m
  have hmem : s ∈ Ioc (gridPt u v m k) (gridPt u v m (k + 1)) := by
    constructor
    · rw [← NNReal.coe_lt_coe, gridPt_coe huv]; exact h1
    · rw [← NNReal.coe_le_coe, gridPt_coe huv]; exact_mod_cast h2
  refine ⟨⟨k, hk⟩, hmem, ?_⟩
  unfold stepFn
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin (2 ^ m))]
  · simp only [if_pos hmem]
  · intro k' _ hne
    rw [if_neg]
    intro hk'
    have hne' : k'.val ≠ k := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with hlt' | hgt'
    · have : gridPt u v m (k'.val + 1) ≤ gridPt u v m k := gridPt_mono u v m (by omega)
      exact absurd (lt_of_le_of_lt (hk'.2.trans this) hmem.1) (lt_irrefl _)
    · have : gridPt u v m (k + 1) ≤ gridPt u v m k'.val := gridPt_mono u v m (by omega)
      exact absurd (lt_of_le_of_lt (hmem.2.trans this) hk'.1) (lt_irrefl _)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem abs_stepFn_sub_le {a : ℝ → ℝ} {K : ℝ≥0} {u v : ℝ≥0} (huv : u ≤ v)
    (ha : LipschitzOnWith K a (Icc (u : ℝ) v)) (m : ℕ) (s : ℝ≥0) :
    |stepFn a u v m s - (Ioc u v).indicator (fun s : ℝ≥0 => a s) s| ≤
      K * ((v : ℝ) - u) / 2 ^ m := by
  have hnn : 0 ≤ (K : ℝ) * ((v : ℝ) - u) / 2 ^ m := by
    have : (0 : ℝ) ≤ (v : ℝ) - u := sub_nonneg.2 (by exact_mod_cast huv)
    positivity
  by_cases hs : s ∈ Ioc u v
  · obtain ⟨k, hk, hstep⟩ := stepFn_eq_of_mem (a := a) huv m hs
    rw [hstep, indicator_of_mem hs]
    have hpk : (gridPt u v m k.val : ℝ) ∈ Icc (u : ℝ) v :=
      ⟨by exact_mod_cast gridPt_ge u v m _,
        by exact_mod_cast gridPt_le huv m (Nat.le_of_lt k.2)⟩
    have hsI : (s : ℝ) ∈ Icc (u : ℝ) v :=
      ⟨by exact_mod_cast hs.1.le, by exact_mod_cast hs.2⟩
    have hd := ha.dist_le_mul _ hpk _ hsI
    rw [Real.dist_eq, Real.dist_eq] at hd
    have hgap : (s : ℝ) - gridPt u v m k.val ≤ ((v : ℝ) - u) / 2 ^ m := by
      have h1 : (s : ℝ) ≤ gridPt u v m (k.val + 1) := by exact_mod_cast hk.2
      rw [gridPt_coe huv] at h1
      rw [gridPt_coe huv]
      push_cast at h1
      have : (u : ℝ) + ((v : ℝ) - u) * (k.val + 1) / 2 ^ m -
          ((u : ℝ) + ((v : ℝ) - u) * k.val / 2 ^ m) = ((v : ℝ) - u) / 2 ^ m := by ring
      linarith
    have hgap0 : 0 ≤ (s : ℝ) - gridPt u v m k.val := by
      have : (gridPt u v m k.val : ℝ) < s := by exact_mod_cast hk.1
      linarith
    rw [abs_sub_comm (gridPt u v m k.val : ℝ) (s : ℝ), abs_of_nonneg hgap0] at hd
    calc |a (gridPt u v m k.val) - a s| ≤ K * (s - gridPt u v m k.val) := hd
      _ ≤ K * (((v : ℝ) - u) / 2 ^ m) := mul_le_mul_of_nonneg_left hgap (NNReal.coe_nonneg K)
      _ = K * ((v : ℝ) - u) / 2 ^ m := by ring
  · rw [stepFn_eq_zero huv m hs, indicator_of_notMem hs]
    simpa using hnn

/-! ## Dyadic simple processes -/

section Simple

open Ripple.Stochastic Ripple.Stochastic.FilteredItoIntegralL2
  Ripple.Stochastic.FilteredItoIntegralCLM Ripple.Stochastic.FilteredItoIntegralProcess
  Ripple.Stochastic.FilteredItoIntegralProcessGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {𝓖 : Filtration ℝ≥0 mΩ} [hB : IsFilteredPreBrownian B 𝓖 μ]

theorem coe_sum_apply {ι' : Type*} (s : Finset ι') (V : ι' → SimpleProcess ℝ 𝓖) (t : ℝ≥0)
    (ω : Ω) : (∑ i ∈ s, V i) t ω = ∑ i ∈ s, V i t ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, SimpleProcess.coe_add, ih]

theorem itoSimpleProcess_sum (hBmeas : ∀ t, Measurable (B t)) {ι' : Type*} (s : Finset ι')
    (V : ι' → SimpleProcess ℝ 𝓖) (t : ℝ≥0) (ω : Ω) :
    itoSimpleProcess (𝓖 := 𝓖) hBmeas (∑ i ∈ s, V i) t ω =
      ∑ i ∈ s, itoSimpleProcess (𝓖 := 𝓖) hBmeas (V i) t ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [itoSimpleProcess]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, itoSimpleProcess_add]
    simp [ih]

/-- The `T`-bounded simple process with the dyadic left-endpoint values of `a` on `(u, v]`. -/
def gridSP (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (a : ℝ → ℝ) {u v : ℝ≥0}
    (huv : u ≤ v) (hvT : v ≤ T) (m : ℕ) : TBoundedSP (𝓖 := 𝓖) T hBmeas :=
  ∑ k : Fin (2 ^ m), a (gridPt u v m k.val) •
    iocSP_T (𝓖 := 𝓖) hBmeas (gridPt_mono u v m (Nat.le_succ k.val))
      ((gridPt_le huv m (Nat.succ_le_of_lt k.2)).trans hvT)
      (F := Set.univ) (@MeasurableSet.univ Ω (𝓖 _))

theorem coe_iocSP_apply {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {x y : ℝ≥0} (hxy : x ≤ y)
    (hyT : y ≤ T) (s : ℝ≥0) (ω : Ω) :
    (iocSP_T (𝓖 := 𝓖) hBmeas hxy hyT (F := Set.univ) (@MeasurableSet.univ Ω (𝓖 _))).val s ω =
      if s ∈ Ioc x y then 1 else 0 := by
  change ((ElementaryPredictableSet.IocProd x y (@MeasurableSet.univ Ω (𝓖 x))).indicator
    (1 : ℝ)) s ω = _
  rw [ElementaryPredictableSet.coe_indicator, ElementaryPredictableSet.coe_IocProd]
  simp [Function.curry, Set.indicator, Set.mem_prod]

theorem uncurry_gridSP (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (a : ℝ → ℝ) {u v : ℝ≥0}
    (huv : u ≤ v) (hvT : v ≤ T) (m : ℕ) (z : ℝ≥0 × Ω) :
    Function.uncurry ⇑(gridSP (𝓖 := 𝓖) T hBmeas a huv hvT m).val z = stepFn a u v m z.1 := by
  obtain ⟨s, ω⟩ := z
  change (gridSP (𝓖 := 𝓖) T hBmeas a huv hvT m).val s ω = _
  unfold gridSP stepFn
  rw [Submodule.coe_sum, coe_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, SimpleProcess.coe_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [coe_iocSP_apply]
  split_ifs <;> simp

theorem itoSimpleProcess_iocSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {x y : ℝ≥0}
    (hxy : x ≤ y) (hyT : y ≤ T) (t : ℝ≥0) (ω : Ω) :
    itoSimpleProcess (𝓖 := 𝓖) hBmeas
      (iocSP_T (𝓖 := 𝓖) hBmeas hxy hyT (F := Set.univ) (@MeasurableSet.univ Ω (𝓖 _))).val t ω =
      B (min y t) ω - B (min x t) ω := by
  rw [itoSimpleProcess_apply]
  change ((ElementaryPredictableSet.IocProd x y (@MeasurableSet.univ Ω (𝓖 x))).indicator
    (1 : ℝ)).value.sum _ = _
  unfold ElementaryPredictableSet.indicator
  simp only
  rw [Finsupp.onFinset_sum _ (by simp)]
  simp [ElementaryPredictableSet.IocProd, hxy]

theorem itoSimpleProcess_gridSP (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (a : ℝ → ℝ)
    {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) (m : ℕ) (t : ℝ≥0) (ω : Ω) :
    itoSimpleProcess (𝓖 := 𝓖) hBmeas (gridSP (𝓖 := 𝓖) T hBmeas a huv hvT m).val t ω =
      ∑ k : Fin (2 ^ m), a (gridPt u v m k.val) *
        (B (min (gridPt u v m (k.val + 1)) t) ω - B (min (gridPt u v m k.val) t) ω) := by
  unfold gridSP
  rw [Submodule.coe_sum, itoSimpleProcess_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul]
  have := itoSimpleProcess_smul (𝓖 := 𝓖) hBmeas (a (gridPt u v m k.val))
    (iocSP_T (𝓖 := 𝓖) hBmeas (gridPt_mono u v m (Nat.le_succ k.val))
      ((gridPt_le huv m (Nat.succ_le_of_lt k.2)).trans hvT)
      (F := Set.univ) (@MeasurableSet.univ Ω (𝓖 _))).val t
  rw [this, Pi.smul_apply, smul_eq_mul, itoSimpleProcess_iocSP]

/-- The deterministic integrand `1_{(0,T]} a`, as a function on `ℝ≥0 × Ω`. -/
def targetFn (a : ℝ → ℝ) (T : ℝ≥0) (z : ℝ≥0 × Ω) : ℝ :=
  (Ioc 0 T).indicator (fun s : ℝ≥0 => a s) z.1

/-- The approximating simple processes: dyadic left endpoints on `(0, t]` and on `(t, T]`. -/
def approxSP (T t : ℝ≥0) (htT : t ≤ T) (hBmeas : ∀ t, Measurable (B t)) (a : ℝ → ℝ)
    (m : ℕ) : TBoundedSP (𝓖 := 𝓖) T hBmeas :=
  gridSP (𝓖 := 𝓖) T hBmeas a (zero_le : (0 : ℝ≥0) ≤ t) htT m + gridSP (𝓖 := 𝓖) T hBmeas a htT le_rfl m

theorem uncurry_approxSP (T t : ℝ≥0) (htT : t ≤ T) (hBmeas : ∀ t, Measurable (B t))
    (a : ℝ → ℝ) (m : ℕ) (z : ℝ≥0 × Ω) :
    Function.uncurry ⇑(approxSP (𝓖 := 𝓖) T t htT hBmeas a m).val z =
      stepFn a 0 t m z.1 + stepFn a t T m z.1 := by
  unfold approxSP
  rw [Submodule.coe_add, SimpleProcess.coe_add]
  simp only [Function.uncurry, Pi.add_apply]
  rw [← uncurry_gridSP (𝓖 := 𝓖) T hBmeas a (zero_le : (0 : ℝ≥0) ≤ t) htT m z,
    ← uncurry_gridSP (𝓖 := 𝓖) T hBmeas a htT le_rfl m z]
  rfl

theorem abs_approx_sub_target_le {T t : ℝ≥0} (htT : t ≤ T) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (hBmeas : ∀ t, Measurable (B t)) (m : ℕ)
    (z : ℝ≥0 × Ω) :
    |Function.uncurry ⇑(approxSP (𝓖 := 𝓖) T t htT hBmeas a m).val z - targetFn a T z| ≤
      K * T / 2 ^ m := by
  rw [uncurry_approxSP]
  have htT' : (t : ℝ) ≤ T := by exact_mod_cast htT
  have ha1 : LipschitzOnWith K a (Icc ((0 : ℝ≥0) : ℝ) (t : ℝ)) :=
    ha.mono (by intro x hx; exact ⟨by simpa using hx.1, hx.2.trans htT'⟩)
  have ha2 : LipschitzOnWith K a (Icc (t : ℝ) (T : ℝ)) :=
    ha.mono (by intro x hx; exact ⟨(NNReal.coe_nonneg t).trans hx.1, hx.2⟩)
  have h1 := abs_stepFn_sub_le (zero_le : (0 : ℝ≥0) ≤ t) ha1 m z.1
  have h2 := abs_stepFn_sub_le htT ha2 m z.1
  have hsplit : targetFn a T z = (Ioc 0 t).indicator (fun s : ℝ≥0 => a s) z.1 +
      (Ioc t T).indicator (fun s : ℝ≥0 => a s) z.1 := by
    unfold targetFn
    have hdisj : Disjoint (Ioc (0 : ℝ≥0) t) (Ioc t T) := Set.Ioc_disjoint_Ioc_of_le le_rfl
    have := congrFun (Set.indicator_union_of_disjoint hdisj (fun s : ℝ≥0 => a s)) z.1
    rw [Set.Ioc_union_Ioc_eq_Ioc (zero_le : (0 : ℝ≥0) ≤ t) htT] at this
    exact this
  rw [hsplit]
  have hsum : (K : ℝ) * (((t : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ)) / 2 ^ m +
      K * ((T : ℝ) - t) / 2 ^ m = K * T / 2 ^ m := by
    simp only [NNReal.coe_zero, sub_zero]; ring
  calc _ = |(stepFn a 0 t m z.1 - (Ioc 0 t).indicator (fun s : ℝ≥0 => a s) z.1) +
        (stepFn a t T m z.1 - (Ioc t T).indicator (fun s : ℝ≥0 => a s) z.1)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq hsum)

theorem tendsto_dyadic_error (c : ℝ) : Tendsto (fun m : ℕ => c / 2 ^ m) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

theorem tendsto_approx_targetFn {T t : ℝ≥0} (htT : t ≤ T) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (hBmeas : ∀ t, Measurable (B t)) (z : ℝ≥0 × Ω) :
    Tendsto (fun m => Function.uncurry ⇑(approxSP (𝓖 := 𝓖) T t htT hBmeas a m).val z) atTop
      (𝓝 (targetFn a T z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun m => norm_nonneg _)
    (fun m => abs_approx_sub_target_le htT ha hBmeas m z) (tendsto_dyadic_error _)

theorem stronglyMeasurable_targetFn {T : ℝ≥0} {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (hBmeas : ∀ t, Measurable (B t)) :
    StronglyMeasurable[𝓖.predictable] (targetFn (Ω := Ω) a T) := by
  refine stronglyMeasurable_of_tendsto (atTop : Filter ℕ)
    (f := fun m => Function.uncurry ⇑(approxSP (𝓖 := 𝓖) T T le_rfl hBmeas a m).val)
    (fun m => (approxSP (𝓖 := 𝓖) T T le_rfl hBmeas a m).val.isStronglyPredictable) ?_
  rw [tendsto_pi_nhds]
  exact fun z => tendsto_approx_targetFn le_rfl ha hBmeas z

theorem abs_targetFn_le {T : ℝ≥0} {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (z : ℝ≥0 × Ω) :
    ‖targetFn a T z‖ ≤ |a 0| + K * T := by
  unfold targetFn
  by_cases hs : z.1 ∈ Ioc 0 T
  · rw [indicator_of_mem hs]
    have h0 : (0 : ℝ) ∈ Icc 0 (T : ℝ) := ⟨le_rfl, NNReal.coe_nonneg T⟩
    have hsI : ((z.1 : ℝ≥0) : ℝ) ∈ Icc 0 (T : ℝ) :=
      ⟨NNReal.coe_nonneg _, by exact_mod_cast hs.2⟩
    have hd := ha.dist_le_mul _ hsI _ h0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at hd
    have hz : |(z.1 : ℝ)| ≤ T := by
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]; exact_mod_cast hs.2
    have : |a z.1| ≤ |a 0| + K * T := by
      calc |a z.1| = |(a z.1 - a 0) + a 0| := by ring_nf
        _ ≤ |a z.1 - a 0| + |a 0| := abs_add_le _ _
        _ ≤ K * |(z.1 : ℝ)| + |a 0| := by gcongr
        _ ≤ K * T + |a 0| := by gcongr
        _ = _ := by ring
    simpa using this
  · rw [indicator_of_notMem hs]
    simp only [norm_zero]
    positivity

omit hB in
theorem memLp_targetFn {T : ℝ≥0} {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (hBmeas : ∀ t, Measurable (B t)) :
    MemLp (targetFn (Ω := Ω) a T) 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) :=
  MemLp.of_bound (stronglyMeasurable_targetFn (𝓖 := 𝓖) ha hBmeas).aestronglyMeasurable _
    (ae_of_all _ fun z => abs_targetFn_le ha z)

omit hB in
/-- The deterministic integrand `1_{(0,T]} a` exists as a predictable `L²` class. -/
theorem exists_deterministicIntegrand (T : ℝ≥0) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (hBmeas : ∀ t, Measurable (B t)) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas),
      (φ : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas] targetFn a T :=
  ⟨(memLp_targetFn (𝓖 := 𝓖) (μ := μ) ha hBmeas).toLp _, MemLp.coeFn_toLp _⟩

theorem tendsto_simpleAssembly_approx {T t : ℝ≥0} (htT : t ≤ T) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas))
    (hφ : (φ : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas] targetFn a T) :
    Tendsto (fun m => simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas
      (approxSP (𝓖 := 𝓖) T t htT hBmeas a m)) atTop (𝓝 φ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hfin : (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) Set.univ ≠ ⊤ := measure_ne_top _ _
  set c : ℝ := (((trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) Set.univ) ^ ((2 : ℝ≥0∞).toReal⁻¹)).toReal with hc
  have hbound : ∀ m, ‖simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas
      (approxSP (𝓖 := 𝓖) T t htT hBmeas a m) - φ‖ ≤ c * (K * T / 2 ^ m) := by
    intro m
    set Vm := approxSP (𝓖 := 𝓖) T t htT hBmeas a m with hVm
    have hco : ∀ᵐ z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas), (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas Vm : ℝ≥0 × Ω → ℝ) z =
        Function.uncurry ⇑Vm.val z :=
      MemLp.coeFn_toLp (memLp_uncurry_trim_T (𝓖 := 𝓖) (μ := μ) T hBmeas Vm.val)
    have hsub : ∀ᵐ z ∂(trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas), ((simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas Vm - φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) :
        ℝ≥0 × Ω → ℝ) z = Function.uncurry ⇑Vm.val z - targetFn a T z := by
      filter_upwards [Lp.coeFn_sub (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas Vm) φ,
        hco, hφ] with z h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    have hnorm : ‖simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas Vm - φ‖ =
        (eLpNorm (fun z => Function.uncurry ⇑Vm.val z - targetFn a T z) 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)).toReal := by
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae hsub
    rw [hnorm]
    have hle := eLpNorm_le_of_ae_bound (μ := (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)) (p := 2)
      (f := fun z => Function.uncurry ⇑Vm.val z - targetFn a T z) (C := K * T / 2 ^ m)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]; exact abs_approx_sub_target_le htT ha hBmeas m z)
    calc (eLpNorm (fun z => Function.uncurry ⇑Vm.val z - targetFn a T z) 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas)).toReal
        ≤ ((trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas) Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (K * T / 2 ^ m)).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top
            (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin) ENNReal.ofReal_ne_top) hle
      _ = c * (K * T / 2 ^ m) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  refine squeeze_zero (fun m => norm_nonneg _) hbound ?_
  simpa using (tendsto_dyadic_error ((K : ℝ) * T)).const_mul c

/-- The simple-process integral at time `t` of the approximants is the left Riemann-Stieltjes
sum on `[0, t]`; the part on `(t, T]` does not contribute. -/
theorem itoSimpleProcess_approxSP {T t : ℝ≥0} (htT : t ≤ T) (hBmeas : ∀ t, Measurable (B t))
    (a : ℝ → ℝ) (m : ℕ) (ω : Ω) :
    itoSimpleProcess (𝓖 := 𝓖) hBmeas (approxSP (𝓖 := 𝓖) T t htT hBmeas a m).val t ω =
      ∑ k : Fin (2 ^ m), a (gridPt 0 t m k.val) *
        (B (gridPt 0 t m (k.val + 1)) ω - B (gridPt 0 t m k.val) ω) := by
  unfold approxSP
  rw [Submodule.coe_add, itoSimpleProcess_add, Pi.add_apply,
    itoSimpleProcess_gridSP, itoSimpleProcess_gridSP]
  have hR : ∑ k : Fin (2 ^ m), a (gridPt t T m k.val) *
      (B (min (gridPt t T m (k.val + 1)) t) ω - B (min (gridPt t T m k.val) t) ω) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [min_eq_right (gridPt_ge t T m _), min_eq_right (gridPt_ge t T m _), sub_self, mul_zero]
  rw [hR, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [min_eq_left (gridPt_le (zero_le : (0 : ℝ≥0) ≤ t) m (Nat.succ_le_of_lt k.2)),
    min_eq_left (gridPt_le (zero_le : (0 : ℝ≥0) ≤ t) m (Nat.le_of_lt k.2))]

/-- Pathwise convergence of the Riemann-Stieltjes sums to the integration-by-parts functional. -/
theorem tendsto_leftSum_J {t : ℝ≥0} {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (t : ℝ))) {ω : Ω}
    (hcont : Continuous fun s : ℝ≥0 => B s ω) (hzero : B 0 ω = 0) :
    Tendsto (fun m => ∑ k : Fin (2 ^ m), a (gridPt 0 t m k.val) *
        (B (gridPt 0 t m (k.val + 1)) ω - B (gridPt 0 t m k.val) ω)) atTop
      (𝓝 (Ripple.Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω) t)) := by
  have hw : ContinuousOn (fun s : ℝ => B s.toNNReal ω) (Icc 0 (t : ℝ)) :=
    (hcont.comp continuous_real_toNNReal).continuousOn
  have hw0 : (fun s : ℝ => B s.toNNReal ω) 0 = 0 := by simpa using hzero
  have h := Ripple.Analysis.BVIntegrationByParts.dyadic_leftSum_tendsto_J
    (NNReal.coe_nonneg t) ha hw hw0
  refine h.congr fun m => Finset.sum_congr rfl fun k _ => ?_
  have hc : ∀ j : ℕ, (gridPt 0 t m j : ℝ) = (t : ℝ) * j / 2 ^ m := fun j => by
    rw [gridPt_coe (zero_le : (0 : ℝ≥0) ≤ t)]; simp
  have hc' : (t : ℝ) * ((k.val : ℝ) + 1) / 2 ^ m = (gridPt 0 t m (k.val + 1) : ℝ) := by
    rw [hc]; push_cast; ring
  rw [hc', ← hc k.val]
  simp [Real.toNNReal_coe]

omit [IsProbabilityMeasure μ] in
include hB in
/-- `B 0 = 0` almost surely for a pre-Brownian motion. -/
theorem ae_zero_of_isFilteredPreBrownian : ∀ᵐ ω ∂μ, B 0 ω = 0 := by
  haveI : IsPreBrownian B μ := hB.toIsPreBrownian
  have h := (IsPreBrownian.hasLaw_eval (X := B) (P := μ) 0)
  simpa using HasLaw.ae_eq_const_of_gaussianReal (by simpa using h)

/-- **The filtered Ito integral of a deterministic Lipschitz integrand.** For `t ≤ T`, the
installed filtered Ito integral process at time `t` of the predictable integrand
`1_{(0,T]} a` equals the integration-by-parts functional `J a (B ·) t` almost surely. -/
theorem itoProcessCLM_deterministic (T t : ℝ≥0) (htT : t ≤ T) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (hBmeas : ∀ t, Measurable (B t))
    (hcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 => B s ω)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas))
    (hφ : (φ : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas] targetFn a T) :
    (itoProcessCLM (𝓖 := 𝓖) (μ := μ) T t hBmeas φ : Ω → ℝ) =ᵐ[μ]
      fun ω => Ripple.Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω) t := by
  have htT' : (t : ℝ) ≤ T := by exact_mod_cast htT
  have ha_t : LipschitzOnWith K a (Icc 0 (t : ℝ)) :=
    ha.mono (Icc_subset_Icc le_rfl htT')
  -- the approximating Lp elements
  set ψ : ℕ → Lp ℝ 2 μ := fun m => itoProcessCLM (𝓖 := 𝓖) (μ := μ) T t hBmeas
    (simpleAssembly_T (𝓖 := 𝓖) (μ := μ) T hBmeas (approxSP (𝓖 := 𝓖) T t htT hBmeas a m))
    with hψ
  have hψlim : Tendsto ψ atTop (𝓝 (itoProcessCLM (𝓖 := 𝓖) (μ := μ) T t hBmeas φ)) :=
    ((itoProcessCLM (𝓖 := 𝓖) (μ := μ) T t hBmeas).continuous.tendsto φ).comp
      (tendsto_simpleAssembly_approx htT ha hBmeas φ hφ)
  -- each approximant is the Riemann-Stieltjes sum, almost surely
  have hψae : ∀ᵐ ω ∂μ, ∀ m, (ψ m : Ω → ℝ) ω = ∑ k : Fin (2 ^ m), a (gridPt 0 t m k.val) *
      (B (gridPt 0 t m (k.val + 1)) ω - B (gridPt 0 t m k.val) ω) := by
    rw [ae_all_iff]
    intro m
    have h1 := MemLp.coeFn_toLp
      (memLp_itoSimpleProcess (𝓖 := 𝓖) (μ := μ) hBmeas
        (approxSP (𝓖 := 𝓖) T t htT hBmeas a m).val t)
    filter_upwards [h1] with ω hω
    have : (ψ m : Ω → ℝ) ω = itoSimpleProcess (𝓖 := 𝓖) hBmeas
        (approxSP (𝓖 := 𝓖) T t htT hBmeas a m).val t ω := by
      simp only [hψ]
      rw [itoProcessCLM_simpleAssembly_T (𝓖 := 𝓖)]
      exact hω
    rw [this, itoSimpleProcess_approxSP]
  -- a subsequence converges almost surely in `L²`
  have hL2 : Tendsto (fun m => eLpNorm ((ψ m : Ω → ℝ) -
      (itoProcessCLM (𝓖 := 𝓖) (μ := μ) T t hBmeas φ : Ω → ℝ)) 2 μ) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hψlim
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    (fun m => (Lp.aestronglyMeasurable (ψ m)))
    (Lp.aestronglyMeasurable (itoProcessCLM (𝓖 := 𝓖) (μ := μ) T t hBmeas φ)) hL2
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  filter_upwards [hae, hψae, hcont, ae_zero_of_isFilteredPreBrownian (B := B) (μ := μ) (𝓖 := 𝓖)]
    with ω h1 h2 h3 h4
  have hJ := (tendsto_leftSum_J ha_t h3 h4).comp hns.tendsto_atTop
  have h1' : Tendsto (fun i => ∑ k : Fin (2 ^ ns i), a (gridPt 0 t (ns i) k.val) *
      (B (gridPt 0 t (ns i) (k.val + 1)) ω - B (gridPt 0 t (ns i) k.val) ω)) atTop
      (𝓝 (itoProcessCLM (𝓖 := 𝓖) (μ := μ) T t hBmeas φ ω)) :=
    h1.congr fun i => h2 (ns i)
  exact tendsto_nhds_unique h1' hJ

/-- The terminal case: at the horizon the process is the terminal Ito integral. -/
theorem itoIntegralCLM_deterministic (T : ℝ≥0) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (hBmeas : ∀ t, Measurable (B t))
    (hcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 => B s ω)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas))
    (hφ : (φ : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas] targetFn a T) :
    (itoIntegralCLM_T (𝓖 := 𝓖) (μ := μ) T hBmeas φ : Ω → ℝ) =ᵐ[μ]
      fun ω => Ripple.Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω) T := by
  have heq : itoProcessCLM (𝓖 := 𝓖) (μ := μ) T T hBmeas φ =
      itoIntegralCLM_T (𝓖 := 𝓖) (μ := μ) T hBmeas φ :=
    congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (𝓖 := 𝓖) (μ := μ) T hBmeas)
      (itoProcessCLM (𝓖 := 𝓖) (μ := μ) T T hBmeas).continuous
      (itoIntegralCLM_T (𝓖 := 𝓖) (μ := μ) T hBmeas).continuous
      (funext fun V => by
        simp only [Function.comp_apply, itoProcessCLM_simpleAssembly_T (𝓖 := 𝓖),
          itoIntegralCLM_T_simpleAssembly_T (𝓖 := 𝓖), itoSimpleProcessLp, itoSimpleLp,
          itoSimpleProcess_eq_itoSimple (𝓖 := 𝓖) hBmeas V.val (fun p hp => V.property p hp)])) φ
  rw [← heq]
  exact itoProcessCLM_deterministic T T le_rfl ha hBmeas hcont φ hφ

/-- **`stochasticIntegral_eq_J`.** The deterministic predictable integrand `1_{(0,T]} a` exists
as a class `φ` in the predictable `L²` space, and for every `t ≤ T` its filtered Ito integral
process at time `t` equals `J a (B ·) t` almost surely. -/
theorem stochasticIntegral_eq_J (T : ℝ≥0) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (hBmeas : ∀ t, Measurable (B t))
    (hcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 => B s ω) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas),
      (φ : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas] targetFn a T ∧
      ∀ t : ℝ≥0, t ≤ T →
        (itoProcessCLM (𝓖 := 𝓖) (μ := μ) T t hBmeas φ : Ω → ℝ) =ᵐ[μ]
          fun ω => Ripple.Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω) t := by
  obtain ⟨φ, hφ⟩ := exists_deterministicIntegrand (𝓖 := 𝓖) (μ := μ) T ha hBmeas
  exact ⟨φ, hφ, fun t htT => itoProcessCLM_deterministic T t htT ha hBmeas hcont φ hφ⟩

/-- Simultaneously in time: any almost surely continuous version `Y` of the Ito integral process
(for example the one from `ContinuousItoElementary.exists_continuousIto_modification`) equals
`J a (B ·)` at all times of `[0, T]`, outside one null set. -/
theorem ae_forall_eq_J (T : ℝ≥0) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (hBmeas : ∀ t, Measurable (B t))
    (hcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 => B s ω)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas))
    (hφ : (φ : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (𝓖 := 𝓖) (μ := μ) T hBmeas] targetFn a T)
    (Y : Set.Icc (0 : ℝ≥0) T → Ω → ℝ)
    (hY : ∀ t, Y t =ᵐ[μ] (itoProcessCLM (𝓖 := 𝓖) (μ := μ) T t.val hBmeas φ : Ω → ℝ))
    (hYc : ∀ᵐ ω ∂μ, Continuous fun t => Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      Y t ω = Ripple.Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω) (t.val : ℝ) := by
  have hT : (0 : ℝ) ≤ T := NNReal.coe_nonneg T
  let rp : SectionFourAssembly.RatIcc (T : ℝ) → Set.Icc (0 : ℝ≥0) T := fun q =>
    ⟨((q.1 : ℚ) : ℝ).toNNReal, zero_le, Real.toNNReal_le_iff_le_coe.2 q.2.2⟩
  have hrp : ∀ q, (((rp q).val : ℝ≥0) : ℝ) = ((q.1 : ℚ) : ℝ) := fun q =>
    Real.coe_toNNReal _ q.2.1
  have hrat : ∀ᵐ ω ∂μ, ∀ q : SectionFourAssembly.RatIcc (T : ℝ),
      Y (rp q) ω = Ripple.Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω)
        (((rp q).val : ℝ≥0) : ℝ) := by
    rw [ae_all_iff]
    intro q
    filter_upwards [hY (rp q),
      itoProcessCLM_deterministic T (rp q).val (rp q).2.2 ha hBmeas hcont φ hφ] with ω h1 h2
    rw [h1, h2]
  filter_upwards [hrat, hYc, hcont] with ω h1 h2 h3
  have hw : ContinuousOn (fun s : ℝ => B s.toNNReal ω) (Icc 0 (T : ℝ)) :=
    (h3.comp continuous_real_toNNReal).continuousOn
  have hJc : Continuous fun t : Set.Icc (0 : ℝ≥0) T =>
      Ripple.Analysis.BVIntegrationByParts.J a (fun s => B s.toNNReal ω) (t.val : ℝ) := by
    refine (Ripple.Analysis.BVIntegrationByParts.continuousOn_J hT ha hw).comp_continuous
      (NNReal.continuous_coe.comp continuous_subtype_val) (fun t => ⟨NNReal.coe_nonneg _, ?_⟩)
    exact_mod_cast t.2.2
  have hdense : Dense (Set.range rp) := by
    intro x
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq⟩ := SectionFourAssembly.exists_ratIcc_near hT
      (t := ((x.val : ℝ≥0) : ℝ)) ⟨NNReal.coe_nonneg _, by exact_mod_cast x.2.2⟩ hε
    refine ⟨rp q, ⟨q, rfl⟩, ?_⟩
    rw [Subtype.dist_eq, NNReal.dist_eq, hrp q, abs_sub_comm]
    exact hq
  have hext := Continuous.ext_on hdense h2 hJc (by
    rintro _ ⟨q, rfl⟩
    exact h1 q)
  exact fun t => congrFun hext t

end Simple

end Ripple.Kurtz.StrongApprox.DeterministicItoBridge

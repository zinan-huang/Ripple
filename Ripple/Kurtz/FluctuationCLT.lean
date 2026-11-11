import Ripple.Kurtz.Fluctuation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The finite-dimensional fluctuation CLT

The public statements are the remaining statement register in
Ripple/Kurtz/Fluctuation.lean. All model hypotheses are retained.
-/

namespace Ripple.Kurtz

open MeasureTheory ProbabilityTheory Filter Topology Set Finset Matrix
open Ripple.CTMC
open scoped BigOperators ENNReal RealInnerProductSpace InnerProductSpace

noncomputable section

variable {d m : ℕ}

/-! ## Uniform exponential bound -/

private theorem fluctuation_norm_expCompRate_le_imaginary
    {S : Type*} [Fintype S] [DecidableEq S]
    (Q : QMatrix S) {g : ℝ → S → S → ℂ}
    (hRe : ∀ s x y, (g s x y).re = 0)
    (Λ : ℝ) (hΛ : ∀ x, Q.exitRate x ≤ Λ) (s : ℝ) (x : S) :
    ‖Q.expCompRate g s x‖ ≤ 2 * Λ := by
  classical
  unfold QMatrix.expCompRate
  calc
    ‖∑ y ∈ Finset.univ.filter (· ≠ x),
        (Q.rate x y : ℂ) * (Complex.exp (g s x y) - 1)‖
        ≤ ∑ y ∈ Finset.univ.filter (· ≠ x),
          ‖(Q.rate x y : ℂ) * (Complex.exp (g s x y) - 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ y ∈ Finset.univ.filter (· ≠ x), Q.rate x y * 2 := by
      refine Finset.sum_le_sum fun y hy => ?_
      have hq : 0 ≤ Q.rate x y :=
        Q.rate_nonneg x y (Finset.mem_filter.mp hy).2.symm
      have hex : ‖Complex.exp (g s x y)‖ = 1 := by
        rw [Complex.norm_exp, hRe s x y, Real.exp_zero]
      calc
        ‖(Q.rate x y : ℂ) * (Complex.exp (g s x y) - 1)‖ =
            Q.rate x y * ‖Complex.exp (g s x y) - 1‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
        _ ≤ Q.rate x y * (‖Complex.exp (g s x y)‖ + ‖(1 : ℂ)‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) hq
        _ = Q.rate x y * 2 := by
          rw [hex, norm_one]
          norm_num
    _ = 2 * Q.exitRate x := by
      rw [← Finset.sum_mul]
      change Q.exitRate x * 2 = 2 * Q.exitRate x
      ring
    _ ≤ 2 * Λ := mul_le_mul_of_nonneg_left (hΛ x) (by norm_num)

private theorem fluctuation_re_expStepExponent_le_imaginary
    {S : Type*} [Fintype S] [DecidableEq S]
    (Q : QMatrix S) {g : ℝ → S → S → ℂ}
    (hRe : ∀ s x y, (g s x y).re = 0)
    (Λ : ℝ) (hΛ : ∀ x, Q.exitRate x ≤ Λ)
    (T u : ℝ) (x : S) (r : ℝ × S) (hu : 0 ≤ u) (hr : 0 ≤ r.1) :
    (Q.expStepExponent g T u x r).re ≤
      (2 * Λ) * (min (u + r.1) T - min u T) := by
  have hab : min u T ≤ min (u + r.1) T :=
    min_le_min (by linarith) le_rfl
  have hint :
      ‖∫ s in (min u T)..(min (u + r.1) T), Q.expCompRate g s x‖ ≤
        (2 * Λ) * (min (u + r.1) T - min u T) := by
    have hbound :
        ‖∫ s in (min u T)..(min (u + r.1) T), Q.expCompRate g s x‖ ≤
          (2 * Λ) * |min (u + r.1) T - min u T| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s _ => fluctuation_norm_expCompRate_le_imaginary Q hRe Λ hΛ s x)
    rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at hbound
  have hjump :
      (if u + r.1 ≤ T then g (u + r.1) x r.2 else 0).re = 0 := by
    split_ifs
    · exact hRe _ _ _
    · rfl
  have hreal :
      (Q.expStepExponent g T u x r).re =
        -(∫ s in (min u T)..(min (u + r.1) T), Q.expCompRate g s x).re := by
    simp only [QMatrix.expStepExponent, max_eq_left hu, max_eq_left hr,
      Complex.sub_re, hjump, zero_sub]
  rw [hreal]
  exact (show
    -(∫ s in (min u T)..(min (u + r.1) T), Q.expCompRate g s x).re ≤
      ‖∫ s in (min u T)..(min (u + r.1) T), Q.expCompRate g s x‖ from by
        simpa only [Complex.neg_re, norm_neg] using
          (Complex.re_le_norm
            (-(∫ s in (min u T)..(min (u + r.1) T), Q.expCompRate g s x)))).trans
    hint

theorem fluctuation_uniform_imaginary_expSum_bound
    {S : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (Q : QMatrix S) {g : ℝ → S → S → ℂ} {D : Set ℝ}
    (hg : IsExpTilt g D) (hRe : ∀ s x y, (g s x y).re = 0)
    (T Λ : ℝ) (hT : 0 ≤ T) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ x, Q.exitRate x ≤ Λ) (x₀ : S) :
    ∀ᵐ ω ∂Q.canonicalRecordMeasure x₀, ∀ r : ℕ,
      ‖Complex.exp (Q.expSum g T r ω)‖ ≤ Real.exp (2 * Λ * T) := by
  classical
  filter_upwards [Q.canonicalRecordMeasure_all_next_holdingTime_nonneg_ae x₀]
    with ω hω
  have htime (k : ℕ) : 0 ≤ QMatrix.recTime ω k := by
    unfold QMatrix.recTime
    exact Finset.sum_nonneg fun j _ => hω j
  have htime_succ (k : ℕ) :
      QMatrix.recTime ω (k + 1) =
        QMatrix.recTime ω k + (ω (k + 1)).1 := by
    simp only [QMatrix.recTime, Finset.sum_range_succ]
  have hpartial (r : ℕ) :
      (Q.expSum g T r ω).re ≤ (2 * Λ) * min (QMatrix.recTime ω r) T := by
    induction r with
    | zero =>
      simp [QMatrix.expSum, QMatrix.recTime, min_eq_left hT]
    | succ r ih =>
      rw [Q.expSum_succ, Complex.add_re]
      have hstep :=
        fluctuation_re_expStepExponent_le_imaginary Q hRe Λ hΛ T
          (QMatrix.recTime ω r) (ω r).2 (ω (r + 1)) (htime r) (hω r)
      calc
        (Q.expSum g T r ω).re +
            (Q.expStepExponent g T (QMatrix.recTime ω r) (ω r).2 (ω (r + 1))).re
            ≤ (2 * Λ) * min (QMatrix.recTime ω r) T +
              (2 * Λ) *
                (min (QMatrix.recTime ω r + (ω (r + 1)).1) T -
                  min (QMatrix.recTime ω r) T) :=
          add_le_add ih hstep
        _ = (2 * Λ) * min (QMatrix.recTime ω (r + 1)) T := by
          rw [htime_succ r]
          ring
  intro r
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  exact (hpartial r).trans
    (mul_le_mul_of_nonneg_left (min_le_right _ _)
      (mul_nonneg (by norm_num) hΛ0))

/-! ## Weighted path identities -/

private theorem fclt_continuous_dot
    {f g : ℝ → Fin d → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun s => f s ⬝ᵥ g s) := by
  unfold dotProduct
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)

private theorem fclt_hasDerivAt_dot
    {f g : ℝ → Fin d → ℝ} {f' g' : Fin d → ℝ} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun u => f u ⬝ᵥ g u) (f' ⬝ᵥ g s + f s ⬝ᵥ g') s := by
  have h := HasDerivAt.fun_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      (hasDerivAt_pi.mp hf i).mul (hasDerivAt_pi.mp hg i))
  simpa only [dotProduct, Finset.sum_add_distrib] using h

private theorem fclt_hasDerivAt_dot_const
    {f : ℝ → Fin d → ℝ} {f' : Fin d → ℝ} {s : ℝ}
    (hf : HasDerivAt f f' s) (v : Fin d → ℝ) :
    HasDerivAt (fun u => f u ⬝ᵥ v) (f' ⬝ᵥ v) s := by
  simpa only [dotProduct_zero, add_zero] using
    fclt_hasDerivAt_dot hf (hasDerivAt_const (x := s) (c := v))

private theorem fclt_integrableOn_time_state
    (M : DensityDepCTMC d) (ω : M.canonicalRecordΩ)
    (g : ℝ → (Fin d → Fin (M.N + 1)) → ℝ)
    (hg : ∀ x, Continuous (fun u => g u x)) (a b : ℝ) :
    IntegrableOn
      (fun u => g u ((M.canonicalPathMap ω).frozenStateAt u))
      (Icc a b) volume := by
  classical
  have hi (x : Fin d → Fin (M.N + 1)) :
      IntegrableOn
        (fun u => if (M.canonicalPathMap ω).frozenStateAt u = x then g u x else 0)
        (Icc a b) volume := by
    have hmeas : MeasurableSet {u : ℝ | (M.canonicalPathMap ω).frozenStateAt u = x} :=
      measurableSet_eq_fun
        (M.measurable_canonicalPathMap_frozenStateAt_section ω) measurable_const
    refine (((hg x).integrableOn_Icc (μ := volume) (a := a) (b := b)).indicator
      hmeas).congr_fun ?_ measurableSet_Icc
    intro u _
    by_cases hu : (M.canonicalPathMap ω).frozenStateAt u = x <;>
      simp [Set.indicator_apply, hu]
  have hsum := integrable_finsetSum Finset.univ (fun x _ => hi x)
  have heq :
      (fun u => ∑ x : Fin d → Fin (M.N + 1),
        if (M.canonicalPathMap ω).frozenStateAt u = x then g u x else 0) =
      (fun u => g u ((M.canonicalPathMap ω).frozenStateAt u)) := by
    funext u
    simp
  rw [heq] at hsum
  exact hsum

private theorem fclt_time_state_integral_sojourn
    {S E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (path : CTMCPath S) (g : ℝ → S → E)
    (hmono : Monotone path.sojournStart) {n : ℕ} {s : ℝ}
    (hint : IntegrableOn (fun u => g u (path.frozenStateAt u)) (Icc 0 s) volume)
    (hns : path.sojournStart n ≤ s)
    (hk : ∀ k < n, ∀ u ∈ Ico (path.sojournStart k) (path.sojournStart (k + 1)),
      path.frozenStateAt u = path.stateSeq k)
    (hn : ∀ u ∈ Icc (path.sojournStart n) s,
      path.frozenStateAt u = path.stateSeq n) :
    ∫ u in Icc 0 s, g u (path.frozenStateAt u) =
      (∑ k ∈ range n, ∫ u in path.sojournStart k..path.sojournStart (k + 1),
        g u (path.stateSeq k)) +
      ∫ u in path.sojournStart n..s, g u (path.stateSeq n) := by
  have hτ0 : path.sojournStart 0 = 0 := rfl
  have hτnn : ∀ k, 0 ≤ path.sojournStart k :=
    fun k => hτ0 ▸ hmono (Nat.zero_le k)
  have hs0 : 0 ≤ s := (hτnn n).trans hns
  let f : ℝ → E := fun u => g u (path.frozenStateAt u)
  have hII : ∀ a b, 0 ≤ a → a ≤ b → b ≤ s →
      IntervalIntegrable f volume a b := by
    intro a b ha hab hbs
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hint.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc ha hbs))
  have hpiece : ∀ k < n,
      (∫ u in path.sojournStart k..path.sojournStart (k + 1), f u) =
      ∫ u in path.sojournStart k..path.sojournStart (k + 1),
        g u (path.stateSeq k) := by
    intro k hkn
    have hle : path.sojournStart k ≤ path.sojournStart (k + 1) :=
      hmono (Nat.le_succ k)
    have hae : ∀ᵐ u ∂volume, u ∉ ({path.sojournStart (k + 1)} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton _)
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with u hu hmem
    rw [Set.uIoc_of_le hle] at hmem
    have hu' : u ≠ path.sojournStart (k + 1) := by simpa using hu
    exact congrArg (g u)
      (hk k hkn u ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hu'⟩)
  have hlast :
      (∫ u in path.sojournStart n..s, f u) =
      ∫ u in path.sojournStart n..s, g u (path.stateSeq n) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hns] at hu
    exact congrArg (g u) (hn u hu)
  have hprefix : ∀ r ≤ n,
      (∫ u in (0 : ℝ)..path.sojournStart r, f u) =
      ∑ k ∈ range r, ∫ u in path.sojournStart k..path.sojournStart (k + 1),
        g u (path.stateSeq k) := by
    intro r
    induction r with
    | zero => intro _; simp [hτ0]
    | succ r ih =>
      intro hr
      have hrn : r ≤ n := Nat.le_of_succ_le hr
      have hrle : path.sojournStart (r + 1) ≤ s := (hmono hr).trans hns
      rw [Finset.sum_range_succ, ← ih hrn, ← hpiece r (Nat.lt_of_succ_le hr)]
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hII 0 _ le_rfl (hτnn r) ((hmono (Nat.le_succ r)).trans hrle))
        (hII _ _ (hτnn r) (hmono (Nat.le_succ r)) hrle)).symm
  calc
    ∫ u in Icc 0 s, f u = ∫ u in (0 : ℝ)..s, f u := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hs0]
    _ = (∫ u in (0 : ℝ)..path.sojournStart n, f u) +
        ∫ u in path.sojournStart n..s, f u :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hII 0 _ le_rfl (hτnn n) hns)
        (hII _ _ (hτnn n) hns le_rfl)).symm
    _ = _ := by rw [hprefix n le_rfl, hlast]

private theorem fclt_goodRecords_strict_sojourn
    (M : DensityDepCTMC d)
    {x₀ : Fin d → Fin (M.N + 1)} {T : ℝ} {ω : M.canonicalRecordΩ}
    (hg : M.GoodRecords x₀ T ω) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ∃ n : ℕ, (M.canonicalPathMap ω).sojournStart n ≤ s ∧
      (M.canonicalPathMap ω).frozenStateAt s = (ω n).2 ∧
      (∀ k < n, ∀ u ∈ Ico ((M.canonicalPathMap ω).sojournStart k)
        ((M.canonicalPathMap ω).sojournStart (k + 1)),
        (M.canonicalPathMap ω).frozenStateAt u = (ω k).2) ∧
      (∀ u ∈ Icc ((M.canonicalPathMap ω).sojournStart n) s,
        (M.canonicalPathMap ω).frozenStateAt u = (ω n).2) ∧
      (s < (M.canonicalPathMap ω).sojournStart (n + 1) ∨
        M.toQMatrix.IsAbsorbing (ω n).2) := by
  classical
  have hmono : Monotone (M.canonicalPathMap ω).sojournStart := hg.sojournStart_mono
  have hstate : ∀ k, (M.canonicalPathMap ω).stateSeq k = (ω k).2 :=
    fun k => M.canonicalPathMap_stateSeq ω k
  have hIco : ∀ k, ∀ u ∈ Ico ((M.canonicalPathMap ω).sojournStart k)
      ((M.canonicalPathMap ω).sojournStart (k + 1)),
      (M.canonicalPathMap ω).frozenStateAt u = (ω k).2 := by
    intro k u hu
    rw [← hstate]
    exact (M.canonicalPathMap ω).frozenStateAt_eq_stateSeq_of_sojourn hmono k hu.1 hu.2
  by_cases hex : ∃ m, s < (M.canonicalPathMap ω).times m
  · -- a future jump exists: the first one gives the sojourn index
    refine ⟨Nat.find hex, ?_, ?_, fun k _ u hu => hIco k u hu, ?_, Or.inl ?_⟩
    · rcases hfind : Nat.find hex with _ | k
      · exact hs.1
      · have hk : ¬ s < (M.canonicalPathMap ω).times k :=
          Nat.find_min hex (by rw [hfind]; exact Nat.lt_succ_self k)
        exact not_lt.mp hk
    · rw [← hstate]
      exact (M.canonicalPathMap ω).frozenStateAt_eq_stateSeq_of_first_time_gt s _
        (Nat.find_spec hex) fun k hk => Nat.find_min hex (Finset.mem_range.mp hk)
    · intro u hu
      exact hIco _ u ⟨hu.1, lt_of_le_of_lt hu.2 (Nat.find_spec hex)⟩
    · exact Nat.find_spec hex
  · -- no future jump: the chain is absorbed; take the first absorbing index
    push_neg at hex
    have habs : ∃ a, M.toQMatrix.IsAbsorbing (ω a).2 := by
      rcases hg.absorb_or_escape with h | ⟨m, hm⟩
      · exact h
      · exact absurd (lt_of_lt_of_le hm (hex m)) (not_lt.mpr hs.2)
    have hn_abs : M.toQMatrix.IsAbsorbing (ω (Nat.find habs)).2 := Nat.find_spec habs
    have hlt : ∀ k < Nat.find habs, ¬ M.toQMatrix.IsAbsorbing (ω k).2 :=
      fun k hk => Nat.find_min habs hk
    have hτ := hg.sojournStart_eq_of_absorbing hn_abs
    have hτn : (M.canonicalPathMap ω).sojournStart (Nat.find habs) ≤ s := by
      rcases hn' : Nat.find habs with _ | k
      · exact hs.1
      · exact hex k
    have hno : ∀ u, (M.canonicalPathMap ω).sojournStart (Nat.find habs) ≤ u →
        ∀ m, ¬ u < (M.canonicalPathMap ω).times m := by
      intro u hu m
      change ¬ u < (M.canonicalPathMap ω).sojournStart (m + 1)
      rcases le_or_gt (m + 1) (Nat.find habs) with hmn | hmn
      · exact not_lt.mpr ((hmono hmn).trans hu)
      · rw [hτ (m + 1) hmn.le]
        exact not_lt.mpr hu
    have hstable : (M.canonicalPathMap ω).stateSeq (Nat.find habs) =
        (M.canonicalPathMap ω).stateSeq (Nat.find habs + 1) := by
      rw [hstate, hstate, hg.state_eq _ hn_abs]
    have hmin : ∀ k ∈ Finset.range (Nat.find habs),
        (M.canonicalPathMap ω).stateSeq k ≠ (M.canonicalPathMap ω).stateSeq (k + 1) := by
      intro k hk
      rw [hstate, hstate]
      exact (hg.state_ne k (hlt k (Finset.mem_range.mp hk))).symm
    refine ⟨Nat.find habs, hτn, ?_, fun k _ u hu => hIco k u hu, ?_, Or.inr hn_abs⟩
    · rw [← hstate]
      exact (M.canonicalPathMap ω).frozenStateAt_eq_stateSeq_of_first_stable s _ (hno s hτn)
        hstable hmin
    · intro u hu
      rw [← hstate]
      exact (M.canonicalPathMap ω).frozenStateAt_eq_stateSeq_of_first_stable u _ (hno u hu.1)
        hstable hmin

private theorem fclt_goodRecords_weighted_ibp
    (M : DensityDepCTMC d)
    {x₀ : Fin d → Fin (M.N + 1)} {T : ℝ} {ω : M.canonicalRecordΩ}
    (hg : M.GoodRecords x₀ T ω)
    (ψ ψ' φ : ℝ → Fin d → ℝ)
    (hψ : ∀ u, HasDerivAt ψ (ψ' u) u) (hψ' : Continuous ψ')
    {s : ℝ} (hs : s ∈ Icc 0 T)
    (hφ : ∀ u ∈ Icc 0 s, φ u = ψ u) :
    ψ s ⬝ᵥ M.frozenDensityProcess M.canonicalPathMap s ω =
      ψ 0 ⬝ᵥ M.scaledState x₀ +
      fluctuationJumpFunctional M φ s ω +
      ∫ u in Icc 0 s,
        ψ' u ⬝ᵥ M.frozenDensityProcess M.canonicalPathMap u ω := by
  classical
  obtain ⟨n, hτn, hX, hk, hn, halt⟩ :=
    fclt_goodRecords_strict_sojourn M hg hs
  have hmono := hg.sojournStart_mono
  have htime (k : ℕ) :
      QMatrix.recTime ω k = (M.canonicalPathMap ω).sojournStart k :=
    (M.canonicalPathMap_sojournStart ω k).symm
  have hzero : ∀ k, n ≤ k → fluctuationJumpSummand M φ s k ω = 0 := by
    intro k hnk
    rcases halt with hfuture | habs
    · have hgt : s < QMatrix.recTime ω (k + 1) := by
        rw [htime]
        exact hfuture.trans_le (hmono (Nat.succ_le_succ hnk))
      simp [fluctuationJumpSummand, not_le.mpr hgt]
    · have he :
          (ω (k + 1)).2 = (ω k).2 :=
        ((hg.stay_of_absorbing habs) (k + 1) (by omega)).1.trans
          (((hg.stay_of_absorbing habs) k hnk).1.symm)
      simp [fluctuationJumpSummand, he]
  have hpartial : ∀ r, n ≤ r →
      fluctuationJumpPartialSum M φ s r ω =
        fluctuationJumpPartialSum M φ s n ω := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => rfl
    | succ r hr ih =>
      change (∑ k ∈ Finset.range (r + 1), fluctuationJumpSummand M φ s k ω) = _
      rw [Finset.sum_range_succ]
      change fluctuationJumpPartialSum M φ s r ω +
        fluctuationJumpSummand M φ s r ω = _
      rw [ih, hzero r hr, add_zero]
  have hterm (k : ℕ) (hkn : k < n) :
      fluctuationJumpSummand M φ s k ω =
        ψ ((M.canonicalPathMap ω).sojournStart (k + 1)) ⬝ᵥ
          (M.scaledState (ω (k + 1)).2 - M.scaledState (ω k).2) := by
    have hle : (M.canonicalPathMap ω).sojournStart (k + 1) ≤ s :=
      (hmono hkn).trans hτn
    have heq := hφ ((M.canonicalPathMap ω).sojournStart (k + 1))
      ⟨hg.sojournStart_nonneg (k + 1), hle⟩
    simp only [fluctuationJumpSummand, htime, heq]
    by_cases he : (ω (k + 1)).2 = (ω k).2
    · simp [he]
    · rw [if_pos ⟨hle, he⟩]
  have hJ :
      fluctuationJumpFunctional M φ s ω =
        ∑ k ∈ Finset.range n,
          ψ ((M.canonicalPathMap ω).sojournStart (k + 1)) ⬝ᵥ
            (M.scaledState (ω (k + 1)).2 - M.scaledState (ω k).2) := by
    obtain ⟨K, hK⟩ := fluctuation_goodRecords_uniform_finite M hg
    calc
      _ = fluctuationJumpPartialSum M φ s K ω := (hK φ s hs.2).2.2.2
      _ = fluctuationJumpPartialSum M φ s (max K n) ω :=
        ((hK φ s hs.2).2.1 _ (le_max_left _ _)).symm
      _ = fluctuationJumpPartialSum M φ s n ω :=
        hpartial _ (le_max_right _ _)
      _ = _ := by
        unfold fluctuationJumpPartialSum
        exact Finset.sum_congr rfl fun k hk => hterm k (Finset.mem_range.mp hk)
  have hint :
      IntegrableOn
        (fun u => ψ' u ⬝ᵥ
          M.scaledState ((M.canonicalPathMap ω).frozenStateAt u))
        (Icc 0 s) volume :=
    fclt_integrableOn_time_state M ω
      (fun u x => ψ' u ⬝ᵥ M.scaledState x)
      (fun _ => fclt_continuous_dot hψ' continuous_const) 0 s
  have hsplit :=
    fclt_time_state_integral_sojourn (M.canonicalPathMap ω)
      (fun u x => ψ' u ⬝ᵥ M.scaledState x) hmono hint hτn
      (fun k hkn u hu => (hk k hkn u hu).trans
        (M.canonicalPathMap_stateSeq ω k).symm)
      (fun u hu => (hn u hu).trans (M.canonicalPathMap_stateSeq ω n).symm)
  simp only [M.canonicalPathMap_stateSeq] at hsplit
  have hFTC (v : Fin d → ℝ) (a b : ℝ) :
      (∫ u in a..b, ψ' u ⬝ᵥ v) = ψ b ⬝ᵥ v - ψ a ⬝ᵥ v :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => fclt_hasDerivAt_dot_const (hψ u) v)
      ((fclt_continuous_dot hψ' continuous_const).intervalIntegrable a b)
  simp_rw [hFTC] at hsplit
  have htel :
      (∑ k ∈ range n,
        ψ ((M.canonicalPathMap ω).sojournStart (k + 1)) ⬝ᵥ
          (M.scaledState (ω (k + 1)).2 - M.scaledState (ω k).2)) +
      (∑ k ∈ range n,
        (ψ ((M.canonicalPathMap ω).sojournStart (k + 1)) ⬝ᵥ
            M.scaledState (ω k).2 -
          ψ ((M.canonicalPathMap ω).sojournStart k) ⬝ᵥ
            M.scaledState (ω k).2)) =
      ψ ((M.canonicalPathMap ω).sojournStart n) ⬝ᵥ M.scaledState (ω n).2 -
        ψ 0 ⬝ᵥ M.scaledState (ω 0).2 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ k ∈ range n,
          (ψ ((M.canonicalPathMap ω).sojournStart (k + 1)) ⬝ᵥ
              M.scaledState (ω (k + 1)).2 -
            ψ ((M.canonicalPathMap ω).sojournStart k) ⬝ᵥ
              M.scaledState (ω k).2) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [dotProduct_sub]
        ring
      _ = _ := by
        simpa only [M.canonicalPathMap_sojournStart_zero] using
          (Finset.sum_range_sub
            (fun k => ψ ((M.canonicalPathMap ω).sojournStart k) ⬝ᵥ
              M.scaledState (ω k).2) n)
  have hinit : M.scaledState (ω 0).2 = M.scaledState x₀ := by
    rw [hg.record_zero]
  rw [hinit] at htel
  change ψ s ⬝ᵥ M.scaledState ((M.canonicalPathMap ω).frozenStateAt s) =
    ψ 0 ⬝ᵥ M.scaledState x₀ + fluctuationJumpFunctional M φ s ω +
      ∫ u in Icc 0 s,
        ψ' u ⬝ᵥ M.scaledState ((M.canonicalPathMap ω).frozenStateAt u)
  rw [hX, hJ]
  linarith [hsplit, htel]

private theorem fclt_continuous_observation
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (j : Fin m) :
    Continuous (fluctuationObservationTest Γ mf t a j) := by
  unfold fluctuationObservationTest
  exact continuous_finset_sum _ fun i _ =>
    continuous_const.smul (continuous_fluctuationBasisAdjoint Γ mf t hF (j, i))

private theorem fclt_observation_terminal
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (j : Fin m) :
    fluctuationObservationTest Γ mf t a j (t j) = (fun i => a (j, i)) := by
  classical
  ext i
  simp [fluctuationObservationTest,
    fluctuationBasisAdjoint_terminal Γ mf t hF, Pi.single_apply]

private theorem fclt_observation_cutoff_eq
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (j : Fin m)
    {s : ℝ} (hs : s ∈ Icc 0 (t j)) :
    fluctuationObservationCutoffTest Γ mf t a j s =
      fluctuationObservationTest Γ mf t a j s := by
  unfold fluctuationObservationCutoffTest fluctuationObservationTest
  apply Finset.sum_congr rfl
  intro i _
  simp [fluctuationBasisCutoff, hs.2, max_eq_left hs.1]

private theorem fclt_hasDerivAt_observation
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (j : Fin m) (s : ℝ) :
    HasDerivAt (fluctuationObservationTest Γ mf t a j)
      (-((fluctuationLinearization Γ mf s)ᵀ *ᵥ
        fluctuationObservationTest Γ mf t a j s)) s := by
  have h := HasDerivAt.fun_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      HasDerivAt.const_smul (a (j, i))
        (hasDerivAt_fluctuationBasisAdjoint Γ mf t hF (j, i) s))
  have heq :
      (∑ i : Fin d, a (j, i) •
        (-((fluctuationLinearization Γ mf s)ᵀ *ᵥ
          fluctuationBasisAdjoint Γ mf t (j, i) s))) =
      -((fluctuationLinearization Γ mf s)ᵀ *ᵥ
        (∑ i : Fin d, a (j, i) •
          fluctuationBasisAdjoint Γ mf t (j, i) s)) := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.neg_apply,
      Matrix.mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul,
      mul_neg, Finset.sum_neg_distrib]
  simpa only [fluctuationObservationTest, heq] using h

private theorem fclt_continuous_adjoint_derivative
    {A : ℝ → Matrix (Fin d) (Fin d) ℝ} {ψ : ℝ → Fin d → ℝ}
    (hA : Continuous A) (hψ : Continuous ψ) :
    Continuous (fun s => -((A s)ᵀ *ᵥ ψ s)) := by
  apply continuous_pi
  intro i
  change Continuous (fun s => -(∑ k : Fin d, A s k i * ψ s k))
  exact (continuous_finset_sum _ fun k _ =>
    (((continuous_apply i).comp ((continuous_apply k).comp hA)).mul
      ((continuous_apply k).comp hψ))).neg

private theorem fclt_cutoff_drift_time_integrable
    (M : DensityDepCTMC d) {ψ : ℝ → Fin d → ℝ}
    (hψ : Measurable ψ) (hψb : ∃ C : ℝ, ∀ s, ‖ψ s‖ ≤ C)
    (T : ℝ) (ω : M.canonicalRecordΩ) :
    IntegrableOn
      (fun s => ψ s ⬝ᵥ
        M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s ω))
      (Icc 0 T) volume := by
  obtain ⟨C, hψC⟩ := hψb
  have hC : 0 ≤ C := (norm_nonneg (ψ 0)).trans (hψC 0)
  obtain ⟨B, hB⟩ :=
    (isCompact_closedBall (0 : Fin d → ℝ) 1).exists_bound_of_continuousOn
      M.rateSpec.drift_continuous.continuousOn
  have hX : Measurable
      (fun s => M.frozenDensityProcess M.canonicalPathMap s ω) := by
    change Measurable
      (fun s => M.scaledState ((M.canonicalPathMap ω).frozenStateAt s))
    exact (Measurable.of_discrete (f := M.scaledState)).comp
      (M.measurable_canonicalPathMap_frozenStateAt_section ω)
  have hFm : Measurable
      (fun s => M.rateSpec.drift
        (M.frozenDensityProcess M.canonicalPathMap s ω)) :=
    M.rateSpec.drift_continuous.measurable.comp hX
  have hm : Measurable
      (fun s => ψ s ⬝ᵥ
        M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s ω)) := by
    unfold dotProduct
    exact Finset.measurable_sum Finset.univ fun i _ =>
      ((measurable_pi_apply i).comp hψ).mul
        ((measurable_pi_apply i).comp hFm)
  refine IntegrableOn.of_bound
    (measure_Icc_lt_top : volume (Icc (0 : ℝ) T) < ⊤)
    (hm.aestronglyMeasurable (μ := volume.restrict (Icc (0 : ℝ) T)))
    ((d : ℝ) * C * B) ?_
  exact Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]
    have hFs :
        ‖M.rateSpec.drift
          (M.frozenDensityProcess M.canonicalPathMap s ω)‖ ≤ B :=
      hB _ (by simpa using
        M.frozenDensityProcess_norm_le M.canonicalPathMap s ω)
    exact (fluctuation_abs_dot_le _ _).trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_left (hψC s) (Nat.cast_nonneg _))
        hFs (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC))

private theorem fclt_compensated_cutoff_sum_of_goodRecords
    {ι : Type*} [Fintype ι] (M : DensityDepCTMC d)
    (ψ : ι → ℝ → Fin d → ℝ) (τ : ι → ℝ) (T : ℝ)
    (hτ : ∀ j, τ j ≤ T)
    (hzero : ∀ j s, τ j < s → ψ j s = 0)
    (hψ : ∀ j, Measurable (ψ j))
    (hψb : ∀ j, ∃ C : ℝ, ∀ s, ‖ψ j s‖ ≤ C)
    {z : Fin d → Fin (M.N + 1)} {ω : M.canonicalRecordΩ}
    (hg : M.GoodRecords z T ω) :
    fluctuationCompensatedJump M (fun s => ∑ j, ψ j s) T ω =
      ∑ j, fluctuationCompensatedJump M (ψ j) (τ j) ω := by
  classical
  have hsummand (k : ℕ) :
      fluctuationJumpSummand M (fun s => ∑ j, ψ j s) T k ω =
        ∑ j, fluctuationJumpSummand M (ψ j) (τ j) k ω := by
    by_cases hc : (ω (k + 1)).2 ≠ (ω k).2
    · by_cases hs : QMatrix.recTime ω (k + 1) ≤ T
      · have hgate :
            QMatrix.recTime ω (k + 1) ≤ T ∧ (ω (k + 1)).2 ≠ (ω k).2 :=
          ⟨hs, hc⟩
        simp only [fluctuationJumpSummand, if_pos hgate]
        rw [sum_dotProduct]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : QMatrix.recTime ω (k + 1) ≤ τ j
        · rw [if_pos (And.intro hj hc)]
        · have hgatej :
              ¬ (QMatrix.recTime ω (k + 1) ≤ τ j ∧ (ω (k + 1)).2 ≠ (ω k).2) :=
            fun h => hj h.1
          rw [if_neg hgatej, hzero j _ (lt_of_not_ge hj), zero_dotProduct]
      · have hj (j : ι) : ¬ QMatrix.recTime ω (k + 1) ≤ τ j :=
          fun h => hs (h.trans (hτ j))
        simp only [fluctuationJumpSummand, hs, hj, false_and, if_false,
          Finset.sum_const_zero]
    · simp only [fluctuationJumpSummand, hc, and_false, if_false,
        Finset.sum_const_zero]
  have hpartial (r : ℕ) :
      fluctuationJumpPartialSum M (fun s => ∑ j, ψ j s) T r ω =
        ∑ j, fluctuationJumpPartialSum M (ψ j) (τ j) r ω := by
    unfold fluctuationJumpPartialSum
    calc
      (∑ k ∈ Finset.range r,
        fluctuationJumpSummand M (fun s => ∑ j, ψ j s) T k ω) =
          ∑ k ∈ Finset.range r,
            ∑ j, fluctuationJumpSummand M (ψ j) (τ j) k ω :=
        Finset.sum_congr rfl fun k _ => hsummand k
      _ = _ := Finset.sum_comm
  obtain ⟨K, hK⟩ := fluctuation_goodRecords_uniform_finite M hg
  have hJ :
      fluctuationJumpFunctional M (fun s => ∑ j, ψ j s) T ω =
        ∑ j, fluctuationJumpFunctional M (ψ j) (τ j) ω := by
    calc
      fluctuationJumpFunctional M (fun s => ∑ j, ψ j s) T ω =
          fluctuationJumpPartialSum M (fun s => ∑ j, ψ j s) T K ω :=
        (hK _ _ le_rfl).2.2.2
      _ = ∑ j, fluctuationJumpPartialSum M (ψ j) (τ j) K ω := hpartial K
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact ((hK _ _ (hτ j)).2.2.2).symm
  have hcut (j : ι) :
      fluctuationDriftIntegral M (ψ j) T ω =
        fluctuationDriftIntegral M (ψ j) (τ j) ω := by
    have hset : Icc (0 : ℝ) T ∩ Iic (τ j) = Icc 0 (τ j) := by
      ext s
      constructor
      · rintro ⟨hs, hsτ⟩
        exact ⟨hs.1, hsτ⟩
      · intro hs
        exact ⟨⟨hs.1, hs.2.trans (hτ j)⟩, hs.2⟩
    unfold fluctuationDriftIntegral
    calc
      (∫ s in Icc 0 T, ψ j s ⬝ᵥ
        M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s ω)) =
          ∫ s in Icc 0 T, (Iic (τ j)).indicator
            (fun s => ψ j s ⬝ᵥ
              M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s ω)) s := by
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by
          by_cases hs : s ∈ Iic (τ j)
          · simp only [Set.indicator_of_mem hs]
          · simp only [Set.indicator_of_notMem hs,
              hzero j s (lt_of_not_ge hs), zero_dotProduct]
      _ = ∫ s in Icc 0 T ∩ Iic (τ j), ψ j s ⬝ᵥ
          M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s ω) :=
        setIntegral_indicator measurableSet_Iic
      _ = _ := by rw [hset]
  have hD :
      fluctuationDriftIntegral M (fun s => ∑ j, ψ j s) T ω =
        ∑ j, fluctuationDriftIntegral M (ψ j) (τ j) ω := by
    unfold fluctuationDriftIntegral
    simp only [sum_dotProduct]
    rw [integral_finsetSum Finset.univ (fun j _ =>
      fclt_cutoff_drift_time_integrable M (hψ j) (hψb j) T ω)]
    exact Finset.sum_congr rfl fun j _ => hcut j
  unfold fluctuationCompensatedJump
  rw [hJ, hD, Finset.sum_sub_distrib]

section RemainingModelStatements

variable [NeZero d]
variable (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
variable
  (hConservative : ∀ (N : ℕ) (hN : 0 < N),
    (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
  (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
    (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
  (hSolBound : ∀ s : ℝ, 0 ≤ s → ‖mf.sol s‖ ≤ 1)
  (hF : ContDiff ℝ 1 Γ.drift)
  (t : Fin m → ℝ) (ht : ∀ j, 0 ≤ t j)
  (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
  (hz : ∀ n, (fluctuationModel Γ n).InSimplex (z n))
  (v₀ : Fin d → ℝ)
  (hinit : Tendsto
    (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) •
      ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0))
    atTop (𝓝 v₀))
  (a : EuclideanSpace ℝ (Fin m × Fin d))

-- Every signature in this section includes precisely these model hypotheses.
include hConservative hBoundary hSolBound hF ht hz hinit

-- Section-dependent expressions are written out explicitly.


theorem fluctuation_adjoint_integration_by_parts (n : ℕ) :
    ∀ᵐ ω ∂((fluctuationModel Γ n).canonicalRecordMeasure (z n)), ∀ j : Fin m,
      (fun i => a (j, i)) ⬝ᵥ (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap (t j) ω) - mf.sol (t j)) =
        fluctuationObservationTest Γ mf t a j 0 ⬝ᵥ
          ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0) +
        fluctuationCompensatedJump (fluctuationModel Γ n)
          (fluctuationObservationCutoffTest Γ mf t a j) (t j) ω +
        fluctuationRemainder (fluctuationModel Γ n)
          (fluctuationObservationCutoffTest Γ mf t a j)
          mf.extendLeft.sol (t j) ω := by
  classical
  let M := fluctuationModel Γ n
  filter_upwards [M.goodRecords_ae (z n)
    (hConservative (n + 1) (Nat.succ_pos n)) (hz n)
    (fluctuationHorizon_pos t)] with ω hω
  intro j
  let ψ := fluctuationObservationTest Γ mf t a j
  let φ := fluctuationObservationCutoffTest Γ mf t a j
  let D : ℝ → Fin d → ℝ :=
    fun s => -((fluctuationLinearization Γ mf s)ᵀ *ᵥ ψ s)
  let x := mf.extendLeft.sol
  let Y : ℝ → Fin d → ℝ :=
    fun s => M.frozenDensityProcess M.canonicalPathMap s ω
  let B : ℝ → ℝ :=
    fun s => D s ⬝ᵥ x s + ψ s ⬝ᵥ Γ.drift (x s)
  have hψ : Continuous ψ := fclt_continuous_observation Γ mf t hF a j
  have hD : Continuous D :=
    fclt_continuous_adjoint_derivative
      (continuous_fluctuationLinearization Γ mf hF) hψ
  have hderiv : ∀ s, HasDerivAt ψ (D s) s :=
    fclt_hasDerivAt_observation Γ mf t hF a j
  have hφ : ∀ s ∈ Icc 0 (t j), φ s = ψ s :=
    fun s hs => fclt_observation_cutoff_eq Γ mf t a j hs
  have hweighted :
      ψ (t j) ⬝ᵥ Y (t j) =
        ψ 0 ⬝ᵥ M.scaledState (z n) +
        fluctuationJumpFunctional M φ (t j) ω +
        ∫ s in Icc 0 (t j), D s ⬝ᵥ Y s :=
    fclt_goodRecords_weighted_ibp M hω ψ D φ hderiv hD
      ⟨ht j, time_le_fluctuationHorizon t j⟩ hφ
  have hBcont : Continuous B :=
    (fclt_continuous_dot hD mf.extendLeft_continuous).add
      (fclt_continuous_dot hψ
        (Γ.drift_continuous.comp mf.extendLeft_continuous))
  have hODE :
      (∫ s in Icc 0 (t j), B s) =
        ψ (t j) ⬝ᵥ x (t j) - ψ 0 ⬝ᵥ x 0 := by
    calc
      (∫ s in Icc 0 (t j), B s) = ∫ s in (0 : ℝ)..t j, B s := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (ht j)]
      _ = _ := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun s => ψ s ⬝ᵥ x s) (f' := B) ?_
          (hBcont.intervalIntegrable 0 (t j))
        intro s hs
        rw [uIcc_of_le (ht j)] at hs
        exact fclt_hasDerivAt_dot (hderiv s) (mf.extendLeft.sol_ode s hs.1)
  have hA :
      IntegrableOn (fun s => D s ⬝ᵥ Y s) (Icc 0 (t j)) volume :=
    fclt_integrableOn_time_state M ω
      (fun s q => D s ⬝ᵥ M.scaledState q)
      (fun _ => fclt_continuous_dot hD continuous_const) 0 (t j)
  have hB : IntegrableOn B (Icc 0 (t j)) volume :=
    hBcont.integrableOn_Icc
  have hC :
      IntegrableOn (fun s => ψ s ⬝ᵥ Γ.drift (Y s))
        (Icc 0 (t j)) volume :=
    fclt_integrableOn_time_state M ω
      (fun s q => ψ s ⬝ᵥ Γ.drift (M.scaledState q))
      (fun _ => fclt_continuous_dot hψ continuous_const) 0 (t j)
  have hcancel (s : ℝ) (v : Fin d → ℝ) :
      D s ⬝ᵥ v = -(ψ s ⬝ᵥ fderiv ℝ Γ.drift (x s) v) := by
    dsimp only [D]
    rw [neg_dotProduct, Matrix.mulVec_transpose,
      ← Matrix.dotProduct_mulVec, fluctuationLinearization_mulVec]
  have hR :
      fluctuationRemainder M φ x (t j) ω =
        (∫ s in Icc 0 (t j), D s ⬝ᵥ Y s) -
        (∫ s in Icc 0 (t j), B s) +
        (∫ s in Icc 0 (t j), ψ s ⬝ᵥ Γ.drift (Y s)) := by
    change (∫ s in Icc 0 (t j), φ s ⬝ᵥ
      (Γ.drift (Y s) - Γ.drift (x s) -
        fderiv ℝ Γ.drift (x s) (Y s - x s))) = _
    calc
      _ = ∫ s in Icc 0 (t j),
          (D s ⬝ᵥ Y s - B s) + ψ s ⬝ᵥ Γ.drift (Y s) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro s hs
        beta_reduce
        rw [hφ s hs]
        dsimp only [B]
        simp only [dotProduct_sub, map_sub, hcancel]
        ring
      _ = _ := by
        have h1 := integral_add (hA.sub hB) hC
        have h2 := integral_sub hA hB
        simp only [Pi.sub_apply] at h1 h2
        rw [h1, h2]
  have hCeq :
      fluctuationDriftIntegral M φ (t j) ω =
        ∫ s in Icc 0 (t j), ψ s ⬝ᵥ Γ.drift (Y s) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    beta_reduce
    rw [hφ s hs]
    try rfl
  have hterminal : ψ (t j) = (fun i => a (j, i)) :=
    fclt_observation_terminal Γ mf t hF a j
  have hxτ : x (t j) = mf.sol (t j) :=
    mf.extendLeft_sol_of_nonneg (ht j)
  have hx0 : x 0 = mf.sol 0 :=
    mf.extendLeft_sol_of_nonneg le_rfl
  change (fun i => a (j, i)) ⬝ᵥ (Y (t j) - mf.sol (t j)) =
    ψ 0 ⬝ᵥ (M.scaledState (z n) - mf.sol 0) +
      fluctuationCompensatedJump M φ (t j) ω +
      fluctuationRemainder M φ x (t j) ω
  rw [← hterminal, ← hxτ, ← hx0]
  simp only [dotProduct_sub, fluctuationCompensatedJump]
  rw [hCeq]
  linarith [hweighted, hODE, hR]

theorem fluctuation_compensated_cutoff_sum (n : ℕ) :
    ∀ᵐ ω ∂((fluctuationModel Γ n).canonicalRecordMeasure (z n)),
      fluctuationCompensatedJump (fluctuationModel Γ n)
        (fluctuationCombinedTest Γ mf t a) (fluctuationHorizon t) ω =
      ∑ j : Fin m, fluctuationCompensatedJump (fluctuationModel Γ n)
        (fluctuationObservationCutoffTest Γ mf t a j) (t j) ω := by
  classical
  have hcombined :
      fluctuationCombinedTest Γ mf t a =
        (fun s => ∑ j : Fin m,
          fluctuationObservationCutoffTest Γ mf t a j s) := by
    funext s
    change (∑ p : Fin m × Fin d,
      a p • fluctuationBasisCutoff Γ mf t p s) =
        ∑ j : Fin m, ∑ i : Fin d,
          a (j, i) • fluctuationBasisCutoff Γ mf t (j, i) s
    exact Fintype.sum_prod_type _
  have hzero (j : Fin m) (s : ℝ) (hs : t j < s) :
      fluctuationObservationCutoffTest Γ mf t a j s = 0 := by
    simp [fluctuationObservationCutoffTest, fluctuationBasisCutoff, not_le.mpr hs]
  have hbound (j : Fin m) :
      ∃ C : ℝ, ∀ s,
        ‖fluctuationObservationCutoffTest Γ mf t a j s‖ ≤ C := by
    have hb (i : Fin d) :
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ s, ‖fluctuationBasisCutoff Γ mf t (j, i) s‖ ≤ B :=
      exists_fluctuationBasisCutoff_bound Γ mf t hF ht (j, i)
    choose B hB0 hB using hb
    refine ⟨∑ i : Fin d, |a (j, i)| * B i, ?_⟩
    intro s
    change ‖∑ i : Fin d,
      a (j, i) • fluctuationBasisCutoff Γ mf t (j, i) s‖ ≤ _
    refine (norm_sum_le Finset.univ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB i s) (abs_nonneg _)
  filter_upwards [(fluctuationModel Γ n).goodRecords_ae
    (z n) (hConservative (n + 1) (Nat.succ_pos n)) (hz n)
    (fluctuationHorizon_pos t)] with ω hω
  rw [hcombined]
  exact fclt_compensated_cutoff_sum_of_goodRecords (fluctuationModel Γ n)
    (fluctuationObservationCutoffTest Γ mf t a) t (fluctuationHorizon t)
    (time_le_fluctuationHorizon t) hzero
    (measurable_fluctuationObservationCutoffTest Γ mf t hF a) hbound hω

theorem fluctuation_scalar_decomposition (n : ℕ) :
    ∀ᵐ ω ∂((fluctuationModel Γ n).canonicalRecordMeasure (z n)),
      ⟪a, fluctuationVector Γ mf t n ω⟫_ℝ =
        fluctuationInitialTerm Γ mf t z a n +
          fluctuationNoise Γ mf t a n ω + fluctuationError Γ mf t a n ω := by
  classical
  filter_upwards
    [fluctuation_adjoint_integration_by_parts Γ mf
      hConservative hBoundary hSolBound hF t ht z hz v₀ hinit a n,
     fluctuation_compensated_cutoff_sum Γ mf
      hConservative hBoundary hSolBound hF t ht z hz v₀ hinit a n]
    with ω hparts hcuts
  have hinitial :
      (∑ j : Fin m, fluctuationObservationTest Γ mf t a j 0 ⬝ᵥ
        ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0)) =
      fluctuationCombinedTest Γ mf t a 0 ⬝ᵥ
        ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0) := by
    rw [fluctuationCombinedTest, sum_dotProduct, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [fluctuationObservationTest, sum_dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp [fluctuationBasisCutoff, ht j]
  have hscalar :
      ⟪a, fluctuationVector Γ mf t n ω⟫_ℝ =
      Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ∑ j : Fin m, (fun i => a (j, i)) ⬝ᵥ
          (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap (t j) ω) - mf.sol (t j)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [fluctuationVector, WithLp.ofLp_toLp, star_trivial,
      dotProduct, Pi.sub_apply]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum :
      (∑ j : Fin m, (fun i => a (j, i)) ⬝ᵥ
        (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap (t j) ω) - mf.sol (t j))) =
      (∑ j : Fin m, fluctuationObservationTest Γ mf t a j 0 ⬝ᵥ
        ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0)) +
      (∑ j : Fin m, fluctuationCompensatedJump (fluctuationModel Γ n)
        (fluctuationObservationCutoffTest Γ mf t a j) (t j) ω) +
      (∑ j : Fin m, fluctuationRemainder (fluctuationModel Γ n)
        (fluctuationObservationCutoffTest Γ mf t a j)
        mf.extendLeft.sol (t j) ω) := by
    calc
      _ = ∑ j : Fin m,
          (fluctuationObservationTest Γ mf t a j 0 ⬝ᵥ
            ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0) +
          fluctuationCompensatedJump (fluctuationModel Γ n)
            (fluctuationObservationCutoffTest Γ mf t a j) (t j) ω +
          fluctuationRemainder (fluctuationModel Γ n)
            (fluctuationObservationCutoffTest Γ mf t a j)
            mf.extendLeft.sol (t j) ω) :=
        Finset.sum_congr rfl fun j _ => hparts j
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hscalar, hsum, hinitial,
    fluctuationInitialTerm_eq Γ mf t ht z a n,
    fluctuationNoise, fluctuationError, hcuts]
  ring

end RemainingModelStatements

/-! ## Exponential identity -/

private theorem fclt_measurable_finite_eval
    {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {f : ℝ → S → ℂ} {X : ℝ → S}
    (hf : ∀ x, Measurable (fun s => f s x)) (hX : Measurable X) :
    Measurable (fun s => f s (X s)) := by
  classical
  have heq : (fun s => f s (X s)) =
      (fun s => ∑ x : S, if X s = x then f s x else 0) := by
    funext s
    simp
  rw [heq]
  exact Finset.measurable_sum Finset.univ fun x _ =>
    Measurable.ite (measurableSet_eq_fun hX measurable_const) (hf x) measurable_const

private theorem fclt_intervalIntegrable_comp
    {d : ℕ} (M : DensityDepCTMC d)
    {g : ℝ → (Fin d → Fin (M.N + 1)) → (Fin d → Fin (M.N + 1)) → ℂ}
    {D : Set ℝ} (hg : IsExpTilt g D)
    (ω : M.canonicalRecordΩ) (a b : ℝ) :
    IntervalIntegrable
      (fun s => M.toQMatrix.expCompRate g s
        ((M.canonicalPathMap ω).frozenStateAt s)) volume a b := by
  obtain ⟨C, hC⟩ := hg.bdd
  exact intervalIntegrable_of_bounded_measurable
    (fclt_measurable_finite_eval
      (M.toQMatrix.measurable_expCompRate hg.meas)
      (M.measurable_canonicalPathMap_frozenStateAt_section ω))
    (fun s => M.toQMatrix.norm_expCompRate_le hC s _) a b

private theorem fclt_expCompRate_eq_zero_of_absorbing
    {S : Type*} [Fintype S] [DecidableEq S] (Q : QMatrix S)
    (g : ℝ → S → S → ℂ) (s : ℝ) {x : S} (hx : Q.IsAbsorbing x) :
    Q.expCompRate g s x = 0 := by
  classical
  unfold QMatrix.expCompRate
  apply Finset.sum_eq_zero
  intro y hy
  rw [QMatrix.IsAbsorbing.rate_eq_zero Q hx y (Finset.mem_filter.mp hy).2.symm]
  simp

private theorem fclt_compensator_prefix
    {d : ℕ} (M : DensityDepCTMC d)
    {z : Fin d → Fin (M.N + 1)} {T : ℝ} {ω : M.canonicalRecordΩ}
    (hT : 0 ≤ T) (hω : M.GoodRecords z T ω)
    {g : ℝ → (Fin d → Fin (M.N + 1)) → (Fin d → Fin (M.N + 1)) → ℂ}
    {D : Set ℝ} (hg : IsExpTilt g D) (r : ℕ) :
    (∑ k ∈ Finset.range r,
      ∫ s in (min (QMatrix.recTime ω k) T)..(min (QMatrix.recTime ω (k + 1)) T),
        M.toQMatrix.expCompRate g s (ω k).2) =
      ∫ s in (0 : ℝ)..(min (QMatrix.recTime ω r) T),
        M.toQMatrix.expCompRate g s ((M.canonicalPathMap ω).frozenStateAt s) := by
  have hrec (k : ℕ) :
      QMatrix.recTime ω k = (M.canonicalPathMap ω).sojournStart k :=
    (M.canonicalPathMap_sojournStart ω k).symm
  have hmono : Monotone (QMatrix.recTime ω) := by
    intro i j hij
    rw [hrec i, hrec j]
    exact hω.sojournStart_mono hij
  have hpiece (k : ℕ) :
      (∫ s in (min (QMatrix.recTime ω k) T)..(min (QMatrix.recTime ω (k + 1)) T),
        M.toQMatrix.expCompRate g s (ω k).2) =
      ∫ s in (min (QMatrix.recTime ω k) T)..(min (QMatrix.recTime ω (k + 1)) T),
        M.toQMatrix.expCompRate g s ((M.canonicalPathMap ω).frozenStateAt s) := by
    have hle : min (QMatrix.recTime ω k) T ≤
        min (QMatrix.recTime ω (k + 1)) T :=
      min_le_min (hmono (Nat.le_succ k)) le_rfl
    have hae :
        ∀ᵐ s ∂volume, s ∉ ({min (QMatrix.recTime ω (k + 1)) T} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton _)
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with s hs hmem
    rw [Set.uIoc_of_le hle] at hmem
    have hne : s ≠ min (QMatrix.recTime ω (k + 1)) T := by simpa using hs
    have hlt : s < min (QMatrix.recTime ω (k + 1)) T :=
      lt_of_le_of_ne hmem.2 hne
    have hstart : QMatrix.recTime ω k ≤ s := by
      rcases le_total (QMatrix.recTime ω k) T with hk | hk
      · rw [min_eq_left hk] at hmem
        exact hmem.1.le
      · rw [min_eq_right hk] at hmem
        exact False.elim ((not_lt_of_ge (hlt.trans_le (min_le_right _ _)).le) hmem.1)
    have hstop : s < QMatrix.recTime ω (k + 1) :=
      hlt.trans_le (min_le_left _ _)
    have hstate :
        (M.canonicalPathMap ω).frozenStateAt s = (ω k).2 := by
      rw [← M.canonicalPathMap_stateSeq ω k]
      exact (M.canonicalPathMap ω).frozenStateAt_eq_stateSeq_of_sojourn
        hω.sojournStart_mono k
          (by rw [← hrec k]; exact hstart)
          (by rw [← hrec (k + 1)]; exact hstop)
    rw [hstate]
  induction r with
  | zero =>
    simp [QMatrix.recTime, min_eq_left hT]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, hpiece r]
    exact intervalIntegral.integral_add_adjacent_intervals
      (fclt_intervalIntegrable_comp M hg ω 0 (min (QMatrix.recTime ω r) T))
      (fclt_intervalIntegrable_comp M hg ω
        (min (QMatrix.recTime ω r) T) (min (QMatrix.recTime ω (r + 1)) T))

private theorem fclt_compensator_eventually_full
    {d : ℕ} (M : DensityDepCTMC d)
    {z : Fin d → Fin (M.N + 1)} {T : ℝ} {ω : M.canonicalRecordΩ}
    (hT : 0 ≤ T) (hω : M.GoodRecords z T ω)
    {g : ℝ → (Fin d → Fin (M.N + 1)) → (Fin d → Fin (M.N + 1)) → ℂ}
    {D : Set ℝ} (hg : IsExpTilt g D) :
    ∀ᶠ r : ℕ in atTop,
      (∑ k ∈ Finset.range r,
        ∫ s in (min (QMatrix.recTime ω k) T)..(min (QMatrix.recTime ω (k + 1)) T),
          M.toQMatrix.expCompRate g s (ω k).2) =
        ∫ s in Icc 0 T,
          M.toQMatrix.expCompRate g s ((M.canonicalPathMap ω).frozenStateAt s) := by
  obtain ⟨j, hj, _, _, hlast, halt⟩ := hω.exists_sojourn ⟨hT, le_rfl⟩
  have hrec (k : ℕ) :
      QMatrix.recTime ω k = (M.canonicalPathMap ω).sojournStart k :=
    (M.canonicalPathMap_sojournStart ω k).symm
  filter_upwards [eventually_ge_atTop (j + 1)] with r hr
  rw [fclt_compensator_prefix M hT hω hg r]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  rcases halt with hjnext | ⟨hjabs, _⟩
  · have hTr : T ≤ QMatrix.recTime ω r := by
      rw [hrec r]
      exact (hjnext.trans (min_le_left _ _)).trans
        (hω.sojournStart_mono hr)
    rw [min_eq_right hTr]
  · have heq : QMatrix.recTime ω r = (M.canonicalPathMap ω).sojournStart j := by
      rw [hrec r]
      exact hω.sojournStart_eq_of_absorbing hjabs r
        ((Nat.le_succ j).trans hr)
    rw [heq, min_eq_left hj]
    have htail :
        (∫ s in (M.canonicalPathMap ω).sojournStart j..T,
          M.toQMatrix.expCompRate g s ((M.canonicalPathMap ω).frozenStateAt s)) = 0 := by
      calc
        _ = ∫ _s in (M.canonicalPathMap ω).sojournStart j..T, (0 : ℂ) := by
          refine intervalIntegral.integral_congr fun s hs => ?_
          rw [Set.uIcc_of_le hj] at hs
          rw [hlast s hs]
          exact fclt_expCompRate_eq_zero_of_absorbing M.toQMatrix g s hjabs
        _ = 0 := by simp
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (fclt_intervalIntegrable_comp M hg ω 0 ((M.canonicalPathMap ω).sojournStart j))
      (fclt_intervalIntegrable_comp M hg ω ((M.canonicalPathMap ω).sojournStart j) T)
    rw [htail, add_zero] at hadd
    exact hadd

private theorem fclt_dot_drift
    {d : ℕ} (Γ : RateSpec d) (b x : Fin d → ℝ) :
    b ⬝ᵥ Γ.drift x =
      ∑ ℓ ∈ Γ.jumps, Γ.rate ℓ x * (b ⬝ᵥ (fun i => (ℓ i : ℝ))) := by
  classical
  unfold dotProduct RateSpec.drift
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem fclt_compRate_split
    {d : ℕ} (M : DensityDepCTMC d)
    (hBC : M.BoundaryCompatibleOnSimplex)
    {x : Fin d → Fin (M.N + 1)} (hx : M.InSimplex x) (b : Fin d → ℝ) :
    (∑ y ∈ Finset.univ.filter (fun y => y ≠ x),
      (M.toQMatrix.rate x y : ℂ) *
        (Complex.exp
          (Complex.I * (((b ⬝ᵥ (fun i => (y i : ℝ) - (x i : ℝ))) /
            Real.sqrt (M.N : ℝ) : ℝ) : ℂ)) - 1)) =
      (Complex.I * (Real.sqrt (M.N : ℝ) : ℂ)) *
        ((b ⬝ᵥ M.rateSpec.drift (M.scaledState x) : ℝ) : ℂ) +
      (M.N : ℂ) * ∑ ℓ ∈ M.rateSpec.jumps,
        (M.rateSpec.rate ℓ (M.scaledState x) : ℂ) *
          fluctuationZeta
            ((b ⬝ᵥ (fun i => (ℓ i : ℝ))) / Real.sqrt (M.N : ℝ)) := by
  classical
  have hN : 0 < (M.N : ℝ) := Nat.cast_pos.mpr M.hN
  have hsqrt : (Real.sqrt (M.N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hN))
  have hsq : (M.N : ℂ) = (Real.sqrt (M.N : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast (Real.sq_sqrt hN.le).symm
  have hscale (q : ℝ) :
      (M.N : ℂ) * (Complex.I * ((q / Real.sqrt (M.N : ℝ) : ℝ) : ℂ)) =
        (Complex.I * (Real.sqrt (M.N : ℝ) : ℂ)) * (q : ℂ) := by
    rw [Complex.ofReal_div, hsq]
    field_simp [hsqrt] <;> ring
  rw [fluctuation_nonlinear_compensator_rewrite M hBC hx b
    (fun q => Complex.exp (Complex.I * (q : ℂ)) - 1) (by simp)]
  calc
    (M.N : ℂ) * ∑ ℓ ∈ M.rateSpec.jumps,
        (M.rateSpec.rate ℓ (M.scaledState x) : ℂ) *
          (Complex.exp
            (Complex.I * (((b ⬝ᵥ (fun i => (ℓ i : ℝ))) /
              Real.sqrt (M.N : ℝ) : ℝ) : ℂ)) - 1) =
        (M.N : ℂ) * ∑ ℓ ∈ M.rateSpec.jumps,
          (M.rateSpec.rate ℓ (M.scaledState x) : ℂ) *
            (Complex.I * (((b ⬝ᵥ (fun i => (ℓ i : ℝ))) /
              Real.sqrt (M.N : ℝ) : ℝ) : ℂ) +
              fluctuationZeta
                ((b ⬝ᵥ (fun i => (ℓ i : ℝ))) / Real.sqrt (M.N : ℝ))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro ℓ _
      unfold fluctuationZeta
      ring
    _ =
        (M.N : ℂ) * (∑ ℓ ∈ M.rateSpec.jumps,
          (M.rateSpec.rate ℓ (M.scaledState x) : ℂ) *
            (Complex.I * (((b ⬝ᵥ (fun i => (ℓ i : ℝ))) /
              Real.sqrt (M.N : ℝ) : ℝ) : ℂ))) +
        (M.N : ℂ) * ∑ ℓ ∈ M.rateSpec.jumps,
          (M.rateSpec.rate ℓ (M.scaledState x) : ℂ) *
            fluctuationZeta
              ((b ⬝ᵥ (fun i => (ℓ i : ℝ))) / Real.sqrt (M.N : ℝ)) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      rw [fclt_dot_drift, Complex.ofReal_sum]
      simp only [Finset.mul_sum, Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro ℓ _
      calc
        (M.N : ℂ) * ((M.rateSpec.rate ℓ (M.scaledState x) : ℂ) *
            (Complex.I * (((b ⬝ᵥ (fun i => (ℓ i : ℝ))) /
              Real.sqrt (M.N : ℝ) : ℝ) : ℂ))) =
            (M.rateSpec.rate ℓ (M.scaledState x) : ℂ) *
              ((M.N : ℂ) * (Complex.I *
                (((b ⬝ᵥ (fun i => (ℓ i : ℝ))) /
                  Real.sqrt (M.N : ℝ) : ℝ) : ℂ))) := by ring
        _ = (M.rateSpec.rate ℓ (M.scaledState x) : ℂ) *
            ((Complex.I * (Real.sqrt (M.N : ℝ) : ℂ)) *
              ((b ⬝ᵥ (fun i => (ℓ i : ℝ)) : ℝ) : ℂ)) := by
          rw [hscale]
        _ = _ := by ring

private theorem fclt_integrableOn_drift
    {d : ℕ} (M : DensityDepCTMC d) {ψ : ℝ → Fin d → ℝ}
    (hψ : Measurable ψ) (hψb : ∃ C : ℝ, ∀ s, ‖ψ s‖ ≤ C)
    (T : ℝ) (ω : M.canonicalRecordΩ) :
    IntegrableOn
      (fun s => ((ψ s ⬝ᵥ M.rateSpec.drift
        (M.frozenDensityProcess M.canonicalPathMap s ω) : ℝ) : ℂ))
      (Icc 0 T) := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) :=
    ⟨by simpa using (measure_Icc_lt_top : volume (Icc (0 : ℝ) T) < ⊤)⟩
  obtain ⟨C, hC⟩ := hψb
  have hC0 : 0 ≤ C := (norm_nonneg (ψ 0)).trans (hC 0)
  let B : ℝ :=
    ∑ x : Fin d → Fin (M.N + 1), ‖M.rateSpec.drift (M.scaledState x)‖
  have hB (x : Fin d → Fin (M.N + 1)) :
      ‖M.rateSpec.drift (M.scaledState x)‖ ≤ B :=
    Finset.single_le_sum
      (f := fun y : Fin d → Fin (M.N + 1) =>
        ‖M.rateSpec.drift (M.scaledState y)‖)
      (fun y _ => norm_nonneg _) (Finset.mem_univ x)
  have hmeas :
      Measurable (fun s => ((ψ s ⬝ᵥ M.rateSpec.drift
        (M.frozenDensityProcess M.canonicalPathMap s ω) : ℝ) : ℂ)) := by
    refine fclt_measurable_finite_eval
      (f := fun (s : ℝ) (x : Fin d → Fin (M.N + 1)) =>
        ((ψ s ⬝ᵥ M.rateSpec.drift (M.scaledState x) : ℝ) : ℂ))
      (X := fun s => (M.canonicalPathMap ω).frozenStateAt s) ?_
      (M.measurable_canonicalPathMap_frozenStateAt_section ω)
    intro x
    apply Complex.measurable_ofReal.comp
    unfold dotProduct
    exact Finset.measurable_sum Finset.univ fun i _ =>
      ((measurable_pi_apply i).comp hψ).mul measurable_const
  refine (integrable_const ((d : ℝ) * C * B)).mono' hmeas.aestronglyMeasurable ?_
  apply Eventually.of_forall
  intro s
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (fluctuation_abs_dot_le _ _).trans
    (mul_le_mul
      (mul_le_mul_of_nonneg_left (hC s) (Nat.cast_nonneg _))
      (hB ((M.canonicalPathMap ω).frozenStateAt s))
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC0))

private theorem fclt_sqrt_scaled_dot
    {d : ℕ} (M : DensityDepCTMC d) (b : Fin d → ℝ)
    (x y : Fin d → Fin (M.N + 1)) :
    Real.sqrt (M.N : ℝ) * (b ⬝ᵥ (M.scaledState y - M.scaledState x)) =
      (b ⬝ᵥ (fun i => (y i : ℝ) - (x i : ℝ))) / Real.sqrt (M.N : ℝ) := by
  have hN : 0 < (M.N : ℝ) := Nat.cast_pos.mpr M.hN
  have hs : 0 < Real.sqrt (M.N : ℝ) := Real.sqrt_pos.mpr hN
  have hdot :
      b ⬝ᵥ (M.scaledState y - M.scaledState x) =
        (b ⬝ᵥ (fun i => (y i : ℝ) - (x i : ℝ))) / (M.N : ℝ) := by
    unfold dotProduct
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    change b i * ((y i : ℝ) / (M.N : ℝ) - (x i : ℝ) / (M.N : ℝ)) =
      (b i * ((y i : ℝ) - (x i : ℝ))) / (M.N : ℝ)
    ring
  rw [hdot]
  apply (eq_div_iff (ne_of_gt hs)).mpr
  calc
    Real.sqrt (M.N : ℝ) *
        ((b ⬝ᵥ (fun i => (y i : ℝ) - (x i : ℝ))) / (M.N : ℝ)) *
        Real.sqrt (M.N : ℝ) =
      (Real.sqrt (M.N : ℝ)) ^ 2 *
        ((b ⬝ᵥ (fun i => (y i : ℝ) - (x i : ℝ))) / (M.N : ℝ)) := by ring
    _ = (M.N : ℝ) *
        ((b ⬝ᵥ (fun i => (y i : ℝ) - (x i : ℝ))) / (M.N : ℝ)) := by
      rw [Real.sq_sqrt hN.le]
    _ = _ := by field_simp [ne_of_gt hN]

private theorem fclt_expSum_eq
    {d m : ℕ} (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (a : EuclideanSpace ℝ (Fin m × Fin d)) (n r : ℕ)
    (ω : (fluctuationModel Γ n).canonicalRecordΩ)
    (hnn : ∀ k, 0 ≤ (ω (k + 1)).1) :
    (fluctuationModel Γ n).toQMatrix.expSum
        (fluctuationTilt Γ mf t a n) (fluctuationHorizon t) r ω =
      (Complex.I * (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ)) *
        (fluctuationJumpPartialSum (fluctuationModel Γ n)
          (fluctuationCombinedTest Γ mf t a) (fluctuationHorizon t) r ω : ℂ) -
      ∑ k ∈ Finset.range r,
        ∫ s in (min (QMatrix.recTime ω k) (fluctuationHorizon t))..
            (min (QMatrix.recTime ω (k + 1)) (fluctuationHorizon t)),
          (fluctuationModel Γ n).toQMatrix.expCompRate
            (fluctuationTilt Γ mf t a n) s (ω k).2 := by
  classical
  have hτ (k : ℕ) : 0 ≤ QMatrix.recTime ω k :=
    Finset.sum_nonneg fun j _ => hnn j
  have hnext (k : ℕ) :
      QMatrix.recTime ω (k + 1) = QMatrix.recTime ω k + (ω (k + 1)).1 := by
    simp only [QMatrix.recTime, Finset.sum_range_succ]
  have hjump (k : ℕ) :
      (if QMatrix.recTime ω (k + 1) ≤ fluctuationHorizon t then
        fluctuationTilt Γ mf t a n (QMatrix.recTime ω (k + 1))
          (ω k).2 (ω (k + 1)).2 else 0) =
      (Complex.I * (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ)) *
        (fluctuationJumpSummand (fluctuationModel Γ n)
          (fluctuationCombinedTest Γ mf t a) (fluctuationHorizon t) k ω : ℂ) := by
    by_cases htime : QMatrix.recTime ω (k + 1) ≤ fluctuationHorizon t
    · by_cases hstate : (ω (k + 1)).2 ≠ (ω k).2
      · simp only [if_pos htime, fluctuationJumpSummand,
          if_pos (And.intro htime hstate), fluctuationTilt]
        simpa only [fluctuationModel, Complex.ofReal_mul, mul_assoc] using
          (congrArg (fun x : ℝ => Complex.I * (x : ℂ))
            (fclt_sqrt_scaled_dot (fluctuationModel Γ n)
              (fluctuationCombinedTest Γ mf t a (QMatrix.recTime ω (k + 1)))
              (ω k).2 (ω (k + 1)).2).symm)
      · have heq : (ω (k + 1)).2 = (ω k).2 := not_ne_iff.mp hstate
        simp [htime, fluctuationJumpSummand, heq, fluctuationTilt, dotProduct]
    · simp [htime, fluctuationJumpSummand]
  calc
    _ = ∑ k ∈ Finset.range r,
        ((Complex.I * (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ)) *
          (fluctuationJumpSummand (fluctuationModel Γ n)
            (fluctuationCombinedTest Γ mf t a) (fluctuationHorizon t) k ω : ℂ) -
          ∫ s in (min (QMatrix.recTime ω k) (fluctuationHorizon t))..
              (min (QMatrix.recTime ω (k + 1)) (fluctuationHorizon t)),
            (fluctuationModel Γ n).toQMatrix.expCompRate
              (fluctuationTilt Γ mf t a n) s (ω k).2) := by
      unfold QMatrix.expSum
      apply Finset.sum_congr rfl
      intro k _
      unfold QMatrix.expStepExponent
      rw [max_eq_left (hτ k), max_eq_left (hnn k), ← hnext k, hjump k]
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [fluctuationJumpPartialSum, Complex.ofReal_sum, Finset.mul_sum]

private theorem fclt_integral_comp_split
    {d m : ℕ} (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
    (t : Fin m → ℝ) (hF : ContDiff ℝ 1 Γ.drift) (ht : ∀ j, 0 ≤ t j)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (n : ℕ)
    (hBC : (fluctuationModel Γ n).BoundaryCompatibleOnSimplex)
    {z : Fin d → Fin (n + 1 + 1)}
    {ω : (fluctuationModel Γ n).canonicalRecordΩ}
    (hω : (fluctuationModel Γ n).GoodRecords z (fluctuationHorizon t) ω) :
    (∫ s in Icc 0 (fluctuationHorizon t),
      (fluctuationModel Γ n).toQMatrix.expCompRate (fluctuationTilt Γ mf t a n) s
        (((fluctuationModel Γ n).canonicalPathMap ω).frozenStateAt s)) =
      (Complex.I * (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ)) *
        (fluctuationDriftIntegral (fluctuationModel Γ n)
          (fluctuationCombinedTest Γ mf t a) (fluctuationHorizon t) ω : ℂ) +
      fluctuationNonlinearCompensator Γ mf t a n ω := by
  let M := fluctuationModel Γ n
  let H := fluctuationHorizon t
  let ψ := fluctuationCombinedTest Γ mf t a
  let c : ℂ := Complex.I * (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ)
  let F : ℝ → ℂ := fun s =>
    M.toQMatrix.expCompRate (fluctuationTilt Γ mf t a n) s
      ((M.canonicalPathMap ω).frozenStateAt s)
  let L : ℝ → ℂ := fun s =>
    c * ((ψ s ⬝ᵥ M.rateSpec.drift
      (M.frozenDensityProcess M.canonicalPathMap s ω) : ℝ) : ℂ)
  let R : ℝ → ℂ := fun s =>
    ((n + 1 : ℕ) : ℂ) *
      ∑ ℓ ∈ Γ.jumps,
        (Γ.rate ℓ (M.frozenDensityProcess M.canonicalPathMap s ω) : ℂ) *
          fluctuationZeta
            (fluctuationPairing ψ ℓ s / Real.sqrt ((n + 1 : ℕ) : ℝ))
  have hH : 0 ≤ H := (fluctuationHorizon_pos t).le
  have htilt := fluctuationTilt_isExpTilt Γ mf t hF ht a n
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 H) : F s = L s + R s := by
    have hh := fclt_compRate_split M hBC
      (hω.inSimplex_frozenStateAt hs) (ψ s)
    simpa only [F, L, R, c, M, ψ, QMatrix.expCompRate,
      fluctuationTilt, fluctuationPairing] using hh
  have hFI : IntegrableOn F (Icc 0 H) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hH).mp
      (fclt_intervalIntegrable_comp M htilt ω 0 H)
  obtain ⟨C, _, hC⟩ := exists_fluctuationCombinedTest_bound Γ mf t hF ht a
  have hLI : IntegrableOn L (Icc 0 H) :=
    (fclt_integrableOn_drift M
      (measurable_fluctuationCombinedTest Γ mf t hF a) ⟨C, hC⟩ H ω).const_mul c
  have hR :
      fluctuationNonlinearCompensator Γ mf t a n ω =
        (∫ s in Icc 0 H, F s) -
          c * (fluctuationDriftIntegral M ψ H ω : ℂ) := by
    change (∫ s in Icc 0 H, R s) = _
    calc
      (∫ s in Icc 0 H, R s) = ∫ s in Icc 0 H, F s - L s := by
        apply integral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
        apply (eq_sub_iff_add_eq).mpr
        simpa only [add_comm] using (hpoint s hs).symm
      _ = (∫ s in Icc 0 H, F s) - ∫ s in Icc 0 H, L s :=
        integral_sub hFI hLI
      _ = _ := by
        simp only [L, integral_const_mul, _root_.integral_complex_ofReal,
          fluctuationDriftIntegral]
  change (∫ s in Icc 0 H, F s) =
    c * (fluctuationDriftIntegral M ψ H ω : ℂ) +
      fluctuationNonlinearCompensator Γ mf t a n ω
  rw [hR]
  ring

section RemainingModelStatements

variable [NeZero d]
variable (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
variable
  (hConservative : ∀ (N : ℕ) (hN : 0 < N),
    (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
  (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
    (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
  (hSolBound : ∀ s : ℝ, 0 ≤ s → ‖mf.sol s‖ ≤ 1)
  (hF : ContDiff ℝ 1 Γ.drift)
  (t : Fin m → ℝ) (ht : ∀ j, 0 ≤ t j)
  (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
  (hz : ∀ n, (fluctuationModel Γ n).InSimplex (z n))
  (v₀ : Fin d → ℝ)
  (hinit : Tendsto
    (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) •
      ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0))
    atTop (𝓝 v₀))
  (a : EuclideanSpace ℝ (Fin m × Fin d))

-- Every signature in this section includes precisely these model hypotheses.
include hConservative hBoundary hSolBound hF ht hz hinit

-- Section-dependent expressions are written out explicitly.


theorem fluctuation_expSum_tendsto (n : ℕ) :
    ∀ᵐ ω ∂((fluctuationModel Γ n).canonicalRecordMeasure (z n)),
      Tendsto
        (fun r => (fluctuationModel Γ n).toQMatrix.expSum
          (fluctuationTilt Γ mf t a n) (fluctuationHorizon t) r ω)
        atTop
        (𝓝 (Complex.I * (fluctuationNoise Γ mf t a n ω : ℂ) -
          fluctuationNonlinearCompensator Γ mf t a n ω)) := by
  have htilt := fluctuationTilt_isExpTilt Γ mf t hF ht a n
  have hBC : (fluctuationModel Γ n).BoundaryCompatibleOnSimplex :=
    hBoundary (n + 1) (Nat.succ_pos n)
  filter_upwards [(fluctuationModel Γ n).goodRecords_ae (z n)
    (hConservative (n + 1) (Nat.succ_pos n)) (hz n)
    (fluctuationHorizon_pos t)] with ω hω
  obtain ⟨K, hK⟩ :=
    fluctuation_goodRecords_uniform_finite (fluctuationModel Γ n) hω
  obtain ⟨_, hpartial, _, hfunctional⟩ :=
    hK (fluctuationCombinedTest Γ mf t a) (fluctuationHorizon t) le_rfl
  have hcomp := fclt_compensator_eventually_full (fluctuationModel Γ n)
    (fluctuationHorizon_pos t).le hω htilt
  have hsplit := fclt_integral_comp_split Γ mf t hF ht a n hBC hω
  have hevent :
      ∀ᶠ r : ℕ in atTop,
        (fluctuationModel Γ n).toQMatrix.expSum
            (fluctuationTilt Γ mf t a n) (fluctuationHorizon t) r ω =
          Complex.I * (fluctuationNoise Γ mf t a n ω : ℂ) -
            fluctuationNonlinearCompensator Γ mf t a n ω := by
    filter_upwards [hcomp, eventually_ge_atTop K] with r hcomp_r hr
    have hjump_r :
        fluctuationJumpPartialSum (fluctuationModel Γ n)
            (fluctuationCombinedTest Γ mf t a) (fluctuationHorizon t) r ω =
          fluctuationJumpFunctional (fluctuationModel Γ n)
            (fluctuationCombinedTest Γ mf t a) (fluctuationHorizon t) ω :=
      (hpartial r hr).trans hfunctional.symm
    rw [fclt_expSum_eq Γ mf t a n r ω hω.hold_nonneg, hcomp_r, hjump_r, hsplit]
    unfold fluctuationNoise fluctuationCompensatedJump
    simp only [Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  exact tendsto_const_nhds.congr' (hevent.mono fun _ hr => hr.symm)

theorem fluctuation_exponential_identity (n : ℕ) :
    (∫ ω, Complex.exp
      (Complex.I * (fluctuationNoise Γ mf t a n ω : ℂ) -
        fluctuationNonlinearCompensator Γ mf t a n ω) ∂((fluctuationModel Γ n).canonicalRecordMeasure (z n))) = 1 := by
  let Q := (fluctuationModel Γ n).toQMatrix
  have htilt := fluctuationTilt_isExpTilt Γ mf t hF ht a n
  have hΛ0 : 0 ≤ Q.uniformRate :=
    (Q.exitRate_nonneg (z n)).trans (Q.exitRate_le_uniformRate (z n))
  have hbound := fluctuation_uniform_imaginary_expSum_bound Q htilt
    (fluctuationTilt_re Γ mf t a n) (fluctuationHorizon t) Q.uniformRate
    (fluctuationHorizon_pos t).le hΛ0 Q.exitRate_le_uniformRate (z n)
  have hsumlimit := fluctuation_expSum_tendsto
    (Γ := Γ) (mf := mf) (hConservative := hConservative)
    (hBoundary := hBoundary) (hSolBound := hSolBound) (hF := hF)
    (t := t) (ht := ht) (z := z) (hz := hz) (v₀ := v₀)
    (hinit := hinit) (a := a) (n := n)
  have hlimit :
      Tendsto
        (fun r => ∫ ω, Complex.exp (Q.expSum (fluctuationTilt Γ mf t a n) (fluctuationHorizon t) r ω)
          ∂((fluctuationModel Γ n).canonicalRecordMeasure (z n)))
        atTop
        (𝓝 (∫ ω, Complex.exp
          (Complex.I * (fluctuationNoise Γ mf t a n ω : ℂ) -
            fluctuationNonlinearCompensator Γ mf t a n ω) ∂((fluctuationModel Γ n).canonicalRecordMeasure (z n)))) :=
    tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (2 * Q.uniformRate * (fluctuationHorizon t)))
      (fun r =>
        (Complex.measurable_exp.comp (Q.measurable_expSum htilt (fluctuationHorizon t) r)).aestronglyMeasurable)
      (integrable_const _)
      (fun r => hbound.mono fun ω hω => hω r)
      (hsumlimit.mono fun ω hω => (Complex.continuous_exp.tendsto _).comp hω)
  have hone (r : ℕ) :
      (∫ ω, Complex.exp (Q.expSum (fluctuationTilt Γ mf t a n) (fluctuationHorizon t) r ω) ∂((fluctuationModel Γ n).canonicalRecordMeasure (z n))) = 1 :=
    Q.integral_cexp_expSum htilt (fluctuationHorizon t) (z n) r
  have hlimit_one :
      Tendsto
        (fun r => ∫ ω, Complex.exp (Q.expSum (fluctuationTilt Γ mf t a n) (fluctuationHorizon t) r ω)
          ∂((fluctuationModel Γ n).canonicalRecordMeasure (z n)))
        atTop (𝓝 (1 : ℂ)) := by
    have hc : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 (1 : ℂ)) :=
      tendsto_const_nhds
    simpa only [hone] using hc
  exact tendsto_nhds_unique hlimit hlimit_one

end RemainingModelStatements

/-! ## Taylor bounds and analytic helpers -/

private theorem fluctuation_zeta_scaled_hasDerivAt (r u : ℝ) :
    HasDerivAt (fun s : ℝ => fluctuationZeta (r * s))
      ((Complex.I * (r : ℂ)) *
        (Complex.exp (Complex.I * ((r * u : ℝ) : ℂ)) - 1)) u := by
  have hlin :
      HasDerivAt (fun s : ℝ => Complex.I * ((r * s : ℝ) : ℂ))
        (Complex.I * (r : ℂ)) u := by
    simpa using (((hasDerivAt_id u).const_mul r).ofReal_comp.const_mul Complex.I)
  convert (hlin.cexp.sub_const 1).sub hlin using 1 <;>
    dsimp [fluctuationZeta] <;> ring

theorem fluctuationZeta_bound (r : ℝ) :
    ‖fluctuationZeta r‖ ≤ r ^ 2 / 2 := by
  have hcont : Continuous (fun s : ℝ =>
      (Complex.I * (r : ℂ)) *
        (Complex.exp (Complex.I * ((r * s : ℝ) : ℂ)) - 1)) := by
    fun_prop
  have hint :
      (∫ s in (0 : ℝ)..1, (Complex.I * (r : ℂ)) *
        (Complex.exp (Complex.I * ((r * s : ℝ) : ℂ)) - 1)) =
          fluctuationZeta r := by
    simpa [fluctuationZeta] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := 1)
        (fun s _ => fluctuation_zeta_scaled_hasDerivAt r s)
        (hcont.intervalIntegrable 0 1))
  rw [← hint]
  calc
    ‖∫ s in (0 : ℝ)..1, (Complex.I * (r : ℂ)) *
        (Complex.exp (Complex.I * ((r * s : ℝ) : ℂ)) - 1)‖
        ≤ ∫ s in (0 : ℝ)..1, |r| ^ 2 * s := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      · exact Eventually.of_forall fun s hs => by
          calc
            ‖(Complex.I * (r : ℂ)) *
                (Complex.exp (Complex.I * ((r * s : ℝ) : ℂ)) - 1)‖ =
                |r| * ‖Complex.exp (Complex.I * ((r * s : ℝ) : ℂ)) - 1‖ := by
              simp only [norm_mul, Complex.norm_I, Complex.norm_real,
                Real.norm_eq_abs, one_mul]
            _ ≤ |r| * |r * s| :=
              mul_le_mul_of_nonneg_left
                (by simpa only [Real.norm_eq_abs] using
                  (Real.norm_exp_I_mul_ofReal_sub_one_le (x := r * s)))
                (abs_nonneg r)
            _ = |r| ^ 2 * s := by
              rw [abs_mul, abs_of_nonneg hs.1.le]
              ring
      · exact (by fun_prop : Continuous (fun s : ℝ => |r| ^ 2 * s)).intervalIntegrable 0 1
    _ = r ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul, _root_.integral_id, sq_abs]
      norm_num <;> ring

private theorem fluctuation_zeta_cubic_scaled_hasDerivAt (r u : ℝ) :
    HasDerivAt
      (fun s : ℝ => fluctuationZeta (r * s) + (((r * s : ℝ) : ℂ) ^ 2) / 2)
      ((Complex.I * (r : ℂ)) * fluctuationZeta (r * u)) u := by
  have hlin :
      HasDerivAt (fun s : ℝ => ((r * s : ℝ) : ℂ)) (r : ℂ) u := by
    simpa using ((hasDerivAt_id u).const_mul r).ofReal_comp
  convert (fluctuation_zeta_scaled_hasDerivAt r u).add
    ((hlin.pow 2).div_const (2 : ℂ)) using 1 <;>
    dsimp [fluctuationZeta] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem fluctuationZeta_cubic_bound (r : ℝ) :
    ‖fluctuationZeta r + ((r : ℂ) ^ 2) / 2‖ ≤ |r| ^ 3 / 6 := by
  have hcont : Continuous (fun s : ℝ =>
      (Complex.I * (r : ℂ)) * fluctuationZeta (r * s)) := by
    unfold fluctuationZeta
    fun_prop
  have hint :
      (∫ s in (0 : ℝ)..1, (Complex.I * (r : ℂ)) * fluctuationZeta (r * s)) =
        fluctuationZeta r + ((r : ℂ) ^ 2) / 2 := by
    simpa [fluctuationZeta] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := 1)
        (fun s _ => fluctuation_zeta_cubic_scaled_hasDerivAt r s)
        (hcont.intervalIntegrable 0 1))
  rw [← hint]
  calc
    ‖∫ s in (0 : ℝ)..1, (Complex.I * (r : ℂ)) * fluctuationZeta (r * s)‖
        ≤ ∫ s in (0 : ℝ)..1, (|r| ^ 3 / 2) * s ^ 2 := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      · exact Eventually.of_forall fun s _ => by
          calc
            ‖(Complex.I * (r : ℂ)) * fluctuationZeta (r * s)‖ =
                |r| * ‖fluctuationZeta (r * s)‖ := by
              simp only [norm_mul, Complex.norm_I, Complex.norm_real,
                Real.norm_eq_abs, one_mul]
            _ ≤ |r| * ((r * s) ^ 2 / 2) :=
              mul_le_mul_of_nonneg_left (fluctuationZeta_bound (r * s)) (abs_nonneg r)
            _ = (|r| ^ 3 / 2) * s ^ 2 := by
              rw [mul_pow, ← sq_abs r]
              ring
      · exact (by fun_prop :
          Continuous (fun s : ℝ => (|r| ^ 3 / 2) * s ^ 2)).intervalIntegrable 0 1
    _ = |r| ^ 3 / 6 := by
      rw [intervalIntegral.integral_const_mul, _root_.integral_pow]
      norm_num <;> ring

private theorem fclt_scaled_zeta_bounds
    (N B p : ℝ) (hN : 0 < N) (hB : 0 ≤ B) (hp : |p| ≤ B) :
    N * ‖fluctuationZeta (p / Real.sqrt N)‖ ≤ B ^ 2 / 2 ∧
      N * ‖fluctuationZeta (p / Real.sqrt N) +
        (((p / Real.sqrt N : ℝ) : ℂ) ^ 2) / 2‖ ≤
          B ^ 3 / (6 * Real.sqrt N) := by
  let R := Real.sqrt N
  have hR : 0 < R := Real.sqrt_pos.mpr hN
  have hR2 : R ^ 2 = N := Real.sq_sqrt hN.le
  have hp2 : p ^ 2 ≤ B ^ 2 :=
    sq_le_sq' (abs_le.mp hp).1 (abs_le.mp hp).2
  have hp3 : |p| ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ (abs_nonneg p) hp 3
  constructor
  · calc
      N * ‖fluctuationZeta (p / Real.sqrt N)‖
          ≤ N * ((p / R) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (fluctuationZeta_bound (p / R)) hN.le
      _ = p ^ 2 / 2 := by
        rw [div_pow, hR2]
        field_simp [hN.ne'] <;> ring
      _ ≤ B ^ 2 / 2 := div_le_div_of_nonneg_right hp2 (by norm_num)
  · calc
      N * ‖fluctuationZeta (p / Real.sqrt N) +
          (((p / Real.sqrt N : ℝ) : ℂ) ^ 2) / 2‖
          ≤ N * (|p / R| ^ 3 / 6) :=
        mul_le_mul_of_nonneg_left (fluctuationZeta_cubic_bound (p / R)) hN.le
      _ = |p| ^ 3 / (6 * R) := by
        rw [abs_div, abs_of_nonneg hR.le, div_pow, ← hR2]
        field_simp [hR.ne']
        <;> ring
      _ ≤ B ^ 3 / (6 * R) :=
        div_le_div_of_nonneg_right hp3 (by positivity)

private theorem fclt_norm_weighted_sum_le
    {ι : Type*} (s : Finset ι) (b : ι → ℝ) (w : ι → ℂ) (N Λ B : ℝ)
    (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hΛ : ∑ i ∈ s, b i ≤ Λ)
    (hw : ∀ i ∈ s, N * ‖w i‖ ≤ B) :
    ‖(N : ℂ) * ∑ i ∈ s, (b i : ℂ) * w i‖ ≤ Λ * B := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN]
  calc
    N * ‖∑ i ∈ s, (b i : ℂ) * w i‖
        ≤ N * ∑ i ∈ s, ‖(b i : ℂ) * w i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hN
    _ = ∑ i ∈ s, b i * (N * ‖w i‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i hi)]
      ring
    _ ≤ ∑ i ∈ s, b i * B :=
      Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hw i hi) (hb i hi)
    _ = (∑ i ∈ s, b i) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ Λ * B := mul_le_mul_of_nonneg_right hΛ hB

private theorem fclt_norm_setIntegral_le
    {T B : ℝ} (hT : 0 ≤ T) (f : ℝ → ℂ)
    (hb : ∀ s ∈ Icc 0 T, ‖f s‖ ≤ B) :
    ‖∫ s in Icc 0 T, f s‖ ≤ T * B := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) :=
    ⟨by simpa using (measure_Icc_lt_top : volume (Icc (0 : ℝ) T) < ⊤)⟩
  have hbound : (fun s => ‖f s‖) ≤ᵐ[volume.restrict (Icc 0 T)] (fun _ => B) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
    exact hb s hs
  calc
    ‖∫ s in Icc 0 T, f s‖ ≤ ∫ s in Icc 0 T, ‖f s‖ :=
      norm_integral_le_integral_norm (f := f) (μ := volume.restrict (Icc 0 T))
    _ ≤ ∫ _s in Icc (0 : ℝ) T, B :=
      integral_mono_of_nonneg (Eventually.of_forall fun s => norm_nonneg (f s))
        (integrable_const B) hbound
    _ = T * B := by simp [Real.volume_Icc, hT, smul_eq_mul]

private theorem fclt_measurable_nonlinear
    (Γ : RateSpec d) (mf : MeanFieldSolution d Γ) (t : Fin m → ℝ)
    (hF : ContDiff ℝ 1 Γ.drift)
    (a : EuclideanSpace ℝ (Fin m × Fin d)) (n : ℕ) :
    Measurable (fluctuationNonlinearCompensator Γ mf t a n) := by
  let M := fluctuationModel Γ n
  have hX : Measurable (fun q : M.canonicalRecordΩ × ℝ =>
      M.frozenDensityProcess M.canonicalPathMap q.2 q.1) := by
    change Measurable (fun q : M.canonicalRecordΩ × ℝ =>
      M.scaledState ((M.canonicalPathMap q.1).frozenStateAt q.2))
    exact (Measurable.of_discrete (f := M.scaledState)).comp
      (M.measurable_prod_canonicalPathMap_frozenStateAt.comp measurable_swap)
  have hp (ℓ : Fin d → ℤ) :
      Measurable (fun q : M.canonicalRecordΩ × ℝ =>
        fluctuationPairing (fluctuationCombinedTest Γ mf t a) ℓ q.2 /
          Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
    ((measurable_fluctuationPairing
      (measurable_fluctuationCombinedTest Γ mf t hF a) ℓ).comp
        measurable_snd).div_const _
  have hζ : Continuous fluctuationZeta := by unfold fluctuationZeta; fun_prop
  have hm : Measurable (fun q : M.canonicalRecordΩ × ℝ =>
      ((n + 1 : ℕ) : ℂ) * ∑ ℓ ∈ Γ.jumps,
        (Γ.rate ℓ (M.frozenDensityProcess M.canonicalPathMap q.2 q.1) : ℂ) *
          fluctuationZeta
            (fluctuationPairing (fluctuationCombinedTest Γ mf t a) ℓ q.2 /
              Real.sqrt ((n + 1 : ℕ) : ℝ))) := by
    exact measurable_const.mul (Finset.measurable_sum _ fun ℓ hℓ =>
      (Complex.measurable_ofReal.comp
        ((fluctuation_rate_continuous Γ ℓ hℓ).measurable.comp hX)).mul
          (hζ.measurable.comp (hp ℓ)))
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Icc 0 (fluctuationHorizon t)))).measurable

private theorem fclt_abs_setIntegral_le
    {τ C : ℝ} (hτ : 0 ≤ τ)
    (f : ℝ → ℝ) (hb : ∀ s ∈ Icc 0 τ, |f s| ≤ C) :
    |∫ s in Icc 0 τ, f s| ≤ τ * C := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) τ)) :=
    ⟨by simpa using
      (measure_Icc_lt_top : volume (Icc (0 : ℝ) τ) < ⊤)⟩
  have hbound : (fun s => |f s|) ≤ᵐ[volume.restrict (Icc 0 τ)]
      (fun _ => C) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
    exact hb s hs
  calc
    |∫ s in Icc 0 τ, f s| ≤ ∫ s in Icc 0 τ, |f s| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (f := f) (μ := volume.restrict (Icc 0 τ)))
    _ ≤ ∫ _s in Icc (0 : ℝ) τ, C :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun s => abs_nonneg (f s))
        (integrable_const C) hbound
    _ = τ * C := by
      simp [Real.volume_Icc, hτ, smul_eq_mul]

private theorem fclt_noise_charFun_of_compensator
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ξ : ∀ n, Ω n → ℝ) (D : ∀ n, Ω n → ℂ) (q K : ℝ)
    (hξ : ∀ n, Measurable (ξ n)) (hD : ∀ n, Measurable (D n))
    (hbound : ∀ n ω, ‖D n ω‖ ≤ K)
    (hprob : ∀ η > (0 : ℝ), Tendsto
      (fun n => P n {ω | η < ‖D n ω + (q : ℂ) / 2‖}) atTop (𝓝 0))
    (hid : ∀ n,
      (∫ ω, Complex.exp (Complex.I * (ξ n ω : ℂ) - D n ω) ∂P n) = 1) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I * (ξ n ω : ℂ)) ∂P n)
      atTop (𝓝 (Complex.exp (-(q : ℂ) / 2))) := by
  let c : ℂ := Complex.exp (-(q : ℂ) / 2)
  let F : ℂ → ℂ := fun z => 1 - c * Complex.exp (-z)
  let W : ∀ n, Ω n → ℂ := fun n ω =>
    Complex.exp (Complex.I * (ξ n ω : ℂ)) -
      c * Complex.exp (Complex.I * (ξ n ω : ℂ) - D n ω)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hFzero : F (-(q : ℂ) / 2) = 0 := by
    dsimp [F, c]
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, sub_self]
  have hWnorm (n : ℕ) (ω : Ω n) : ‖W n ω‖ = ‖F (D n ω)‖ := by
    have heq : W n ω =
        Complex.exp (Complex.I * (ξ n ω : ℂ)) * F (D n ω) := by
      dsimp [W, F]
      simp only [sub_eq_add_neg, Complex.exp_add]
      ring
    rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hExp (n : ℕ) (ω : Ω n) : ‖Complex.exp (-D n ω)‖ ≤ Real.exp K := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr
      ((Complex.re_le_norm (-D n ω)).trans (by simpa only [norm_neg] using hbound n ω))
  have hWbound : ∀ n, ∀ᵐ ω ∂P n, ‖W n ω‖ ≤ 1 + ‖c‖ * Real.exp K := by
    intro n
    exact Eventually.of_forall fun ω => by
      rw [hWnorm]
      calc
        ‖F (D n ω)‖ ≤ ‖(1 : ℂ)‖ + ‖c * Complex.exp (-D n ω)‖ :=
          norm_sub_le _ _
        _ ≤ 1 + ‖c‖ * Real.exp K := by
          rw [norm_one, norm_mul]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hExp n ω) (norm_nonneg _))
  have hWprob : ∀ η > (0 : ℝ),
      Tendsto (fun n => P n {ω | η < ‖W n ω‖}) atTop (𝓝 0) := by
    intro η hη
    obtain ⟨δ, hδ, hδF⟩ := Metric.continuous_iff.mp hF (-(q : ℂ) / 2) η hη
    have hsub (n : ℕ) :
        {ω : Ω n | η < ‖W n ω‖} ⊆
          {ω | δ / 2 < ‖D n ω + (q : ℂ) / 2‖} := by
      intro ω hω
      change η < ‖W n ω‖ at hω
      by_contra hnot
      have hle : ‖D n ω + (q : ℂ) / 2‖ ≤ δ / 2 := le_of_not_gt hnot
      have hdist : dist (D n ω) (-(q : ℂ) / 2) < δ := by
        rw [dist_eq_norm]
        have heq : D n ω - (-(q : ℂ) / 2) = D n ω + (q : ℂ) / 2 := by ring
        rw [heq]
        exact hle.trans_lt (half_lt_self hδ)
      have hsmall : ‖F (D n ω)‖ < η := by
        simpa only [hFzero, dist_eq_norm, sub_zero] using hδF (D n ω) hdist
      have hlarge : η < ‖F (D n ω)‖ := by
        simpa only [hWnorm] using hω
      exact (not_lt_of_ge hsmall.le) hlarge
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    filter_upwards
      [(ENNReal.tendsto_nhds_zero.mp (hprob (δ / 2) (half_pos hδ))) ε hε]
      with n hn
    exact (measure_mono (hsub n)).trans hn
  have hWlim :=
    tendsto_integral_complex_of_bounded_of_tendsto_measure P W
      (M := 1 + ‖c‖ * Real.exp K) (by positivity) hWbound hWprob
  have hphase (n : ℕ) :
      Integrable (fun ω => Complex.exp (Complex.I * (ξ n ω : ℂ))) (P n) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact (Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp (hξ n)))).aestronglyMeasurable
    · exact Eventually.of_forall fun ω =>
        (Complex.norm_exp_I_mul_ofReal (ξ n ω)).le
  have hcomp (n : ℕ) :
      Integrable (fun ω => Complex.exp (Complex.I * (ξ n ω : ℂ) - D n ω))
        (P n) := by
    refine (integrable_const (Real.exp K)).mono' ?_ ?_
    · exact (Complex.measurable_exp.comp
        ((measurable_const.mul (Complex.measurable_ofReal.comp (hξ n))).sub
          (hD n))).aestronglyMeasurable
    · exact Eventually.of_forall fun ω => by
        simpa only [sub_eq_add_neg, Complex.exp_add, norm_mul,
          Complex.norm_exp_I_mul_ofReal, one_mul] using hExp n ω
  have hWeq (n : ℕ) :
      (∫ ω, W n ω ∂P n) =
        (∫ ω, Complex.exp (Complex.I * (ξ n ω : ℂ)) ∂P n) - c := by
    dsimp [W]
    rw [integral_sub (hphase n) ((hcomp n).const_mul c),
      integral_const_mul, hid n, mul_one]
  simpa only [hWeq, sub_add_cancel, zero_add] using hWlim.add_const c

/-! ## Compensator convergence, tightness, and remainder -/

section RemainingModelStatements

variable [NeZero d]
variable (Γ : RateSpec d) (mf : MeanFieldSolution d Γ)
variable
  (hConservative : ∀ (N : ℕ) (hN : 0 < N),
    (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
  (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
    (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
  (hSolBound : ∀ s : ℝ, 0 ≤ s → ‖mf.sol s‖ ≤ 1)
  (hF : ContDiff ℝ 1 Γ.drift)
  (t : Fin m → ℝ) (ht : ∀ j, 0 ≤ t j)
  (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
  (hz : ∀ n, (fluctuationModel Γ n).InSimplex (z n))
  (v₀ : Fin d → ℝ)
  (hinit : Tendsto
    (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) •
      ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0))
    atTop (𝓝 v₀))
  (a : EuclideanSpace ℝ (Fin m × Fin d))

-- Every signature in this section includes precisely these model hypotheses.
include hConservative hBoundary hSolBound hF ht hz hinit

-- Section-dependent expressions are written out explicitly.


theorem fluctuation_compensator_constants :
    ∃ J Λ C : ℝ, 1 ≤ J ∧ 1 ≤ Λ ∧ 0 ≤ C ∧
      (∀ ℓ ∈ Γ.jumps, ‖(fun i => (ℓ i : ℝ))‖ ≤ J) ∧
      (∀ x : Fin d → ℝ, (∀ i, 0 ≤ x i) → ‖x‖ ≤ 1 →
        (∑ ℓ ∈ Γ.jumps, Γ.rate ℓ x) ≤ Λ) ∧
      (∀ s, ‖fluctuationCombinedTest Γ mf t a s‖ ≤ C) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_fluctuationCombinedTest_bound Γ mf t hF ht a
  have hrate : Continuous
      (fun x : Fin d → ℝ => ∑ ℓ ∈ Γ.jumps, Γ.rate ℓ x) :=
    continuous_finset_sum _ fun ℓ hℓ => fluctuation_rate_continuous Γ ℓ hℓ
  obtain ⟨B, hB⟩ :=
    (isCompact_closedBall (0 : Fin d → ℝ) 1).exists_bound_of_continuousOn
      hrate.continuousOn
  refine ⟨max 1 (∑ ℓ ∈ Γ.jumps, ‖(fun i => (ℓ i : ℝ))‖),
    max 1 B, C, le_max_left _ _, le_max_left _ _, hC0, ?_, ?_, hC⟩
  · intro ℓ hℓ
    exact (Finset.single_le_sum (fun k _ => norm_nonneg (fun i => (k i : ℝ)))
      hℓ).trans (le_max_right _ _)
  · intro x _ hx
    calc
      (∑ ℓ ∈ Γ.jumps, Γ.rate ℓ x)
          ≤ ‖∑ ℓ ∈ Γ.jumps, Γ.rate ℓ x‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (∑ ℓ ∈ Γ.jumps, Γ.rate ℓ x)
      _ ≤ B := hB x (by simpa using hx)
      _ ≤ max 1 B := le_max_right _ _

theorem fluctuation_compensator_uniform_bounds
    (J Λ C : ℝ) (hJ0 : 1 ≤ J) (hΛ0 : 0 ≤ Λ) (hC0 : 0 ≤ C)
    (hJ : ∀ ℓ ∈ Γ.jumps, ‖(fun i => (ℓ i : ℝ))‖ ≤ J)
    (hΛ : ∀ x : Fin d → ℝ, (∀ i, 0 ≤ x i) → ‖x‖ ≤ 1 →
      (∑ ℓ ∈ Γ.jumps, Γ.rate ℓ x) ≤ Λ)
    (hC : ∀ s, ‖fluctuationCombinedTest Γ mf t a s‖ ≤ C)
    (n : ℕ) (ω : (fluctuationModel Γ n).canonicalRecordΩ) :
    ‖fluctuationNonlinearCompensator Γ mf t a n ω‖ ≤
        (fluctuationHorizon t) * Λ * ((d : ℝ) * J * C) ^ 2 / 2 ∧
      ‖fluctuationNonlinearCompensator Γ mf t a n ω +
          (fluctuationPathQuadratic Γ mf t a n ω : ℂ) / 2‖ ≤
        (fluctuationHorizon t) * Λ * ((d : ℝ) * J * C) ^ 3 /
          (6 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  classical
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let R : ℝ := Real.sqrt N
  let B : ℝ := (d : ℝ) * J * C
  let p := fluctuationPairing (fluctuationCombinedTest Γ mf t a)
  let b : (Fin d → ℤ) → ℝ → ℝ := fun ℓ s => Γ.rate ℓ (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω))
  let f : ℝ → ℂ := fun s =>
    (N : ℂ) * ∑ ℓ ∈ Γ.jumps, (b ℓ s : ℂ) * fluctuationZeta (p ℓ s / R)
  let e : ℝ → ℂ := fun s =>
    (N : ℂ) * ∑ ℓ ∈ Γ.jumps, (b ℓ s : ℂ) *
      (fluctuationZeta (p ℓ s / R) + (((p ℓ s / R : ℝ) : ℂ) ^ 2) / 2)
  let q : ℝ → ℝ := fun s => ∑ ℓ ∈ Γ.jumps, b ℓ s * (p ℓ s) ^ 2
  have hN : 0 < N := by dsimp [N]; positivity
  have hR : 0 < R := Real.sqrt_pos.mpr hN
  have hR2 : R ^ 2 = N := Real.sq_sqrt hN.le
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hJ0)) hC0
  have hX0 (s : ℝ) (i : Fin d) : 0 ≤ ((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω) i := by
    change 0 ≤
      (((fluctuationModel Γ n).canonicalPathMap ω).frozenStateAt s i : ℝ) /
        ((fluctuationModel Γ n).N : ℝ)
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hXnorm (s : ℝ) : ‖((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω)‖ ≤ 1 :=
    (fluctuationModel Γ n).frozenDensityProcess_norm_le
      (fluctuationModel Γ n).canonicalPathMap s ω
  have hb (ℓ : Fin d → ℤ) (hℓ : ℓ ∈ Γ.jumps) (s : ℝ) : 0 ≤ b ℓ s :=
    Γ.rate_nonneg ℓ hℓ (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω)) (hX0 s)
  have hbsum (s : ℝ) : (∑ ℓ ∈ Γ.jumps, b ℓ s) ≤ Λ :=
    hΛ (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω)) (hX0 s) (hXnorm s)
  have hp (ℓ : Fin d → ℤ) (hℓ : ℓ ∈ Γ.jumps) (s : ℝ) : |p ℓ s| ≤ B := by
    calc
      |p ℓ s| ≤ (d : ℝ) * ‖fluctuationCombinedTest Γ mf t a s‖ *
          ‖(fun i => (ℓ i : ℝ))‖ := fluctuation_abs_dot_le _ _
      _ ≤ (d : ℝ) * C * J :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hC s) (Nat.cast_nonneg _))
          (hJ ℓ hℓ) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC0)
      _ = B := by dsimp [B]; ring
  have hfbound (s : ℝ) : ‖f s‖ ≤ Λ * (B ^ 2 / 2) := by
    apply fclt_norm_weighted_sum_le Γ.jumps (fun ℓ => b ℓ s)
      (fun ℓ => fluctuationZeta (p ℓ s / R)) N Λ (B ^ 2 / 2) hN.le
        (by positivity) (fun ℓ hℓ => hb ℓ hℓ s) (hbsum s)
    intro ℓ hℓ
    exact (fclt_scaled_zeta_bounds N B (p ℓ s) hN hB (hp ℓ hℓ s)).1
  have hebound (s : ℝ) : ‖e s‖ ≤ Λ * (B ^ 3 / (6 * R)) := by
    apply fclt_norm_weighted_sum_le Γ.jumps (fun ℓ => b ℓ s)
      (fun ℓ => fluctuationZeta (p ℓ s / R) +
        (((p ℓ s / R : ℝ) : ℂ) ^ 2) / 2) N Λ (B ^ 3 / (6 * R)) hN.le
        (by positivity) (fun ℓ hℓ => hb ℓ hℓ s) (hbsum s)
    intro ℓ hℓ
    exact (fclt_scaled_zeta_bounds N B (p ℓ s) hN hB (hp ℓ hℓ s)).2
  have hXm : Measurable (fun s => ((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω)) := by
    change Measurable
      (fun s => (fluctuationModel Γ n).scaledState
        (((fluctuationModel Γ n).canonicalPathMap ω).frozenStateAt s))
    exact (Measurable.of_discrete (f := (fluctuationModel Γ n).scaledState)).comp
      ((fluctuationModel Γ n).measurable_canonicalPathMap_frozenStateAt_section ω)
  have hbm (ℓ : Fin d → ℤ) (hℓ : ℓ ∈ Γ.jumps) : Measurable (b ℓ) :=
    (fluctuation_rate_continuous Γ ℓ hℓ).measurable.comp hXm
  have hpm (ℓ : Fin d → ℤ) : Measurable (fun s => p ℓ s / R) :=
    (measurable_fluctuationPairing
      (measurable_fluctuationCombinedTest Γ mf t hF a) ℓ).div_const R
  have hζ : Continuous fluctuationZeta := by unfold fluctuationZeta; fun_prop
  have hfm : Measurable f := by
    exact measurable_const.mul (Finset.measurable_sum _ fun ℓ hℓ =>
      (Complex.measurable_ofReal.comp (hbm ℓ hℓ)).mul
        (hζ.measurable.comp (hpm ℓ)))
  have hem : Measurable e := by
    exact measurable_const.mul (Finset.measurable_sum _ fun ℓ hℓ =>
      (Complex.measurable_ofReal.comp (hbm ℓ hℓ)).mul
        ((hζ.measurable.comp (hpm ℓ)).add
          (((Complex.measurable_ofReal.comp (hpm ℓ)).pow_const 2).div_const 2)))
  have hfi : IntegrableOn f (Icc 0 (fluctuationHorizon t)) volume :=
    IntegrableOn.of_bound
      (measure_Icc_lt_top : volume (Icc (0 : ℝ) (fluctuationHorizon t)) < ⊤)
      hfm.aestronglyMeasurable (Λ * (B ^ 2 / 2))
      (Eventually.of_forall hfbound)
  have hei : IntegrableOn e (Icc 0 (fluctuationHorizon t)) volume :=
    IntegrableOn.of_bound
      (measure_Icc_lt_top : volume (Icc (0 : ℝ) (fluctuationHorizon t)) < ⊤)
      hem.aestronglyMeasurable (Λ * (B ^ 3 / (6 * R)))
      (Eventually.of_forall hebound)
  have hsquare (u : ℝ) :
      (N : ℂ) * ((((u / R : ℝ) : ℂ) ^ 2) / 2) = ((u ^ 2 : ℝ) : ℂ) / 2 := by
    have hRc : (R : ℂ) ^ 2 = (N : ℂ) := by exact_mod_cast hR2
    push_cast
    rw [div_pow, hRc]
    field_simp [Complex.ofReal_ne_zero.mpr hN.ne'] <;> ring
  have heq (s : ℝ) : e s = f s + (q s : ℂ) / 2 := by
    dsimp [e, f, q]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ℓ _
    calc
      (N : ℂ) * ((b ℓ s : ℂ) * (((p ℓ s : ℂ) / (R : ℂ)) ^ 2 / 2)) =
          (b ℓ s : ℂ) * ((N : ℂ) * (((p ℓ s : ℂ) / (R : ℂ)) ^ 2 / 2)) := by
        ring
      _ = (b ℓ s : ℂ) * ((p ℓ s : ℂ) ^ 2 / 2) := by
        simpa only [Complex.ofReal_div, Complex.ofReal_pow] using
          congrArg (fun z : ℂ => (b ℓ s : ℂ) * z) (hsquare (p ℓ s))
      _ = (b ℓ s : ℂ) * (p ℓ s : ℂ) ^ 2 / 2 := by ring
  have hintq :
      ((∫ s in Icc 0 (fluctuationHorizon t), q s : ℝ) : ℂ) / 2 =
        (∫ s in Icc 0 (fluctuationHorizon t), e s) - ∫ s in Icc 0 (fluctuationHorizon t), f s := by
    rw [← integral_complex_ofReal, ← integral_div]
    calc
      (∫ s in Icc 0 (fluctuationHorizon t), (q s : ℂ) / 2) =
          ∫ s in Icc 0 (fluctuationHorizon t), e s - f s := by
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by beta_reduce; rw [heq s]; ring
      _ = _ := integral_sub hei hfi
  constructor
  · change ‖∫ s in Icc 0 (fluctuationHorizon t), f s‖ ≤ _
    exact (fclt_norm_setIntegral_le (fluctuationHorizon_pos t).le f
      (fun s _ => hfbound s)).trans_eq (by dsimp [B]; ring)
  · change ‖(∫ s in Icc 0 (fluctuationHorizon t), f s) + ((∫ s in Icc 0 (fluctuationHorizon t), q s : ℝ) : ℂ) / 2‖ ≤ _
    rw [hintq, ← add_sub_assoc, add_sub_cancel_left]
    exact (fclt_norm_setIntegral_le (fluctuationHorizon_pos t).le e
      (fun s _ => hebound s)).trans_eq (by dsimp [B, R, N]; ring)

theorem fluctuationNonlinearCompensator_tendsto :
    (∀ n, Measurable (fluctuationNonlinearCompensator Γ mf t a n)) ∧
      ∀ ε > (0 : ℝ),
        Tendsto
          (fun n => ((fluctuationModel Γ n).canonicalRecordMeasure (z n)) {ω | ε <
            ‖fluctuationNonlinearCompensator Γ mf t a n ω +
              (fluctuationLimitQuadratic Γ mf t a : ℂ) / 2‖})
          atTop (𝓝 0) := by
  refine ⟨fclt_measurable_nonlinear Γ mf t hF a, ?_⟩
  obtain ⟨J, Λ, C, hJ0, hΛ1, hC0, hJ, hΛ, hC⟩ :=
    fluctuation_compensator_constants Γ mf hConservative hBoundary hSolBound hF
      t ht z hz v₀ hinit a
  let b : ℕ → ℝ := fun n =>
    ((fluctuationHorizon t) * Λ * ((d : ℝ) * J * C) ^ 3 / 6) *
      (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹
  have hb : Tendsto b atTop (𝓝 0) := by
    have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hinv : Tendsto
        (fun n : ℕ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hinv :
        Tendsto b atTop (𝓝 (((fluctuationHorizon t) * Λ * ((d : ℝ) * J * C) ^ 3 / 6) * 0)))
  have hbound (n : ℕ) (ω : (fluctuationModel Γ n).canonicalRecordΩ) :
      ‖fluctuationNonlinearCompensator Γ mf t a n ω +
          (fluctuationPathQuadratic Γ mf t a n ω : ℂ) / 2‖ ≤ b n := by
    have hh := (fluctuation_compensator_uniform_bounds Γ mf
      hConservative hBoundary hSolBound hF t ht z hz v₀ hinit a
        J Λ C hJ0 (zero_le_one.trans hΛ1) hC0 hJ hΛ hC n ω).2
    have hden :
        (fluctuationHorizon t) * Λ * ((d : ℝ) * J * C) ^ 3 /
            (6 * Real.sqrt ((n + 1 : ℕ) : ℝ)) = b n := by
      dsimp only [b]
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring
    exact hh.trans_eq hden
  intro ε hε
  have hq := fluctuationPathQuadratic_tendsto Γ mf hConservative hBoundary hSolBound
    hF t ht z hz v₀ hinit a ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  filter_upwards
    [hb.eventually (Iio_mem_nhds (half_pos hε)),
      (ENNReal.tendsto_nhds_zero.mp hq) η hη] with n hn hqn
  refine (measure_mono ?_).trans hqn
  intro ω hω
  by_contra hnot
  have hqle :
      |fluctuationPathQuadratic Γ mf t a n ω -
        fluctuationLimitQuadratic Γ mf t a| ≤ ε := le_of_not_gt hnot
  have heq :
      fluctuationNonlinearCompensator Γ mf t a n ω +
          (fluctuationLimitQuadratic Γ mf t a : ℂ) / 2 =
        (fluctuationNonlinearCompensator Γ mf t a n ω +
          (fluctuationPathQuadratic Γ mf t a n ω : ℂ) / 2) -
          ((fluctuationPathQuadratic Γ mf t a n ω -
            fluctuationLimitQuadratic Γ mf t a : ℝ) : ℂ) / 2 := by
    push_cast
    ring
  have hnorm :
      ‖fluctuationNonlinearCompensator Γ mf t a n ω +
        (fluctuationLimitQuadratic Γ mf t a : ℂ) / 2‖ ≤
          b n + |fluctuationPathQuadratic Γ mf t a n ω -
            fluctuationLimitQuadratic Γ mf t a| / 2 := by
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    apply add_le_add (hbound n ω)
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  change ε < ‖fluctuationNonlinearCompensator Γ mf t a n ω +
    (fluctuationLimitQuadratic Γ mf t a : ℂ) / 2‖ at hω
  have hbn : b n < ε / 2 := hn
  linarith

theorem fluctuationNoise_charFun_tendsto :
    Tendsto
      (fun n => ∫ ω,
        Complex.exp (Complex.I * (fluctuationNoise Γ mf t a n ω : ℂ)) ∂((fluctuationModel Γ n).canonicalRecordMeasure (z n)))
      atTop
      (𝓝 (Complex.exp (-(fluctuationLimitQuadratic Γ mf t a : ℂ) / 2))) := by
  obtain ⟨J, Λ, C, hJ0, hΛ1, hC0, hJ, hΛ, hC⟩ :=
    fluctuation_compensator_constants Γ mf hConservative hBoundary hSolBound hF
      t ht z hz v₀ hinit a
  have hconv := fluctuationNonlinearCompensator_tendsto Γ mf
    hConservative hBoundary hSolBound hF t ht z hz v₀ hinit a
  apply fclt_noise_charFun_of_compensator (fun n : ℕ => (fluctuationModel Γ n).canonicalRecordMeasure (z n))
    (fluctuationNoise Γ mf t a) (fluctuationNonlinearCompensator Γ mf t a)
    (fluctuationLimitQuadratic Γ mf t a)
    ((fluctuationHorizon t) * Λ * ((d : ℝ) * J * C) ^ 2 / 2)
    (fun n => measurable_fluctuationNoise Γ mf t hF a n) hconv.1
    (fun n ω => (fluctuation_compensator_uniform_bounds Γ mf
      hConservative hBoundary hSolBound hF t ht z hz v₀ hinit a
        J Λ C hJ0 (zero_le_one.trans hΛ1) hC0 hJ hΛ hC n ω).1) hconv.2
  exact fluctuation_exponential_identity Γ mf
    hConservative hBoundary hSolBound hF t ht z hz v₀ hinit a

theorem fluctuationScaledErrorSup_tight :
    ∀ ε > (0 : ℝ), ∃ R > (0 : ℝ), ∀ n,
      ((fluctuationModel Γ n).canonicalRecordMeasure (z n)) {ω | R < fluctuationScaledErrorSup Γ mf t n ω} ≤ ENNReal.ofReal ε := by
  obtain ⟨B, hBpos, hB⟩ :=
    hinit.cauchySeq.isBounded_range.exists_pos_norm_le
  have hBscaled (n : ℕ) :
      Real.sqrt ((n + 1 : ℕ) : ℝ) *
        ‖(fluctuationModel Γ n).scaledState (z n) - mf.x₀‖ ≤ B := by
    have hb := hB _ (Set.mem_range_self n)
    simpa only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mf.sol_init] using hb
  have hH : 0 < (fluctuationHorizon t) := fluctuationHorizon_pos t
  have hDrift : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).DriftZeroAtAbsorbingOnSimplex :=
    fun N hN =>
      driftZeroAtAbsorbingOnSimplex_of_boundaryCompatible _ (hBoundary N hN)
  obtain ⟨C, hCpos, hqv⟩ :=
    frozen_martingale_qv_bound_uniform_of_doob Γ
      (DensityDepCTMC.frozenMartingalePartDoobL2Constant_pos d)
      (frozenDoobL2_of_boundaryCompatible Γ hConservative hBoundary)
      Γ.exists_instantQVRate_bound_uniform hH
  obtain ⟨K, hK1, hincl⟩ :=
    frozen_event_inclusion_generic_linear Γ mf.extendLeft hDrift hConservative
      (fun s hs => by
        rw [mf.extendLeft_sol_of_nonneg hs]
        exact hSolBound s hs)
      mf.extendLeft_measurable
      (fun i s _ => mf.extendLeft_drift_intervalIntegrable i s) hH
  have hKpos : 0 < K := zero_lt_one.trans_le hK1
  intro ε hε
  let A : ℝ := B + 1 + C * (fluctuationHorizon t) / ε
  have hratio0 : 0 ≤ C * (fluctuationHorizon t) / ε := (div_pos (mul_pos hCpos hH) hε).le
  have hBA : B < A := by dsimp [A]; linarith
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hApos : 0 < A := zero_lt_one.trans_le hA1
  have hAsq : A ≤ A ^ 2 := by nlinarith
  have hbudget : C * (fluctuationHorizon t) ≤ ε * A ^ 2 := by
    have hratio : C * (fluctuationHorizon t) / ε ≤ A := by dsimp [A]; linarith
    have hlinear : C * (fluctuationHorizon t) ≤ A * ε := (div_le_iff₀ hε).mp hratio
    exact hlinear.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hAsq hε.le)
  change ∃ R : ℝ, 0 < R ∧ ∀ n : ℕ,
    (fluctuationModel Γ n).canonicalRecordMeasure (z n)
      {ω : (fluctuationModel Γ n).canonicalRecordΩ |
        R < fluctuationScaledErrorSup Γ mf t n ω} ≤ ENNReal.ofReal ε
  refine ⟨K * A, mul_pos hKpos hApos, ?_⟩
  intro n
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hNpos : 0 < N := by
    change (0 : ℝ) < ((n + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.succ_pos n
  let σ : ℝ := Real.sqrt N
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hNpos
  have hσsq : σ ^ 2 = N := Real.sq_sqrt hNpos.le
  let δ : ℝ := A / σ
  have hδpos : 0 < δ := div_pos hApos hσpos
  have hcancel : (K * δ) / K = δ := by
    field_simp [hKpos.ne'] <;> ring
  have hNδ : N * δ ^ 2 = A ^ 2 := by
    dsimp [δ]
    rw [div_pow, hσsq]
    exact mul_div_cancel₀ _ hNpos.ne'
  let M : DensityDepCTMC d := fluctuationModel Γ n
  let dp := M.toFrozenDensityProcess (z n)
    (hDrift (n + 1) (Nat.succ_pos n))
    (hConservative (n + 1) (Nat.succ_pos n)) (hz n)
  let μ := M.canonicalRecordMeasure (z n)
  let E : Set M.canonicalRecordΩ :=
    {ω | K * A < fluctuationScaledErrorSup Γ mf t n ω}
  let G : Set M.canonicalRecordΩ :=
    {ω | δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ (fluctuationHorizon t)),
      ‖dp.martingale_part s ω‖ ^ 2}
  change μ E ≤ ENNReal.ofReal ε
  have hclose : ‖M.scaledState (z n) - mf.x₀‖ < δ := by
    change ‖M.scaledState (z n) - mf.x₀‖ < A / σ
    rw [lt_div_iff₀ hσpos]
    have hb : σ * ‖M.scaledState (z n) - mf.x₀‖ ≤ B :=
      hBscaled n
    nlinarith
  have hevent :
      ∀ᵐ ω ∂μ,
        (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ (fluctuationHorizon t)),
          ‖dp.process s ω - mf.extendLeft.sol s‖) ≥ K * δ →
        (‖dp.init ω - mf.x₀‖ ≥ δ) ∨
          (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ (fluctuationHorizon t)),
            ‖dp.martingale_part s ω‖ ^ 2) := by
    have h := hincl (mul_pos hKpos hδpos)
      (n + 1) (Nat.succ_pos n) (z n) (hz n)
    simpa only [hcancel, MeanFieldSolution.extendLeft_x₀] using h
  have hinit_ae : ∀ᵐ ω ∂μ, dp.init ω = M.scaledState (z n) := by
    exact M.canonical_frozenInitialCondition_eq_scaledState_ae (z n)
  have hEG : ∀ᵐ ω ∂μ, ω ∈ E → ω ∈ G := by
    filter_upwards [hevent, hinit_ae] with ω he hi hE
    have hsup :
        K * δ < fluctuationTimeSup (fluctuationHorizon t)
          (fun s => ‖dp.process s ω - mf.sol s‖) := by
      change K * A < σ * fluctuationTimeSup (fluctuationHorizon t)
        (fun s => ‖dp.process s ω - mf.sol s‖) at hE
      dsimp [δ]
      rw [← mul_div_assoc, div_lt_iff₀ hσpos]
      simpa only [mul_comm] using hE
    have hext :
        (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ (fluctuationHorizon t)),
          ‖dp.process s ω - mf.extendLeft.sol s‖) =
        fluctuationTimeSup (fluctuationHorizon t) (fun s => ‖dp.process s ω - mf.sol s‖) := by
      unfold fluctuationTimeSup
      refine iSup_congr fun s => iSup_congr fun hs => ?_
      rw [mf.extendLeft_sol_of_nonneg hs.1]
    have hsup' :
        (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ (fluctuationHorizon t)),
          ‖dp.process s ω - mf.extendLeft.sol s‖) ≥ K * δ := by
      rw [hext]
      exact hsup.le
    rcases he hsup' with hbad | hgood
    · rw [hi] at hbad
      exact (not_le_of_gt hclose hbad).elim
    · exact hgood
  have hnonneg :
      ∀ᵐ ω ∂μ, 0 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ (fluctuationHorizon t)),
        ‖dp.martingale_part s ω‖ ^ 2 :=
    dp.martingale_sup_sq_nonneg (fluctuationHorizon t) hH
  have hintegrable :
      Integrable
        (fun ω => ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ (fluctuationHorizon t)),
          ‖dp.martingale_part s ω‖ ^ 2) μ :=
    dp.martingale_sup_sq_integrable (fluctuationHorizon t) hH
  have hmark :
      δ ^ 2 * μ.real G ≤
        ∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ (fluctuationHorizon t)),
          ‖dp.martingale_part s ω‖ ^ 2 ∂μ :=
    mul_meas_ge_le_integral_of_nonneg hnonneg hintegrable (δ ^ 2)
  have hqvN :
      (∫ ω, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ (fluctuationHorizon t)),
        ‖dp.martingale_part s ω‖ ^ 2 ∂μ) ≤ C * (fluctuationHorizon t) / N := by
    exact hqv (n + 1) (Nat.succ_pos n) (z n) (hz n)
  have hscaled : A ^ 2 * μ.real G ≤ C * (fluctuationHorizon t) := by
    calc
      A ^ 2 * μ.real G = N * (δ ^ 2 * μ.real G) := by
        rw [← hNδ]
        ring
      _ ≤ N * (C * (fluctuationHorizon t) / N) :=
        mul_le_mul_of_nonneg_left (hmark.trans hqvN) hNpos.le
      _ = C * (fluctuationHorizon t) := mul_div_cancel₀ _ hNpos.ne'
  have hreal : μ.real G ≤ ε := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hApos)).mp
    exact hscaled.trans (by simpa only [mul_comm] using hbudget)
  exact (measure_mono_ae hEG).trans
    ((ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ G) hε.le).2 hreal)

theorem fluctuation_remainder_local_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (n : ℕ)
      (ω : (fluctuationModel Γ n).canonicalRecordΩ) (j : Fin m) (C : ℝ),
      0 ≤ C →
      (∀ s ∈ Icc 0 (t j),
        ‖fluctuationObservationCutoffTest Γ mf t a j s‖ ≤ C) →
      (fluctuationTimeSup (fluctuationHorizon t)
        (fun s => ‖(fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω - mf.sol s‖)) ≤ δ →
      Real.sqrt ((n + 1 : ℕ) : ℝ) *
          |fluctuationRemainder (fluctuationModel Γ n)
            (fluctuationObservationCutoffTest Γ mf t a j)
            mf.extendLeft.sol (t j) ω| ≤
        ((d : ℝ) * t j * C * ε) * fluctuationScaledErrorSup Γ mf t n ω := by
  obtain ⟨δ, hδ, hTaylor⟩ := exists_taylor_modulus_on_closedBall hF 1 ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n ω j C hC hψ hclose
  have hX (s : ℝ) : ‖((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω)‖ ≤ 1 :=
    (fluctuationModel Γ n).frozenDensityProcess_norm_le
      (fluctuationModel Γ n).canonicalPathMap s ω
  have hdist : ∀ s ∈ Icc 0 (fluctuationHorizon t), ‖((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω) - mf.sol s‖ ≤ 2 := by
    intro s hs
    calc
      ‖((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω) - mf.sol s‖ ≤ ‖((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω)‖ + ‖mf.sol s‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hX s) (hSolBound s hs.1)
      _ = 2 := by norm_num
  have hsup (s : ℝ) (hs : s ∈ Icc 0 (t j)) :
      ‖((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω) - mf.sol s‖ ≤ (fluctuationTimeSup (fluctuationHorizon t)
        (fun s => ‖(fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω - mf.sol s‖)) :=
    fluctuation_le_timeSup (by norm_num : (0 : ℝ) ≤ 2) hdist
      ⟨hs.1, hs.2.trans (time_le_fluctuationHorizon t j)⟩
  have hrem (s : ℝ) (hs : s ∈ Icc 0 (t j)) :
      ‖Γ.drift (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω)) - Γ.drift (mf.extendLeft.sol s) -
        (fderiv ℝ Γ.drift (mf.extendLeft.sol s))
          (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω) - mf.extendLeft.sol s)‖ ≤ ε * (fluctuationTimeSup (fluctuationHorizon t)
        (fun s => ‖(fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω - mf.sol s‖)) := by
    rw [mf.extendLeft_sol_of_nonneg hs.1]
    exact (hTaylor (mf.sol s) (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω)) (hSolBound s hs.1) (hX s)
      ((hsup s hs).trans hclose)).trans
        (mul_le_mul_of_nonneg_left (hsup s hs) hε.le)
  have hR :
      |fluctuationRemainder (fluctuationModel Γ n)
        (fluctuationObservationCutoffTest Γ mf t a j)
        mf.extendLeft.sol (t j) ω| ≤
          t j * ((d : ℝ) * C * (ε * (fluctuationTimeSup (fluctuationHorizon t)
        (fun s => ‖(fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω - mf.sol s‖)))) := by
    change |∫ s in Icc 0 (t j),
      fluctuationObservationCutoffTest Γ mf t a j s ⬝ᵥ
        (Γ.drift (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω)) - Γ.drift (mf.extendLeft.sol s) -
          (fderiv ℝ Γ.drift (mf.extendLeft.sol s))
            (((fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω) - mf.extendLeft.sol s))| ≤ _
    apply fclt_abs_setIntegral_le (ht j)
    intro s hs
    exact (fluctuation_abs_dot_le _ _).trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_left (hψ s hs) (Nat.cast_nonneg _))
        (hrem s hs) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hC))
  calc
    Real.sqrt ((n + 1 : ℕ) : ℝ) *
        |fluctuationRemainder (fluctuationModel Γ n)
          (fluctuationObservationCutoffTest Γ mf t a j)
          mf.extendLeft.sol (t j) ω|
        ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) *
          (t j * ((d : ℝ) * C * (ε * (fluctuationTimeSup (fluctuationHorizon t)
        (fun s => ‖(fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω - mf.sol s‖))))) :=
      mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg _)
    _ = ((d : ℝ) * t j * C * ε) * fluctuationScaledErrorSup Γ mf t n ω := by
      unfold fluctuationScaledErrorSup
      ring

theorem fluctuationError_tendsto :
    ∀ ε > (0 : ℝ),
      Tendsto
        (fun n => ((fluctuationModel Γ n).canonicalRecordMeasure (z n)) {ω | ε < |fluctuationError Γ mf t a n ω|})
        atTop (𝓝 0) := by
  classical
  have hbound (j : Fin m) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s,
        ‖fluctuationObservationCutoffTest Γ mf t a j s‖ ≤ C := by
    have hb (i : Fin d) :
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ s, ‖fluctuationBasisCutoff Γ mf t (j, i) s‖ ≤ B :=
      exists_fluctuationBasisCutoff_bound Γ mf t hF ht (j, i)
    choose B hB0 hB using hb
    refine ⟨∑ i : Fin d, |a (j, i)| * B i, ?_, ?_⟩
    · exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (abs_nonneg _) (hB0 i)
    · intro s
      have hsum :
          ‖(∑ i : Fin d,
            a (j, i) • fluctuationBasisCutoff Γ mf t (j, i) s :
              Fin d → ℝ)‖ ≤
            ∑ i : Fin d, |a (j, i)| * B i := by
        refine (norm_sum_le Finset.univ
          (fun i : Fin d =>
            a (j, i) • fluctuationBasisCutoff Γ mf t (j, i) s)).trans ?_
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hB i s) (abs_nonneg _)
      simpa only [fluctuationObservationCutoffTest] using hsum
  choose C hC0 hC using hbound
  let D : ℝ := ∑ j : Fin m, (d : ℝ) * t j * C j
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (ht j)) (hC0 j)
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  by_cases hetop : e = ⊤
  · exact Eventually.of_forall fun _ => hetop ▸ le_top
  let η : ℝ := e.toReal
  have hη : 0 < η := ENNReal.toReal_pos he.ne' hetop
  have hofη : ENNReal.ofReal η = e := ENNReal.ofReal_toReal hetop
  obtain ⟨R, hR, htail⟩ :=
    fluctuationScaledErrorSup_tight Γ mf
      hConservative hBoundary hSolBound hF t ht z hz v₀ hinit η hη
  let q : ℝ := ε / (D * R + 1)
  have hden : 0 < D * R + 1 := by positivity
  have hq : 0 < q := div_pos hε hden
  have hbudget : D * q * R ≤ ε := by
    change D * (ε / (D * R + 1)) * R ≤ ε
    rw [show D * (ε / (D * R + 1)) * R =
      (D * R * ε) / (D * R + 1) by ring]
    apply (div_le_iff₀ hden).2
    nlinarith
  obtain ⟨δ, hδ, hlocal⟩ :=
    fluctuation_remainder_local_bound Γ mf
      hConservative hBoundary hSolBound hF t ht z hz v₀ hinit a q hq
  have herr (n : ℕ) (ω : (fluctuationModel Γ n).canonicalRecordΩ)
      (hY : (fluctuationTimeSup (fluctuationHorizon t)
        (fun s => ‖(fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω - mf.sol s‖)) ≤ δ) :
      |fluctuationError Γ mf t a n ω| ≤
        D * q * fluctuationScaledErrorSup Γ mf t n ω := by
    rw [fluctuationError, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt ((n + 1 : ℕ) : ℝ) *
          |∑ j : Fin m, fluctuationRemainder (fluctuationModel Γ n)
            (fluctuationObservationCutoffTest Γ mf t a j)
            mf.extendLeft.sol (t j) ω| ≤
        Real.sqrt ((n + 1 : ℕ) : ℝ) *
          ∑ j : Fin m, |fluctuationRemainder (fluctuationModel Γ n)
            (fluctuationObservationCutoffTest Γ mf t a j)
            mf.extendLeft.sol (t j) ω| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (Real.sqrt_nonneg _)
      _ = ∑ j : Fin m, Real.sqrt ((n + 1 : ℕ) : ℝ) *
          |fluctuationRemainder (fluctuationModel Γ n)
            (fluctuationObservationCutoffTest Γ mf t a j)
            mf.extendLeft.sol (t j) ω| := Finset.mul_sum _ _ _
      _ ≤ ∑ j : Fin m, ((d : ℝ) * t j * C j * q) *
          fluctuationScaledErrorSup Γ mf t n ω := by
        apply Finset.sum_le_sum
        intro j _
        exact hlocal n ω j (C j) (hC0 j) (fun s _ => hC j s) hY
      _ = D * q * fluctuationScaledErrorSup Γ mf t n ω := by
        simp only [D, Finset.sum_mul]
  filter_upwards [hsqrt.eventually (eventually_ge_atTop (R / δ))] with n hn
  have hscale : R ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) * δ :=
    (div_le_iff₀ hδ).mp hn
  have hσpos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.succ_pos n
  have hsub :
      {ω : (fluctuationModel Γ n).canonicalRecordΩ |
        ε < |fluctuationError Γ mf t a n ω|} ⊆
      {ω | R < fluctuationScaledErrorSup Γ mf t n ω} := by
    intro ω hω
    change R < fluctuationScaledErrorSup Γ mf t n ω
    by_contra hbad
    have hU : fluctuationScaledErrorSup Γ mf t n ω ≤ R :=
      le_of_not_gt hbad
    have hY : (fluctuationTimeSup (fluctuationHorizon t)
        (fun s => ‖(fluctuationModel Γ n).frozenDensityProcess
          (fluctuationModel Γ n).canonicalPathMap s ω - mf.sol s‖)) ≤ δ := by
      apply (mul_le_mul_iff_right₀ hσpos).mp
      exact hU.trans hscale
    have hsmall : |fluctuationError Γ mf t a n ω| ≤ ε :=
      (herr n ω hY).trans
        ((mul_le_mul_of_nonneg_left hU (mul_nonneg hD0 hq.le)).trans hbudget)
    exact (not_lt_of_ge hsmall) hω
  exact ((measure_mono hsub).trans (htail n)).trans_eq hofη

end RemainingModelStatements

/-! ## Theorem 4.2 -/

theorem kurtz_finite_dimensional_clt
    {d m : ℕ} [NeZero d] (Γ : RateSpec d)
    (mf : MeanFieldSolution d Γ)
    (hConservative : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).ConservativeJumps)
    (hBoundary : ∀ (N : ℕ) (hN : 0 < N),
      (DensityDepCTMC.mk N hN Γ).BoundaryCompatibleOnSimplex)
    (hSolBound : ∀ s : ℝ, 0 ≤ s → ‖mf.sol s‖ ≤ 1)
    (hF : ContDiff ℝ 1 Γ.drift)
    (t : Fin m → ℝ) (ht : ∀ j, 0 ≤ t j)
    (z : ∀ n : ℕ, Fin d → Fin (n + 1 + 1))
    (hz : ∀ n, (fluctuationModel Γ n).InSimplex (z n))
    (v₀ : Fin d → ℝ)
    (hinit : Tendsto
      (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) •
        ((fluctuationModel Γ n).scaledState (z n) - mf.sol 0))
      atTop (𝓝 v₀)) :
    (fluctuationCovariance Γ mf t).PosSemidef ∧
      Tendsto (fun n => fluctuationLaw Γ mf t z n) atTop
        (𝓝 (⟨ProbabilityTheory.multivariateGaussian
          (fluctuationMean Γ mf t v₀)
          (fluctuationCovariance Γ mf t), inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin m × Fin d)))) := by
  have hS := fluctuationCovariance_posSemidef_of_model Γ mf
    hConservative hBoundary hSolBound hF t z hz v₀ hinit
  refine ⟨hS, ?_⟩
  apply fluctuation_tendsto_gaussian_of_charFun
    (fun n => fluctuationLaw Γ mf t z n)
    (fluctuationMean Γ mf t v₀) (fluctuationCovariance Γ mf t) hS
  intro a
  have hchar := fluctuation_charFun_limit_of_scalar_steps Γ mf t hF z v₀ hinit a
    (fluctuation_scalar_decomposition Γ mf
      hConservative hBoundary hSolBound hF t ht z hz v₀ hinit a)
    (fluctuationNoise_charFun_tendsto Γ mf
      hConservative hBoundary hSolBound hF t ht z hz v₀ hinit a)
    (fluctuationError_tendsto Γ mf
      hConservative hBoundary hSolBound hF t ht z hz v₀ hinit a)
  simpa only [fluctuationLimitQuadratic] using hchar

end

end Ripple.Kurtz

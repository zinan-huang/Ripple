import Mathlib
import Ripple.Core.SurrogateCompilationBlowup
import Ripple.Core.Constructible
import Ripple.Core.CRNReadout

namespace Ripple

open MvPolynomial Filter Topology MeasureTheory

set_option maxHeartbeats 800000

variable {d : ℕ}

/-! ## B2: the missing clauses of the surrogate bound -/

/-- Away from the zero state the monomial bound is strict. -/
theorem abs_eval_lt_jointClock_of_ne_zero_journal {N : ℕ}
    (hN : Even N) (a : MIndex d N) (ha : a.degree ≤ N)
    {y : Fin d → ℝ} (hy : y ≠ 0) :
    |a.eval y| < jointClock N y := by
  classical
  by_cases hsmall : ‖y‖ ≤ 1
  · have hm : |a.eval y| ≤ 1 := by
      have hb := a.eval_bounded y 1 one_pos (fun i =>
        (by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i :
          |y i| ≤ ‖y‖).trans hsmall)
      simpa using hb
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra h
      push_neg at h
      apply hy
      funext i
      exact h i
    have hjpos : 0 < y j ^ N := by
      rw [← hN.pow_abs]
      exact pow_pos (abs_pos.mpr hj) N
    have hsum : y j ^ N ≤ ∑ i, y i ^ N :=
      Finset.single_le_sum (fun i _ => hN.pow_nonneg (y i))
        (Finset.mem_univ j)
    unfold jointClock
    linarith
  · push_neg at hsmall
    have hM : 0 < ‖y‖ := lt_trans one_pos hsmall
    have hb := a.eval_bounded y ‖y‖ hM (fun i =>
      by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i)
    have hp : ‖y‖ ^ a.degree ≤ ‖y‖ ^ N :=
      pow_le_pow_right₀ hsmall.le ha
    obtain ⟨j, hj⟩ : ∃ j, ‖y‖ ≤ |y j| := by
      by_contra h
      push_neg at h
      have : ‖y‖ < ‖y‖ :=
        (pi_norm_lt_iff hM).2 (fun i => by
          simpa [Real.norm_eq_abs] using h i)
      exact lt_irrefl _ this
    have hjN : ‖y‖ ^ N ≤ y j ^ N :=
      (pow_le_pow_left₀ (norm_nonneg _) hj N).trans_eq (hN.pow_abs (y j))
    have hsum : y j ^ N ≤ ∑ i, y i ^ N :=
      Finset.single_le_sum (fun i _ => hN.pow_nonneg (y i))
        (Finset.mem_univ j)
    unfold jointClock
    linarith

/-- The equality case requires positive even N, as in the paper. -/
theorem abs_eval_eq_jointClock_iff_journal {N : ℕ}
    (hN : Even N) (hNpos : 0 < N) (a : MIndex d N)
    (ha : a.degree ≤ N) (y : Fin d → ℝ) :
    |a.eval y| = jointClock N y ↔
      a = MIndex.zero' d N ∧ y = 0 := by
  classical
  constructor
  · intro heq
    have hy : y = 0 := by
      by_contra h
      exact (ne_of_lt
        (abs_eval_lt_jointClock_of_ne_zero_journal hN a ha h)) heq
    refine ⟨?_, hy⟩
    have hv : |a.eval (0 : Fin d → ℝ)| = 1 := by
      simpa [hy, jointClock, Nat.ne_of_gt hNpos] using heq
    funext i
    apply Fin.ext
    change (a i : ℕ) = 0
    by_contra hi
    have hz : a.eval (0 : Fin d → ℝ) = 0 := by
      unfold MIndex.eval
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hz, abs_zero] at hv
    norm_num at hv
  · rintro ⟨rfl, rfl⟩
    simp [jointClock, Nat.ne_of_gt hNpos]

/-- The zero surrogate is positive and at most one. -/
theorem jointSurrogate_zero_bounds_journal {N : ℕ}
    (hN : Even N) (y : Fin d → ℝ) :
    0 < jointSurrogate N (SurrogateIndex.zero d N) y ∧
      jointSurrogate N (SurrogateIndex.zero d N) y ≤ 1 := by
  have hp : 0 < jointSurrogate N (SurrogateIndex.zero d N) y := by
    unfold jointSurrogate
    rw [SurrogateIndex.zero_eval]
    exact div_pos one_pos (jointClock_pos hN y)
  exact ⟨hp, (le_abs_self _).trans
    (jointSurrogate_abs_le_one hN (SurrogateIndex.zero d N) y)⟩

/-- Componentwise nonnegative states give surrogates in [0,1]. -/
theorem jointSurrogate_mem_Icc_of_nonneg_journal {N : ℕ}
    (hN : Even N) (a : SurrogateIndex d N) (y : Fin d → ℝ)
    (hy : ∀ i, 0 ≤ y i) :
    jointSurrogate N a y ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (a.1.eval_nonneg y hy) (jointClock_pos hN y).le
  · exact (le_abs_self _).trans (jointSurrogate_abs_le_one hN a y)

/-- Even exponents give surrogates in [0,1], without a sign premise on y. -/
theorem jointSurrogate_mem_Icc_of_even_journal {N : ℕ}
    (hN : Even N) (a : SurrogateIndex d N) (y : Fin d → ℝ)
    (ha : ∀ i, Even (a.1 i : ℕ)) :
    jointSurrogate N a y ∈ Set.Icc (0 : ℝ) 1 := by
  have hm : 0 ≤ a.1.eval y := by
    unfold MIndex.eval
    exact Finset.prod_nonneg (fun i _ => (ha i).pow_nonneg (y i))
  exact ⟨div_nonneg hm (jointClock_pos hN y).le,
    (le_abs_self _).trans (jointSurrogate_abs_le_one hN a y)⟩

/-- The common coefficient-sum maximum. The range is finite and nonempty
(the output coordinate supplies an index), so this supremum is a maximum. -/
noncomputable def PolyPIVP.jointCoefficientMaximum (P : PolyPIVP d)
    (N : ℕ) : ℝ :=
  sSup (Set.range (fun i : Fin d =>
    ∑ b : MIndex d N, |(((P.field i).coeff b.toFinsupp : ℚ) : ℝ)|))

/-- One coefficient maximum bounds every component against the same clock. -/
theorem PolyPIVP.evalField_le_jointCoefficientMaximum (P : PolyPIVP d)
    {N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    0 ≤ P.jointCoefficientMaximum N ∧
      ∀ (i : Fin d) (y : Fin d → ℝ),
        |P.evalField y i| ≤ P.jointCoefficientMaximum N * jointClock N y := by
  classical
  let c : Fin d → ℝ := fun i =>
    ∑ b : MIndex d N, |(((P.field i).coeff b.toFinsupp : ℚ) : ℝ)|
  have hbdd : BddAbove (Set.range c) := (Set.finite_range c).bddAbove
  have hmax : ∀ i, c i ≤ P.jointCoefficientMaximum N := by
    intro i
    change c i ≤ sSup (Set.range c)
    exact le_csSup hbdd ⟨i, rfl⟩
  have hc : 0 ≤ c P.output := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨hc.trans (hmax P.output), ?_⟩
  intro i y
  calc
    |P.evalField y i| ≤ c i * jointClock N y :=
      abs_eval₂_le_jointClock hN (P.field i) (hdeg i) y
    _ ≤ P.jointCoefficientMaximum N * jointClock N y :=
      mul_le_mul_of_nonneg_right (hmax i) (jointClock_pos hN y).le

/-! ## B6: a common compact-set field and trajectory-length bound -/

/-- The same v bounds the field on the specified compact D and length along
any supplied solution remaining in D. -/
theorem PolyPIVP.arcLength_and_field_le_of_isCompact (P : PolyPIVP d)
    (sol : PIVP.Solution P.toPIVP) (D : Set (Fin d → ℝ))
    (hD : IsCompact D) (htraj : ∀ t, 0 ≤ t → sol.trajectory t ∈ D) :
    ∃ v : ℝ, 0 ≤ v ∧ (∀ z ∈ D, ‖P.evalField z‖ ≤ v) ∧
      ∀ t, 0 ≤ t → P.arcLength sol.trajectory t ≤ v * t := by
  obtain ⟨v, hv⟩ :=
    hD.exists_bound_of_continuousOn P.continuous_evalField.continuousOn
  have hvD : ∀ z ∈ D, ‖P.evalField z‖ ≤ max v 0 :=
    fun z hz => (hv z hz).trans (le_max_left _ _)
  refine ⟨max v 0, le_max_right _ _, hvD, ?_⟩
  intro t ht
  have hle : P.arcLength sol.trajectory t ≤
      ∫ _u in (0 : ℝ)..t, max v 0 := by
    exact intervalIntegral.integral_mono_on ht
      ((P.speed_continuousOn sol 0 t le_rfl).intervalIntegrable_of_Icc ht)
      intervalIntegrable_const (fun u hu => hvD _ (htraj u hu.1))
  simpa [mul_comm] using hle

/-! ## B7: retain the exact clock modulus in the certificate -/

/-- The old polynomial compilation export, with the constructed modulus
mu'(r) = integral[0,mu(r)] jointClock retained in the statement. -/
theorem bounded_compilation_polyTime_clock_certified {α : ℝ} (P : PolyPIVP d)
    (sol : PIVP.Solution P.toPIVP) (μ : TimeModulus) (k : ℕ) (C : ℝ)
    (hconv : ∀ r : ℕ, ∀ t : ℝ, t > μ r →
      |sol.trajectory t P.output - α| < Real.exp (-(r : ℝ)))
    (hμ : ∀ r : ℕ, 0 ≤ μ r ∧ μ r ≤ C * ((r : ℝ) + 1) ^ k)
    (hL : ∀ r : ℕ, P.arcLength sol.trajectory (μ r) ≤ C * ((r : ℝ) + 1) ^ k)
    {N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim d N) α,
      btc.pivp = P.jointSurrogateCompile N ∧
      (∀ r : ℕ, btc.modulus r =
        ∫ u in (0 : ℝ)..(μ r), jointClock N (sol.trajectory u)) ∧
      (∃ C' : ℝ, 0 < C' ∧ ∀ r : ℕ,
        btc.modulus r ≤ C' * ((r : ℝ) + 1) ^ (k * (N + 1))) ∧
      (∃ v : ℝ, 0 ≤ v ∧ ∀ τ, 0 ≤ τ →
        btc.pivp.arcLength btc.sol.trajectory τ ≤ v * τ) := by
  obtain ⟨sol', s, -, hs0, hsm, -, hclock, hout, hsur⟩ :=
    P.jointSurrogateCompile_solution hN hdeg sol
  have hs_nn : ∀ τ, 0 ≤ τ → 0 ≤ s τ := fun τ hτ => hs0 ▸ hsm.monotone hτ
  have hlim := tendsto_of_modulus μ hconv
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_tendsto
    (fun t ht => (continuous_apply P.output).continuousAt.comp
      ((sol.is_solution t ht).continuousAt)) hlim
  have hbd := jointSurrogateCompile_isBounded P hN sol' (fun τ => sol.trajectory (s τ))
    hout hsur (fun τ hτ => hM _ (hs_nn τ hτ))
  have hclk_cont : ∀ a b, 0 ≤ a →
      ContinuousOn (fun u => jointClock N (sol.trajectory u)) (Set.Icc a b) :=
    fun a b ha u hu => ((continuous_jointClock N).continuousAt.comp
      (P.solution_continuousAt sol (ha.trans hu.1))).continuousWithinAt
  have hθ_nn : ∀ t, 0 ≤ t →
      0 ≤ ∫ u in (0 : ℝ)..t, jointClock N (sol.trajectory u) :=
    fun t ht => intervalIntegral.integral_nonneg ht
      (fun u _ => zero_le_one.trans (jointClock_ge_one hN _))
  have hconv' : ∀ r : ℕ, ∀ τ : ℝ,
      τ > (fun r : ℕ => ∫ u in (0 : ℝ)..(μ r), jointClock N (sol.trajectory u)) r →
      |sol'.trajectory τ (P.jointSurrogateCompile N).output - α| <
        Real.exp (-(r : ℝ)) := by
    intro r τ hτ
    have hτ0 : 0 ≤ τ := (hθ_nn _ (hμ r).1).trans hτ.le
    have hsτ : μ r < s τ := by
      have := hsm hτ
      rwa [hclock _ (hμ r).1] at this
    rw [hout τ hτ0]
    exact hconv r (s τ) hsτ
  obtain ⟨btc, hbtc, hmod, -⟩ :=
    CertifiedBoundedTimeComputable.exists_of_solution _ sol' hbd _ hconv'
  refine ⟨btc, hbtc, ?_, ?_, ?_⟩
  · intro r
    rw [hmod r, max_eq_right (hθ_nn _ (hμ r).1)]
  · have hC : 0 ≤ C := by
      have := (hμ 0).1.trans (hμ 0).2
      simpa using this
    obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = ∑ i, |(P.init i : ℝ)| := ⟨_, rfl⟩
    have hc₀_nn : 0 ≤ c₀ := hc₀ ▸ Finset.sum_nonneg (fun i _ => abs_nonneg _)
    obtain ⟨K, hK⟩ : ∃ K : ℝ,
        K = C * (1 + (d : ℝ) * (c₀ + C) ^ N) := ⟨_, rfl⟩
    refine ⟨max K 1, lt_max_of_lt_right one_pos, fun r => ?_⟩
    rw [hmod r, max_eq_right (hθ_nn _ (hμ r).1)]
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((r : ℝ) + 1) ^ k := ⟨_, rfl⟩
    have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) r
      linarith
    have hq1 : 1 ≤ q := hq ▸ one_le_pow₀ hr1
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = c₀ + C * q := ⟨_, rfl⟩
    have hLr : P.arcLength sol.trajectory (μ r) ≤ C * q := hq ▸ hL r
    have hcoord : ∀ u ∈ Set.Icc 0 (μ r), ∀ i, |sol.trajectory u i| ≤ B := by
      intro u hu i
      have h1 := P.abs_sub_init_le_arcLength sol i hu.1
      have h2 := P.arcLength_mono sol hu.1 hu.2
      have h3 : |(P.init i : ℝ)| ≤ c₀ := hc₀ ▸
        Finset.single_le_sum (f := fun i => |(P.init i : ℝ)|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ i)
      have h4 := abs_sub_abs_le_abs_sub (sol.trajectory u i) (P.init i : ℝ)
      rw [hB]
      linarith
    have hclk_le : ∀ u ∈ Set.Icc 0 (μ r),
        jointClock N (sol.trajectory u) ≤ 1 + (d : ℝ) * B ^ N := by
      intro u hu
      unfold jointClock
      have : ∑ i, sol.trajectory u i ^ N ≤ ∑ _i : Fin d, B ^ N :=
        Finset.sum_le_sum (fun i _ => by
          rw [← hN.pow_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord u hu i) N)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      linarith
    have hθle : (∫ u in (0 : ℝ)..(μ r), jointClock N (sol.trajectory u)) ≤
        μ r * (1 + (d : ℝ) * B ^ N) := by
      have h := intervalIntegral.integral_mono_on (hμ r).1
        ((hclk_cont 0 (μ r) le_rfl).intervalIntegrable_of_Icc
          (μ := MeasureTheory.volume) (hμ r).1)
        ((continuous_const : Continuous fun _ : ℝ => 1 + (d : ℝ) * B ^ N).intervalIntegrable
          (μ := MeasureTheory.volume) _ _) hclk_le
      simpa [mul_comm] using h
    have hB_le : B ≤ (c₀ + C) * q := by
      have : c₀ ≤ c₀ * q := le_mul_of_one_le_right hc₀_nn hq1
      rw [hB]
      nlinarith
    have hB_nn : 0 ≤ B := by rw [hB]; positivity
    have hBN : B ^ N ≤ (c₀ + C) ^ N * q ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hB_nn hB_le N
    have hqN : q * q ^ N = ((r : ℝ) + 1) ^ (k * (N + 1)) := by
      rw [hq, ← pow_succ', ← pow_mul, mul_comm]
    have hq_le : q ≤ ((r : ℝ) + 1) ^ (k * (N + 1)) := by
      rw [hq]
      exact pow_le_pow_right₀ hr1 (Nat.le_mul_of_pos_right k (Nat.succ_pos N))
    have hμr : μ r ≤ C * q := hq ▸ (hμ r).2
    have hq0 : 0 ≤ q := le_trans zero_le_one hq1
    calc
      (∫ u in (0 : ℝ)..(μ r), jointClock N (sol.trajectory u))
          ≤ μ r * (1 + (d : ℝ) * B ^ N) := hθle
      _ ≤ (C * q) * (1 + (d : ℝ) * ((c₀ + C) ^ N * q ^ N)) := by gcongr
      _ = C * q + C * (d : ℝ) * (c₀ + C) ^ N * (q * q ^ N) := by ring
      _ ≤ C * ((r : ℝ) + 1) ^ (k * (N + 1)) +
          C * (d : ℝ) * (c₀ + C) ^ N * ((r : ℝ) + 1) ^ (k * (N + 1)) := by
        rw [hqN]
        gcongr
      _ = K * ((r : ℝ) + 1) ^ (k * (N + 1)) := by rw [hK]; ring
      _ ≤ max K 1 * ((r : ℝ) + 1) ^ (k * (N + 1)) := by
        gcongr
        exact le_max_left _ _
  · exact btc.pivp.arcLength_le_of_bounded btc.sol btc.bounded

/-! ## B8: an explicit bounded difference from iterated logarithms -/

namespace Constructible

/-- Every fixed iterate of log tends to infinity. -/
theorem iteratedLog_tendsto_atTop_journal (k : ℕ) :
    Tendsto (Real.log^[k]) atTop atTop := by
  induction k with
  | zero => exact tendsto_id
  | succ k ih =>
      rw [Function.iterate_succ']
      exact Real.tendsto_log_atTop.comp ih

/-- An explicit eventual estimate, with depth-dependent constant k. -/
theorem L_sub_iteratedLog_eventually (k : ℕ) :
    ∀ᶠ t : ℝ in atTop,
      0 ≤ L k t - (Real.log^[k]) t ∧
      L k t - (Real.log^[k]) t ≤ (k : ℝ) := by
  induction k with
  | zero =>
      filter_upwards [] with t
      simp [L]
  | succ k ih =>
      have hlarge : ∀ᶠ t : ℝ in atTop, (1 : ℝ) ≤ (Real.log^[k]) t :=
        (iteratedLog_tendsto_atTop_journal k).eventually (eventually_ge_atTop 1)
      filter_upwards [ih, hlarge] with t h hlarge
      let a : ℝ := (Real.log^[k]) t
      let b : ℝ := L k t
      change 0 ≤ b - a ∧ b - a ≤ (k : ℝ) at h
      have ha : 1 ≤ a := hlarge
      have hap : 0 < a := by linarith
      have hbp : 0 < 1 + b := by linarith [h.1]
      have hlo : 0 ≤ Real.log (1 + b) - Real.log a :=
        sub_nonneg.mpr (Real.log_le_log hap (by linarith [h.1]))
      have hka : (k : ℝ) + 1 ≤ ((k : ℝ) + 1) * a :=
        le_mul_of_one_le_right (by positivity) ha
      have hratio : (1 + b) / a ≤ (k : ℝ) + 2 := by
        apply (div_le_iff₀ hap).2
        nlinarith [h.2]
      have hlog : Real.log ((1 + b) / a) ≤ (1 + b) / a - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hbp hap)
      have hu : Real.log (1 + b) - Real.log a ≤ (k : ℝ) + 1 := by
        rw [← Real.log_div hbp.ne' hap.ne']
        linarith
      simpa only [L, Function.iterate_succ_apply', Nat.cast_succ] using And.intro hlo hu

/-- In particular L_k(t) = log^[k](t) + O(1), with an explicit constant. -/
theorem L_iteratedLog_eventual_abs_bound (k : ℕ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      |L k t - (Real.log^[k]) t| ≤ (k : ℝ) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (L_sub_iteratedLog_eventually k)
  refine ⟨T, ?_⟩
  intro t ht
  rw [abs_of_nonneg (hT t ht).1]
  exact (hT t ht).2

end Constructible

/-! ## A3: exact cancellation alternatives, including logarithmic speed -/

namespace CRNReadout

/-- A nonzero scaled exponential limit determines the logarithmic speed. -/
theorem exponential_speed_of_scaled_limit {f : ℝ → ℝ} {a c : ℝ}
    (hc : c ≠ 0)
    (hlim : Tendsto (fun t => Real.exp (a * t) * f t) atTop (𝓝 c)) :
    Tendsto (fun t => -Real.log |f t| / t) atTop (𝓝 a) := by
  have habs : Tendsto (fun t => |Real.exp (a * t) * f t|) atTop (𝓝 |c|) :=
    hlim.abs
  have hlog : Tendsto (fun t => Real.log |Real.exp (a * t) * f t|)
      atTop (𝓝 (Real.log |c|)) :=
    (Real.continuousAt_log (abs_pos.mpr hc).ne').tendsto.comp habs
  have hquot : Tendsto (fun t => Real.log |Real.exp (a * t) * f t| / t)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      hlog.mul (tendsto_inv_atTop_zero :
        Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have hbase : Tendsto (fun t => a - Real.log |Real.exp (a * t) * f t| / t)
      atTop (𝓝 a) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => a) atTop (𝓝 a)).sub hquot)
  have hnon : ∀ᶠ t : ℝ in atTop, 0 < |Real.exp (a * t) * f t| :=
    habs.eventually (Ioi_mem_nhds (abs_pos.mpr hc))
  refine hbase.congr' ?_
  filter_upwards [hnon, eventually_gt_atTop (0 : ℝ)] with t ht htp
  have hf : f t ≠ 0 := by
    intro hz
    simp [hz] at ht
  have hlogeq : Real.log |Real.exp (a * t) * f t| = a * t + Real.log |f t| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _),
      Real.log_mul (Real.exp_pos _).ne' (abs_pos.mpr hf).ne', Real.log_exp]
  rw [hlogeq]
  field_simp [htp.ne'] <;> ring

/-- The slow-exponential coefficient is the exact scaled limit. -/
theorem module_limited_scaled_tendsto {α β Cε : ℝ} (hβα : α < β)
    {δ : ℝ → ℝ}
    (hδ : ∀ t, 0 ≤ t →
      HasDerivAt δ (-α * δ t + α * (Cε * Real.exp (-β * t))) t) :
    Tendsto (fun t => Real.exp (α * t) * δ t) atTop
      (𝓝 (δ 0 + α * Cε / (β - α))) := by
  let D : ℝ := α * Cε / (β - α)
  let A : ℝ := δ 0 + D
  have hlin : Tendsto (fun t : ℝ => -((β - α) * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      (Tendsto.const_mul_atTop (sub_pos.mpr hβα) tendsto_id)
  have hdec := Real.tendsto_exp_atBot.comp hlin
  have hb : Tendsto (fun t : ℝ => A - D * Real.exp (-((β - α) * t)))
      atTop (𝓝 A) := by
    simpa only [mul_zero, sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => A) atTop (𝓝 A)).sub
        (hdec.const_mul D))
  refine hb.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have he : Real.exp (α * t) * Real.exp (-α * t) = 1 := by
    rw [← Real.exp_add, show α * t + -α * t = 0 by ring, Real.exp_zero]
  have hecross : Real.exp (α * t) * Real.exp (-β * t) =
      Real.exp (-((β - α) * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hscaled : Real.exp (α * t) * δ t =
      A - D * Real.exp (-((β - α) * t)) := by
    rw [module_limited (ne_of_lt hβα) hδ ht]
    change Real.exp (α * t) * (A * Real.exp (-α * t) - D * Real.exp (-β * t)) = _
    calc
      _ = A * (Real.exp (α * t) * Real.exp (-α * t)) -
          D * (Real.exp (α * t) * Real.exp (-β * t)) := by ring
      _ = A - D * Real.exp (-((β - α) * t)) := by rw [he, hecross, mul_one]
  exact hscaled.symm

/-- If the slow coefficient is nonzero, the speed is α. -/
theorem module_limited_slow_speed {α β Cε : ℝ} (hβα : α < β)
    {δ : ℝ → ℝ}
    (hδ : ∀ t, 0 ≤ t →
      HasDerivAt δ (-α * δ t + α * (Cε * Real.exp (-β * t))) t)
    (hcoef : δ 0 + α * Cε / (β - α) ≠ 0) :
    Tendsto (fun t => -Real.log |δ t| / t) atTop (𝓝 α) :=
  exponential_speed_of_scaled_limit hcoef (module_limited_scaled_tendsto hβα hδ)

/-- The exceptional initial value cancels the slow exponential exactly. -/
theorem module_limited_cancelled {α β Cε : ℝ} (hαβ : α ≠ β)
    {δ : ℝ → ℝ}
    (hδ : ∀ t, 0 ≤ t →
      HasDerivAt δ (-α * δ t + α * (Cε * Real.exp (-β * t))) t)
    (hcoef : δ 0 + α * Cε / (β - α) = 0) {t : ℝ} (ht : 0 ≤ t) :
    δ t = -(α * Cε / (β - α)) * Real.exp (-β * t) := by
  rw [module_limited hαβ hδ ht, hcoef]
  ring

/-- The remaining coefficient is the exact β-scaled limit in the cancelled case. -/
theorem module_limited_cancelled_scaled {α β Cε : ℝ} (hαβ : α ≠ β)
    {δ : ℝ → ℝ}
    (hδ : ∀ t, 0 ≤ t →
      HasDerivAt δ (-α * δ t + α * (Cε * Real.exp (-β * t))) t)
    (hcoef : δ 0 + α * Cε / (β - α) = 0) :
    Tendsto (fun t => Real.exp (β * t) * δ t) atTop
      (𝓝 (-(α * Cε / (β - α)))) := by
  let D : ℝ := α * Cε / (β - α)
  have heq : (fun t => Real.exp (β * t) * δ t) =ᶠ[atTop] (fun _ => -D) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [module_limited_cancelled hαβ hδ hcoef ht]
    have he : Real.exp (β * t) * Real.exp (-β * t) = 1 := by
      rw [← Real.exp_add, show β * t + -β * t = 0 by ring, Real.exp_zero]
    change Real.exp (β * t) * (-D * Real.exp (-β * t)) = -D
    calc
      _ = -D * (Real.exp (β * t) * Real.exp (-β * t)) := by ring
      _ = -D := by rw [he, mul_one]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => -D) atTop (𝓝 (-D))).congr' heq.symm

/-- In the positive-rate regime, a nonzero forcing coefficient gives speed β
when the slow coefficient vanishes. -/
theorem module_limited_cancelled_speed {α β Cε : ℝ}
    (hα : 0 < α) (hβα : α < β) {δ : ℝ → ℝ}
    (hδ : ∀ t, 0 ≤ t →
      HasDerivAt δ (-α * δ t + α * (Cε * Real.exp (-β * t))) t)
    (hcoef : δ 0 + α * Cε / (β - α) = 0) (hC : Cε ≠ 0) :
    Tendsto (fun t => -Real.log |δ t| / t) atTop (𝓝 β) := by
  have hD : -(α * Cε / (β - α)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hα.ne' hC)
      (sub_ne_zero.mpr (ne_of_gt hβα)))
  exact exponential_speed_of_scaled_limit hD
    (module_limited_cancelled_scaled (ne_of_lt hβα) hδ hcoef)

/-- Vanishing forcing and the exceptional initial value give zero error. -/
theorem module_limited_cancelled_zero {α β Cε : ℝ} (hαβ : α ≠ β)
    {δ : ℝ → ℝ}
    (hδ : ∀ t, 0 ≤ t →
      HasDerivAt δ (-α * δ t + α * (Cε * Real.exp (-β * t))) t)
    (hcoef : δ 0 + α * Cε / (β - α) = 0) (hC : Cε = 0) :
    ∀ t, 0 ≤ t → δ t = 0 := by
  intro t ht
  simpa [hC] using module_limited_cancelled hαβ hδ hcoef ht

/-! ## B10: fixed inversion parameters and every admissible k -/

/-- The square-error comparison used by the fixed-parameter export. -/
theorem invFilter_energy_comparison_journal {α : ℝ} (hα : 0 < α)
    {x : ℝ → ℝ} (hx : Continuous x) (q₀ : ℝ) {T t η : ℝ}
    (hTt : T ≤ t)
    (hxlo : ∀ s ∈ Set.Ioo T t, α / 2 ≤ x s)
    (hη : ∀ s ∈ Set.Ioo T t, |x s - α| ≤ η) :
    (invFilter x q₀ t - 1 / α) ^ 2 ≤
      4 * η ^ 2 * (1 / α) ^ 4 +
        ((invFilter x q₀ T - 1 / α) ^ 2 - 4 * η ^ 2 * (1 / α) ^ 4) *
          Real.exp (-(α / 2 * (t - T))) := by
  let w : ℝ := 1 / α
  have hw : α * w = 1 := mul_one_div_cancel hα.ne'
  have hc : Continuous (fun s => (invFilter x q₀ s - w) ^ 2) :=
    ((invFilter_continuous hx q₀).sub continuous_const).pow 2
  have hd : ∀ s, HasDerivAt (fun u => (invFilter x q₀ u - w) ^ 2)
      (2 * (invFilter x q₀ s - w) * (1 - x s * invFilter x q₀ s)) s := by
    intro s
    refine (((invFilter_hasDerivAt hx q₀ s).sub_const w).pow 2).congr_deriv ?_
    norm_num <;> ring
  refine comparison (V := fun s => (invFilter x q₀ s - w) ^ 2)
    hTt hc.continuousOn (fun s _ => hd s) (fun s hs => ?_)
  have hD : (x s - α) ^ 2 ≤ η ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hη s hs) 2
  exact lyapunov_step hα hw (hxlo s hs) hD

/-- Lemma 7.3 with the prescribed constants and EVERY admissible k.
No monotonicity of μ and no sign premise on q₀ are used. -/
theorem invFilter_fixedParameters {α : ℝ} (hα : 0 < α)
    {x : ℝ → ℝ} (hx : Continuous x) (q₀ : ℝ) (μ : TimeModulus)
    (hμ : ∀ r : ℕ, ∀ t : ℝ, μ r < t → |x t - α| < Real.exp (-(r : ℝ)))
    (r₀ : ℕ) (hr₀ : Real.exp (-(r₀ : ℝ)) ≤ α / 2) :
    let T₀ : ℝ := max (μ r₀) 0
    let K : ℝ := (invFilter x q₀ T₀ - 1 / α) ^ 2 + 1 / α ^ 2
    let Cq : ℝ := (2 / α) * max (Real.log (2 * K)) 0
    (∀ t, T₀ ≤ t → (invFilter x q₀ t - 1 / α) ^ 2 ≤ K) ∧
      ∀ k : ℕ, 8 / α ^ 4 ≤ Real.exp (2 * (k : ℝ)) →
        ∀ (r : ℕ) (t : ℝ),
          max (μ (r + k)) T₀ + (4 / α) * r + Cq < t →
            |invFilter x q₀ t - 1 / α| < Real.exp (-(r : ℝ)) := by
  let T₀ : ℝ := max (μ r₀) 0
  let q : ℝ → ℝ := invFilter x q₀
  let w : ℝ := 1 / α
  let K : ℝ := (q T₀ - w) ^ 2 + 1 / α ^ 2
  let M : ℝ := max (Real.log (2 * K)) 0
  change (∀ t, T₀ ≤ t → (q t - w) ^ 2 ≤ K) ∧
    ∀ k : ℕ, 8 / α ^ 4 ≤ Real.exp (2 * (k : ℝ)) →
      ∀ (r : ℕ) (t : ℝ),
        max (μ (r + k)) T₀ + (4 / α) * r + (2 / α) * M < t →
          |q t - w| < Real.exp (-(r : ℝ))
  have hT₀μ : μ r₀ ≤ T₀ := le_max_left _ _
  have hK0 : 0 < K := by dsimp [K]; positivity
  have hM0 : 0 ≤ M := le_max_right _ _
  have hML : Real.log (2 * K) ≤ M := le_max_left _ _
  have hxlo : ∀ s, T₀ < s → α / 2 ≤ x s ∧ |x s - α| ≤ α / 2 := by
    intro s hs
    have habs : |x s - α| ≤ α / 2 :=
      (hμ r₀ s (hT₀μ.trans_lt hs)).le.trans hr₀
    exact ⟨by have h := (abs_le.mp habs).1; linarith, habs⟩
  have hbase : 4 * (α / 2) ^ 2 * w ^ 4 = 1 / α ^ 2 := by
    dsimp [w]
    field_simp [hα.ne'] <;> ring
  have hbound : ∀ t, T₀ ≤ t → (q t - w) ^ 2 ≤ K := by
    intro t ht
    have h := invFilter_energy_comparison_journal hα hx q₀ (T := T₀)
      (t := t) (η := α / 2) ht
      (fun s hs => (hxlo s hs.1).1) (fun s hs => (hxlo s hs.1).2)
    change (q t - w) ^ 2 ≤ 4 * (α / 2) ^ 2 * w ^ 4 +
      ((q T₀ - w) ^ 2 - 4 * (α / 2) ^ 2 * w ^ 4) *
        Real.exp (-(α / 2 * (t - T₀))) at h
    rw [hbase] at h
    have hE0 := (Real.exp_pos (-(α / 2 * (t - T₀)))).le
    have hE1 : Real.exp (-(α / 2 * (t - T₀))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have hc0 : 0 ≤ 1 / α ^ 2 := by positivity
    have hterm : ((q T₀ - w) ^ 2 - 1 / α ^ 2) *
        Real.exp (-(α / 2 * (t - T₀))) ≤ (q T₀ - w) ^ 2 := by
      calc
        _ ≤ (q T₀ - w) ^ 2 * Real.exp (-(α / 2 * (t - T₀))) :=
          mul_le_mul_of_nonneg_right (by linarith) hE0
        _ ≤ (q T₀ - w) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hE1 (sq_nonneg _)
        _ = (q T₀ - w) ^ 2 := mul_one _
    dsimp only [K]
    linarith
  refine ⟨hbound, ?_⟩
  intro k hk r t ht
  let T₁ : ℝ := max (μ (r + k)) T₀
  have hT₁a : μ (r + k) ≤ T₁ := le_max_left _ _
  have hT₁b : T₀ ≤ T₁ := le_max_right _ _
  change T₁ + (4 / α) * r + (2 / α) * M < t at ht
  have hT₁t : T₁ ≤ t := by
    have hn : 0 ≤ (4 / α) * (r : ℝ) + (2 / α) * M := by positivity
    linarith
  let η : ℝ := Real.exp (-((r + k : ℕ) : ℝ))
  let ρ : ℝ := Real.exp (-(r : ℝ))
  let E : ℝ := Real.exp (-(k : ℝ))
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hηρ : η = ρ * E := by
    dsimp [η, ρ, E]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hwfour : w ^ 4 = 1 / α ^ 4 := by
    dsimp [w]
    rw [div_pow, one_pow]
  have hkW : 8 * w ^ 4 ≤ Real.exp (2 * (k : ℝ)) := by
    rw [hwfour, mul_one_div]
    exact hk
  have hEinv : E ^ 2 * Real.exp (2 * (k : ℝ)) = 1 := by
    dsimp [E]
    rw [sq, ← Real.exp_add, ← Real.exp_add,
      show -(k : ℝ) + -(k : ℝ) + 2 * (k : ℝ) = 0 by ring, Real.exp_zero]
  have hsmall : 8 * w ^ 4 * E ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hkW (sq_nonneg E)
    have he : Real.exp (2 * (k : ℝ)) * E ^ 2 = 1 := by
      rw [mul_comm]
      exact hEinv
    rwa [he] at h
  have hcoeff : 4 * E ^ 2 * w ^ 4 ≤ 1 / 2 := by nlinarith
  have hnoise : 4 * η ^ 2 * w ^ 4 ≤ ρ ^ 2 / 2 := by
    calc
      4 * η ^ 2 * w ^ 4 = ρ ^ 2 * (4 * E ^ 2 * w ^ 4) := by rw [hηρ]; ring
      _ ≤ ρ ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left hcoeff (sq_nonneg ρ)
      _ = ρ ^ 2 / 2 := by ring
  have h := invFilter_energy_comparison_journal hα hx q₀ (T := T₁)
    (t := t) (η := η) hT₁t
    (fun s hs => (hxlo s (hT₁b.trans_lt hs.1)).1)
    (fun s hs => (hμ (r + k) s (hT₁a.trans_lt hs.1)).le)
  change (q t - w) ^ 2 ≤ 4 * η ^ 2 * w ^ 4 +
    ((q T₁ - w) ^ 2 - 4 * η ^ 2 * w ^ 4) *
      Real.exp (-(α / 2 * (t - T₁))) at h
  have hVT := hbound T₁ hT₁b
  have htime : (4 / α) * (r : ℝ) + (2 / α) * M < t - T₁ := by linarith
  have halg : α / 2 * ((4 / α) * (r : ℝ) + (2 / α) * M) =
      2 * (r : ℝ) + M := by
    field_simp [hα.ne'] <;> ring
  have hmul := mul_lt_mul_of_pos_left htime (by positivity : (0 : ℝ) < α / 2)
  rw [halg] at hmul
  have hlt : 2 * (r : ℝ) + Real.log (2 * K) < α / 2 * (t - T₁) := by linarith
  have hE : Real.exp (-(α / 2 * (t - T₁))) <
      Real.exp (-(2 * (r : ℝ) + Real.log (2 * K))) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hEK : Real.exp (-(2 * (r : ℝ) + Real.log (2 * K))) * (2 * K) = ρ ^ 2 := by
    have hh : Real.exp (-(2 * (r : ℝ) + Real.log (2 * K))) *
        Real.exp (Real.log (2 * K)) = ρ ^ 2 := by
      dsimp [ρ]
      rw [← Real.exp_add, sq, ← Real.exp_add]
      congr 1
      ring
    rwa [Real.exp_log (by positivity)] at hh
  have hE0 := (Real.exp_pos (-(α / 2 * (t - T₁)))).le
  have hc0 : 0 ≤ 4 * η ^ 2 * w ^ 4 := by positivity
  have hterm : ((q T₁ - w) ^ 2 - 4 * η ^ 2 * w ^ 4) *
      Real.exp (-(α / 2 * (t - T₁))) ≤
        K * Real.exp (-(α / 2 * (t - T₁))) :=
    mul_le_mul_of_nonneg_right (by linarith) hE0
  have hdec : K * Real.exp (-(α / 2 * (t - T₁))) < ρ ^ 2 / 2 := by
    have hm := mul_lt_mul_of_pos_left hE hK0
    nlinarith [hEK]
  have hfin : (q t - w) ^ 2 < ρ ^ 2 := by linarith
  exact abs_lt_of_sq_lt_sq hfin hρ0.le

end CRNReadout

end Ripple

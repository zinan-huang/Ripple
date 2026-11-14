-- Ripple/Kurtz/StrongApprox/SectionFourTails.lean
import Ripple.Kurtz.StrongApprox.SectionFourAssembly
import Ripple.Analysis.LinearVolterra

/-!
# Section 4: pathwise Gronwall, Taylor remainder, and tail combination

The parts of this section that need no stochastic integral.

* `gronwall_norm_le`, `pathSupIcc_le_gronwall` (U1) and `linear_volterra_norm_le`,
  `pathSupIcc_le_linear_volterra` (R3): pathwise Gronwall bounds for suprema over `[0, T]`.
* `taylor_remainder_le`, `scaled_taylor_remainder_le`, `taylor_forcing_bound` (R2).
* `sectionFour_U_tail` (U3) and `sectionFour_R_tail`, `sectionFour_R_expMoment` (R5, R6):
  tail combination as abstract probability lemmas. The maximal-inequality inputs are hypotheses on
  given random variables; their producers are listed at each statement.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace Ripple.Kurtz.StrongApprox.SectionFourAssembly

/-! ## Gronwall -/

section Gronwall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pathwise Gronwall: `D t = M t + ∫₀ᵗ Fd`, `‖Fd‖ ≤ L ‖D‖`, `‖M‖ ≤ s` on `[0, T]` give
`‖D t‖ ≤ s e^{L t}`. -/
theorem gronwall_norm_le {T L s : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hs : 0 ≤ s)
    {D M Fd : ℝ → E} (hD : Continuous D) (hFd : ContinuousOn Fd (Icc 0 T))
    (hM : ∀ t ∈ Icc 0 T, ‖M t‖ ≤ s)
    (hEq : ∀ t ∈ Icc 0 T, D t = M t + ∫ u in (0 : ℝ)..t, Fd u)
    (hF : ∀ u ∈ Icc 0 T, ‖Fd u‖ ≤ L * ‖D u‖) :
    ∀ t ∈ Icc 0 T, ‖D t‖ ≤ s * Real.exp (L * t) := by
  refine Ripple.Analysis.LinearVolterra.integral_gronwall_continuous hD.norm hT hs hL
    (fun t _ => norm_nonneg _) ?_
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht0]; exact Icc_subset_Icc le_rfl ht.2
  have hFdi : IntervalIntegrable (fun u => ‖Fd u‖) volume 0 t :=
    (hFd.mono hsub).norm.intervalIntegrable
  have hDi : IntervalIntegrable (fun u => L * ‖D u‖) volume 0 t :=
    (continuous_const.mul hD.norm).intervalIntegrable _ _
  calc ‖D t‖ = ‖M t + ∫ u in (0 : ℝ)..t, Fd u‖ := by rw [← hEq t ht]
    _ ≤ ‖M t‖ + ‖∫ u in (0 : ℝ)..t, Fd u‖ := norm_add_le _ _
    _ ≤ s + ∫ u in (0 : ℝ)..t, ‖Fd u‖ :=
        add_le_add (hM t ht) (intervalIntegral.norm_integral_le_integral_norm ht0)
    _ ≤ s + ∫ u in (0 : ℝ)..t, L * ‖D u‖ := by
        gcongr
        exact intervalIntegral.integral_mono_on ht0 hFdi hDi (fun u hu =>
          hF u ⟨hu.1, hu.2.trans ht.2⟩)

/-- The linear Volterra form (R1): `E = H + ∫ A E + Q` with `‖A‖ ≤ L1`. -/
theorem linear_volterra_norm_le {T L1 sH sQ : ℝ} (hT : 0 ≤ T) (hL1 : 0 ≤ L1)
    (hsH : 0 ≤ sH) (hsQ : 0 ≤ sQ)
    {A : ℝ → E →L[ℝ] E} {Ef H Q : ℝ → E} (hE : Continuous Ef)
    (hAE : ContinuousOn (fun u => A u (Ef u)) (Icc 0 T))
    (hH : ∀ t ∈ Icc 0 T, ‖H t‖ ≤ sH) (hQ : ∀ t ∈ Icc 0 T, ‖Q t‖ ≤ sQ)
    (hA : ∀ u ∈ Icc 0 T, ‖A u‖ ≤ L1)
    (hEq : ∀ t ∈ Icc 0 T, Ef t = H t + (∫ u in (0 : ℝ)..t, A u (Ef u)) + Q t) :
    ∀ t ∈ Icc 0 T, ‖Ef t‖ ≤ (sH + sQ) * Real.exp (L1 * T) := by
  intro t ht
  have h := gronwall_norm_le (T := T) (L := L1) (s := sH + sQ) hT hL1 (by positivity)
    (D := Ef) (M := fun t => H t + Q t) (Fd := fun u => A u (Ef u)) hE hAE
    (fun t ht => (norm_add_le _ _).trans (add_le_add (hH t ht) (hQ t ht)))
    (fun t ht => by rw [hEq t ht]; beta_reduce; abel)
    (fun u hu => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hA u hu) (norm_nonneg _))) t ht
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hL1))
    (by positivity)

end Gronwall

/-! ### Gronwall for rational suprema -/

section PathSup

variable {Ω : Type*} {d : ℕ}

theorem pathSupIcc_le_of_bound {T c : ℝ} (hc : 0 ≤ c) {Y : ℝ → Ω → (Fin d → ℝ)} {ω : Ω}
    (h : ∀ t ∈ Icc (0 : ℝ) T, ‖Y t ω‖ ≤ c) : pathSupIcc T Y ω ≤ c := by
  unfold pathSupIcc
  have : (⨆ q : RatIcc T, ENNReal.ofReal ‖Y (q : ℝ) ω‖) ≤ ENNReal.ofReal c :=
    iSup_le fun q => ENNReal.ofReal_le_ofReal (h _ ⟨q.2.1, q.2.2⟩)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top this).trans_eq (ENNReal.toReal_ofReal hc)

/-- (U1): the supremum of `D` is at most `e^{L T}` times the supremum of `M`. -/
theorem pathSupIcc_le_gronwall {T L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {D M Fd : ℝ → Ω → (Fin d → ℝ)} {ω : Ω}
    (hD : Continuous fun t => D t ω) (hM : ContinuousOn (fun t => M t ω) (Icc 0 T))
    (hFd : ContinuousOn (fun t => Fd t ω) (Icc 0 T))
    (hEq : ∀ t ∈ Icc (0 : ℝ) T, D t ω = M t ω + ∫ u in (0 : ℝ)..t, Fd u ω)
    (hF : ∀ u ∈ Icc (0 : ℝ) T, ‖Fd u ω‖ ≤ L * ‖D u ω‖) :
    pathSupIcc T D ω ≤ Real.exp (L * T) * pathSupIcc T M ω := by
  have hs := pathSupIcc_nonneg T M ω
  have h := gronwall_norm_le hT hL hs (D := fun t => D t ω) (M := fun t => M t ω)
    (Fd := fun t => Fd t ω) hD hFd (fun t ht => norm_le_pathSupIcc hT M ω hM ht) hEq hF
  refine pathSupIcc_le_of_bound (by positivity) fun t ht => ?_
  calc ‖D t ω‖ ≤ pathSupIcc T M ω * Real.exp (L * t) := h t ht
    _ ≤ pathSupIcc T M ω * Real.exp (L * T) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hL)) hs
    _ = Real.exp (L * T) * pathSupIcc T M ω := mul_comm _ _

/-- (R3): `E = H + ∫ A E + Q` with `‖A‖ ≤ L1` gives
`sup ‖E‖ ≤ e^{L1 T} (sup ‖H‖ + sup ‖Q‖)`. -/
theorem pathSupIcc_le_linear_volterra {T L1 : ℝ} (hT : 0 ≤ T) (hL1 : 0 ≤ L1)
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {Ef H Q : ℝ → Ω → (Fin d → ℝ)} {ω : Ω}
    (hE : Continuous fun t => Ef t ω)
    (hAE : ContinuousOn (fun u => A u (Ef u ω)) (Icc 0 T))
    (hH : ContinuousOn (fun t => H t ω) (Icc 0 T))
    (hQ : ContinuousOn (fun t => Q t ω) (Icc 0 T))
    (hA : ∀ u ∈ Icc (0 : ℝ) T, ‖A u‖ ≤ L1)
    (hEq : ∀ t ∈ Icc (0 : ℝ) T,
      Ef t ω = H t ω + (∫ u in (0 : ℝ)..t, A u (Ef u ω)) + Q t ω) :
    pathSupIcc T Ef ω ≤ Real.exp (L1 * T) * (pathSupIcc T H ω + pathSupIcc T Q ω) := by
  have h := linear_volterra_norm_le hT hL1 (pathSupIcc_nonneg T H ω) (pathSupIcc_nonneg T Q ω)
    (A := A) (Ef := fun t => Ef t ω) (H := fun t => H t ω) (Q := fun t => Q t ω) hE hAE
    (fun t ht => norm_le_pathSupIcc hT H ω hH ht) (fun t ht => norm_le_pathSupIcc hT Q ω hQ ht)
    hA hEq
  refine pathSupIcc_le_of_bound (by have := pathSupIcc_nonneg T H ω
                                    have := pathSupIcc_nonneg T Q ω
                                    positivity) fun t ht => ?_
  calc ‖Ef t ω‖ ≤ (pathSupIcc T H ω + pathSupIcc T Q ω) * Real.exp (L1 * T) := h t ht
    _ = _ := mul_comm _ _

end PathSup

/-! ## Taylor remainder -/

section Taylor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Second-order Taylor remainder for a map with Lipschitz derivative (R2, pointwise form). -/
theorem taylor_remainder_le {f : E → F} {f' : E → E →L[ℝ] F} {L2 : ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hL : ∀ x y, ‖f' y - f' x‖ ≤ L2 * ‖y - x‖) (x y : E) :
    ‖f y - f x - f' x (y - x)‖ ≤ L2 / 2 * ‖y - x‖ ^ 2 := by
  set h : E := y - x with hh
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (x + s • h))
      (f' (x + s • h) h) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add x
    exact (hf (x + s • h)).comp_hasDerivAt s h1
  set g : ℝ → F := fun s => f (x + s • h) - f x - s • f' x h with hg
  have hgd : ∀ s : ℝ, HasDerivAt g (f' (x + s • h) h - f' x h) s := by
    intro s
    have h2 : HasDerivAt (fun s : ℝ => s • f' x h) (f' x h) s := by
      simpa using (hasDerivAt_id s).smul_const (f' x h)
    exact ((hderiv s).sub_const (f x)).sub h2
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖f' (x + s • h) h - f' x h‖ ≤ L2 * ‖h‖ ^ 2 * s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    calc ‖f' (x + s • h) h - f' x h‖ = ‖(f' (x + s • h) - f' x) h‖ := by
          rw [ContinuousLinearMap.sub_apply]
      _ ≤ ‖f' (x + s • h) - f' x‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L2 * ‖(x + s • h) - x‖ * ‖h‖ :=
          mul_le_mul_of_nonneg_right (hL x (x + s • h)) (norm_nonneg _)
      _ = L2 * ‖h‖ ^ 2 * s := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0]; ring
  have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => L2 * ‖h‖ ^ 2 * s ^ 2 / 2) (L2 * ‖h‖ ^ 2 * s) s := by
    intro s
    have := ((hasDerivAt_pow 2 s).const_mul (L2 * ‖h‖ ^ 2)).div_const 2
    convert this using 1
    simp; ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := g) (a := 0) (b := 1) (f' := fun s => f' (x + s • h) h - f' x h)
    (fun s _ => (hgd s).continuousAt.continuousWithinAt)
    (fun s _ => (hgd s).hasDerivWithinAt) (B := fun s : ℝ => L2 * ‖h‖ ^ 2 * s ^ 2 / 2)
    (B' := fun s => L2 * ‖h‖ ^ 2 * s)
    (by simp [hg]) hB hbound (x := 1) ⟨zero_le_one, le_rfl⟩
  have key' : ‖f y - f x - f' x (y - x)‖ ≤ L2 * ‖y - x‖ ^ 2 / 2 := by simpa [hg, hh] using key
  linarith

/-- Scaled form: for `D = √N • (z - x)`, `‖N • (f z - f x - f' x (z - x))‖ ≤ (L2/2) ‖D‖²`. -/
theorem scaled_taylor_remainder_le {f : E → F} {f' : E → E →L[ℝ] F} {L2 : ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hL : ∀ x y, ‖f' y - f' x‖ ≤ L2 * ‖y - x‖) {N : ℝ} (hN : 0 ≤ N) (x z : E) :
    ‖N • (f z - f x - f' x (z - x))‖ ≤ L2 / 2 * ‖Real.sqrt N • (z - x)‖ ^ 2 := by
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hN, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt hN]
  calc N * ‖f z - f x - f' x (z - x)‖ ≤ N * (L2 / 2 * ‖z - x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (taylor_remainder_le hf hL x z) hN
    _ = L2 / 2 * (N * ‖z - x‖ ^ 2) := by ring

/-- (R2): a pointwise bound `‖q s‖ ≤ (L2/2) U²` on `[0, T]` gives
`‖∫₀ᵗ q‖ ≤ (L2 T / 2) U²`. -/
theorem taylor_forcing_bound {q : ℝ → F} {T L2 U : ℝ} (hL2 : 0 ≤ L2)
    (hq : ∀ s ∈ Icc (0 : ℝ) T, ‖q s‖ ≤ L2 / 2 * U ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖∫ s in (0 : ℝ)..t, q s‖ ≤ L2 * T / 2 * U ^ 2 := by
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := q) (C := L2 / 2 * U ^ 2) (fun s hs => by
      rw [uIoc_of_le ht0] at hs
      exact hq s ⟨hs.1.le, hs.2.trans ht.2⟩)
  rw [sub_zero, abs_of_nonneg ht0] at h
  calc ‖∫ s in (0 : ℝ)..t, q s‖ ≤ L2 / 2 * U ^ 2 * t := h
    _ ≤ L2 / 2 * U ^ 2 * T :=
        mul_le_mul_of_nonneg_left ht.2 (by positivity)
    _ = L2 * T / 2 * U ^ 2 := by ring

end Taylor

/-! ## Tail combination -/

section Tails

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- `a_U = 2 max(1, d)`. -/
def sectionFourAU (d : ℕ) : ℝ := 2 * max (1 : ℝ) d

/-- `b_U = 1 / (2 G² Q₀)`. -/
def sectionFourBU (G Q0 : ℝ) : ℝ := 1 / (2 * G ^ 2 * Q0)

/-- `a_R = 4 max(1, d)`. -/
def sectionFourAR (d : ℕ) : ℝ := 4 * max (1 : ℝ) d

/-- `c_R = min {1 / (4 G³ Q₀ A), A / (4 G Q₁)}`. -/
def sectionFourCR (G Q0 Q1 A : ℝ) : ℝ := min (1 / (4 * G ^ 3 * Q0 * A)) (A / (4 * G * Q1))

omit [IsProbabilityMeasure P] in
/-- Union bound over the coordinates and the two signs. -/
theorem measure_le_of_coordinate_cover (W : Set Ω) (Ep Em : Fin d → Set Ω)
    (hW : ∀ᵐ ω ∂P, ω ∈ W → ∃ i, ω ∈ Ep i ∨ ω ∈ Em i) {e : ℝ≥0∞}
    (hp : ∀ i, P (W ∩ Ep i) ≤ e) (hm : ∀ i, P (W ∩ Em i) ≤ e) :
    P W ≤ 2 * d * e := by
  have hsub : W ≤ᵐ[P] ⋃ i, ((W ∩ Ep i) ∪ (W ∩ Em i)) := by
    filter_upwards [hW] with ω h hω
    obtain ⟨i, hi⟩ := h hω
    refine mem_iUnion.2 ⟨i, ?_⟩
    rcases hi with hi | hi
    · exact Or.inl ⟨hω, hi⟩
    · exact Or.inr ⟨hω, hi⟩
  calc P W ≤ P (⋃ i, ((W ∩ Ep i) ∪ (W ∩ Em i))) := measure_mono_ae hsub
    _ ≤ ∑ i, P ((W ∩ Ep i) ∪ (W ∩ Em i)) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : Fin d, (e + e) := Finset.sum_le_sum fun i _ =>
        (measure_union_le _ _).trans (add_le_add (hp i) (hm i))
    _ = 2 * d * e := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem two_mul_card_mul_ofReal_le (d : ℕ) (x : ℝ) :
    2 * (d : ℝ≥0∞) * ENNReal.ofReal x ≤ ENNReal.ofReal (2 * max (1 : ℝ) d * x) := by
  have h1 : (d : ℝ≥0∞) ≤ ENNReal.ofReal (max (1 : ℝ) d) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have h0 : 0 ≤ max (1 : ℝ) d := le_trans zero_le_one (le_max_left _ _)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have : ENNReal.ofReal 2 = 2 := by simp
  rw [this]
  gcongr

omit [IsProbabilityMeasure P] in
/-- (U3). Producers of the hypotheses:
* `hU` is `U ≤ G sup_t ‖M⁰‖_∞` (U1, `pathSupIcc_le_gronwall`) with `Sp i = sup_t M⁰_i`,
  `Sm i = sup_t (-M⁰_i)`;
* `hmaxp`, `hmaxm` are the one-sided exponential maximal inequality for the continuous local
  martingale `M⁰_i` and its negative (component 3), with `br i` its bracket;
* `hbr` is the bracket bound (U2): `br i ≤ Q₀` almost surely (component 3 bracket algebra with
  `0 ≤ f_l ≤ ε_l`, component 4 for the SDE). -/
theorem sectionFour_U_tail {U : Ω → ℝ} {Sp Sm br : Fin d → Ω → ℝ} {G Q0 : ℝ}
    (hG : 0 < G) (hQ0 : 0 < Q0)
    (hU : ∀ᵐ ω ∂P, ∀ c : ℝ, 0 ≤ c → (∀ i, Sp i ω ≤ c ∧ Sm i ω ≤ c) → U ω ≤ G * c)
    (hbr : ∀ i, ∀ᵐ ω ∂P, br i ω ≤ Q0)
    (hmaxp : ∀ (i : Fin d) (s q : ℝ), 0 ≤ s → 0 < q →
      P ({ω | s ≤ Sp i ω} ∩ {ω | br i ω ≤ q}) ≤ ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * q))))
    (hmaxm : ∀ (i : Fin d) (s q : ℝ), 0 ≤ s → 0 < q →
      P ({ω | s ≤ Sm i ω} ∩ {ω | br i ω ≤ q}) ≤ ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * q))))
    {r : ℝ} (hr : 0 ≤ r) :
    P {ω | r < U ω} ≤
      ENNReal.ofReal (sectionFourAU d * Real.exp (-sectionFourBU G Q0 * r ^ 2)) := by
  set c : ℝ := r / G with hc
  have hc0 : 0 ≤ c := by positivity
  have hexp : -(c ^ 2) / (2 * Q0) = -sectionFourBU G Q0 * r ^ 2 := by
    simp only [hc, sectionFourBU]; field_simp
  have hW : ∀ᵐ ω ∂P, ω ∈ {ω | r < U ω} →
      ∃ i, ω ∈ {ω | c ≤ Sp i ω} ∨ ω ∈ {ω | c ≤ Sm i ω} := by
    filter_upwards [hU] with ω h hω
    by_contra hne
    push Not at hne
    have := h c hc0 (fun i => ⟨le_of_lt (hne i).1, le_of_lt (hne i).2⟩)
    have hGc : G * c = r := by simp only [hc]; field_simp
    have hω' : r < U ω := hω
    linarith
  have hp : ∀ i, P ({ω | r < U ω} ∩ {ω | c ≤ Sp i ω}) ≤
      ENNReal.ofReal (Real.exp (-sectionFourBU G Q0 * r ^ 2)) := by
    intro i
    refine le_trans ?_ (hexp ▸ hmaxp i c Q0 hc0 hQ0)
    refine measure_mono_ae ?_
    filter_upwards [hbr i] with ω h hω
    exact ⟨hω.2, h⟩
  have hm : ∀ i, P ({ω | r < U ω} ∩ {ω | c ≤ Sm i ω}) ≤
      ENNReal.ofReal (Real.exp (-sectionFourBU G Q0 * r ^ 2)) := by
    intro i
    refine le_trans ?_ (hexp ▸ hmaxm i c Q0 hc0 hQ0)
    refine measure_mono_ae ?_
    filter_upwards [hbr i] with ω h hω
    exact ⟨hω.2, h⟩
  refine (measure_le_of_coordinate_cover _ _ _ hW hp hm).trans ?_
  exact two_mul_card_mul_ofReal_le d _

/-- (R5). Producers of the hypotheses:
* `hUtail` is the conclusion of `sectionFour_U_tail` (U3);
* `hRU` is `R ≤ G (sup ‖H‖ + B U²)`: (R3) `pathSupIcc_le_linear_volterra` with the Taylor
  forcing bound (R2) `taylor_forcing_bound`, with `Hsup` the supremum of `‖H‖` (component 0 `V`
  equation and component 4 SDE give (R1));
* `hHsup` is `sup ‖H‖ ≤ c` whenever all `sup ±H_i ≤ c`, and `hmaxHp`, `hmaxHm` are the
  one-sided exponential maximal inequality for the continuous local martingales `H_i`,
  `-H_i` with brackets `brH i` (component 3);
* `hbrH` is the bracket bound (R4) `brH i ≤ c1 U²`, with `c1 = M T` (component 3 bracket algebra
  and the Lipschitz hypothesis on `g_l`). -/
theorem sectionFour_R_tail {U R Hsup : Ω → ℝ} {Tp Tm brH : Fin d → Ω → ℝ}
    {G Q0 Q1 B c1 : ℝ} (hG : 0 < G) (hQ0 : 0 < Q0) (hQ1 : 0 < Q1) (hB : 0 ≤ B)
    (hc1 : c1 ≤ Q1)
    (hU0 : ∀ᵐ ω ∂P, 0 ≤ U ω)
    (hUtail : ∀ r : ℝ, 0 ≤ r → P {ω | r < U ω} ≤
      ENNReal.ofReal (sectionFourAU d * Real.exp (-sectionFourBU G Q0 * r ^ 2)))
    (hRU : ∀ᵐ ω ∂P, R ω ≤ G * (Hsup ω + B * U ω ^ 2))
    (hHsup : ∀ᵐ ω ∂P, ∀ c : ℝ, 0 ≤ c → (∀ i, Tp i ω ≤ c ∧ Tm i ω ≤ c) → Hsup ω ≤ c)
    (hbrH : ∀ i, ∀ᵐ ω ∂P, brH i ω ≤ c1 * U ω ^ 2)
    (hmaxHp : ∀ (i : Fin d) (s q : ℝ), 0 ≤ s → 0 < q →
      P ({ω | s ≤ Tp i ω} ∩ {ω | brH i ω ≤ q}) ≤
        ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * q))))
    (hmaxHm : ∀ (i : Fin d) (s q : ℝ), 0 ≤ s → 0 < q →
      P ({ω | s ≤ Tm i ω} ∩ {ω | brH i ω ≤ q}) ≤
        ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * q))))
    {r : ℝ} (hr : 0 ≤ r) :
    P {ω | r < R ω} ≤
      ENNReal.ofReal (sectionFourAR d *
        Real.exp (-sectionFourCR G Q0 Q1 (1 + B) * r)) := by
  set A : ℝ := 1 + B with hA
  have hApos : 0 < A := by rw [hA]; linarith
  set κ : ℝ := sectionFourCR G Q0 Q1 A with hκ
  have hκ1 : κ ≤ 1 / (4 * G ^ 3 * Q0 * A) := min_le_left _ _
  have hκ2 : κ ≤ A / (4 * G * Q1) := min_le_right _ _
  have hκ0 : 0 < κ := lt_min (by positivity) (by positivity)
  rcases hr.eq_or_lt with hr0 | hrpos
  · -- r = 0
    subst hr0
    calc P {ω | (0 : ℝ) < R ω} ≤ 1 := prob_le_one
      _ ≤ _ := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        simp only [mul_zero, Real.exp_zero, mul_one, sectionFourAR]
        have : (1 : ℝ) ≤ max 1 (d : ℝ) := le_max_left _ _
        linarith
  set u : ℝ := r / (2 * G * A) with hu
  have hupos : 0 < u := by positivity
  set c : ℝ := r / (2 * G) with hc
  have hc0 : 0 ≤ c := by positivity
  -- split
  have hsplit : {ω | r < R ω} ⊆
      ({ω | r < R ω} ∩ {ω | U ω ^ 2 ≤ u}) ∪ {ω | u < U ω ^ 2} := by
    intro ω hω
    by_cases h : U ω ^ 2 ≤ u
    · exact Or.inl ⟨hω, h⟩
    · exact Or.inr (not_le.1 h)
  -- the large-U part
  have hW2 : P {ω | u < U ω ^ 2} ≤
      ENNReal.ofReal (sectionFourAU d * Real.exp (-sectionFourBU G Q0 * u)) := by
    have hsq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hupos.le
    have := hUtail (Real.sqrt u) (Real.sqrt_nonneg _)
    rw [hsq] at this
    refine le_trans (measure_mono_ae ?_) this
    filter_upwards [hU0] with ω h0 hω
    have hω' : u < U ω ^ 2 := hω
    show Real.sqrt u < U ω
    calc Real.sqrt u < Real.sqrt (U ω ^ 2) := Real.sqrt_lt_sqrt hupos.le hω'
      _ = U ω := Real.sqrt_sq h0
  -- the small-U part
  set q : ℝ := Q1 * u with hq
  have hqpos : 0 < q := by positivity
  have hexp : -(c ^ 2) / (2 * q) = -(A / (4 * G * Q1)) * r := by
    simp only [hc, hq, hu]; field_simp; norm_num
  have hW : ∀ᵐ ω ∂P, ω ∈ ({ω | r < R ω} ∩ {ω | U ω ^ 2 ≤ u}) →
      ∃ i, ω ∈ {ω | c ≤ Tp i ω} ∨ ω ∈ {ω | c ≤ Tm i ω} := by
    filter_upwards [hRU, hHsup] with ω h1 h2 hω
    by_contra hne
    push Not at hne
    have hH := h2 c hc0 (fun i => ⟨le_of_lt (hne i).1, le_of_lt (hne i).2⟩)
    have hRr : r < R ω := hω.1
    have hUu : U ω ^ 2 ≤ u := hω.2
    have hGc : G * c = r / 2 := by simp only [hc]; field_simp
    have hGBu : G * (B * u) ≤ r / 2 := by
      have : G * (B * u) = B / A * (r / 2) := by simp only [hu]; field_simp
      rw [this]
      have hBA : B / A ≤ 1 := by
        rw [div_le_one hApos, hA]; linarith
      have : B / A * (r / 2) ≤ 1 * (r / 2) :=
        mul_le_mul_of_nonneg_right hBA (by positivity)
      linarith
    have : R ω ≤ G * c + G * (B * u) := by
      calc R ω ≤ G * (Hsup ω + B * U ω ^ 2) := h1
        _ ≤ G * (c + B * u) := by
            apply mul_le_mul_of_nonneg_left _ hG.le
            have := mul_le_mul_of_nonneg_left hUu hB
            linarith
        _ = G * c + G * (B * u) := by ring
    linarith
  have hpart : ∀ (S : Fin d → Ω → ℝ),
      (∀ (i : Fin d) (s q : ℝ), 0 ≤ s → 0 < q →
        P ({ω | s ≤ S i ω} ∩ {ω | brH i ω ≤ q}) ≤
          ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * q)))) →
      ∀ i, P (({ω | r < R ω} ∩ {ω | U ω ^ 2 ≤ u}) ∩ {ω | c ≤ S i ω}) ≤
        ENNReal.ofReal (Real.exp (-(A / (4 * G * Q1)) * r)) := by
    intro S hmax i
    refine le_trans ?_ (hexp ▸ hmax i c q hc0 hqpos)
    refine measure_mono_ae ?_
    filter_upwards [hbrH i] with ω h hω
    refine ⟨hω.2, ?_⟩
    have hUu : U ω ^ 2 ≤ u := hω.1.2
    show brH i ω ≤ q
    calc brH i ω ≤ c1 * U ω ^ 2 := h
      _ ≤ Q1 * U ω ^ 2 := mul_le_mul_of_nonneg_right hc1 (sq_nonneg _)
      _ ≤ Q1 * u := mul_le_mul_of_nonneg_left hUu hQ1.le
  have hW1 : P ({ω | r < R ω} ∩ {ω | U ω ^ 2 ≤ u}) ≤
      ENNReal.ofReal (sectionFourAU d * Real.exp (-(A / (4 * G * Q1)) * r)) :=
    (measure_le_of_coordinate_cover _ _ _ hW (hpart Tp hmaxHp) (hpart Tm hmaxHm)).trans
      (two_mul_card_mul_ofReal_le d _)
  -- combine
  have hD : 0 ≤ max (1 : ℝ) d := le_trans zero_le_one (le_max_left _ _)
  have e1 : Real.exp (-sectionFourBU G Q0 * u) ≤ Real.exp (-κ * r) := by
    apply Real.exp_le_exp.2
    have : sectionFourBU G Q0 * u = 1 / (4 * G ^ 3 * Q0 * A) * r := by
      simp only [sectionFourBU, hu]; field_simp; ring
    have h2 : κ * r ≤ 1 / (4 * G ^ 3 * Q0 * A) * r := mul_le_mul_of_nonneg_right hκ1 hr
    nlinarith
  have e2 : Real.exp (-(A / (4 * G * Q1)) * r) ≤ Real.exp (-κ * r) := by
    apply Real.exp_le_exp.2
    have h2 : κ * r ≤ A / (4 * G * Q1) * r := mul_le_mul_of_nonneg_right hκ2 hr
    nlinarith
  calc P {ω | r < R ω}
      ≤ P (({ω | r < R ω} ∩ {ω | U ω ^ 2 ≤ u}) ∪ {ω | u < U ω ^ 2}) := measure_mono hsplit
    _ ≤ P ({ω | r < R ω} ∩ {ω | U ω ^ 2 ≤ u}) + P {ω | u < U ω ^ 2} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (sectionFourAU d * Real.exp (-(A / (4 * G * Q1)) * r)) +
          ENNReal.ofReal (sectionFourAU d * Real.exp (-sectionFourBU G Q0 * u)) :=
        add_le_add hW1 hW2
    _ ≤ ENNReal.ofReal (sectionFourAU d * Real.exp (-κ * r)) +
          ENNReal.ofReal (sectionFourAU d * Real.exp (-κ * r)) := by
        have hAU : 0 ≤ sectionFourAU d := by unfold sectionFourAU; positivity
        exact add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left e2 hAU))
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left e1 hAU))
    _ = ENNReal.ofReal (sectionFourAR d * Real.exp (-κ * r)) := by
        have hAU : 0 ≤ sectionFourAU d * Real.exp (-κ * r) := by
          unfold sectionFourAU; positivity
        rw [← ENNReal.ofReal_add hAU hAU]
        congr 1
        unfold sectionFourAU sectionFourAR
        ring

/-- (R6): the exponential moment of `R` at order `c_R / 2`, with constant `1 + a_R`. -/
theorem sectionFour_R_expMoment {R : Ω → ℝ} (hR : Measurable R) (hR0 : ∀ ω, 0 ≤ R ω)
    {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 ≤ a)
    (htail : ∀ r : ℝ, 0 ≤ r → P {ω | r < R ω} ≤ ENNReal.ofReal (a * Real.exp (-c * r))) :
    Integrable (fun ω => Real.exp (c / 2 * R ω)) P ∧
      ∫ ω, Real.exp (c / 2 * R ω) ∂P ≤ 1 + a := by
  obtain ⟨h1, h2⟩ := integrable_exp_mul_of_exp_tail hR hR0 ha htail (η := c / 2)
    (by positivity) (by linarith)
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  unfold expTailMomentConst
  field_simp
  ring

/-- Uniform-in-`N` form of (R6), in the shape consumed by `sectionFour_final_assembly`. -/
theorem uniformExpMoment_of_exp_tail {R : ℕ → Ω → ℝ}
    (hR : ∀ N, 2 ≤ N → Measurable (R N)) (hR0 : ∀ N, 2 ≤ N → ∀ ω, 0 ≤ R N ω)
    {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a)
    (htail : ∀ N, 2 ≤ N → ∀ r : ℝ, 0 ≤ r →
      P {ω | r < R N ω} ≤ ENNReal.ofReal (a * Real.exp (-c * r))) :
    UniformExpMoment R (c / 2) (1 + a) P where
  eta_pos := by positivity
  measurable := hR
  nonneg := hR0
  integrable N hN := (sectionFour_R_expMoment (hR N hN) (hR0 N hN) hc ha (htail N hN)).1
  integral_le N hN := (sectionFour_R_expMoment (hR N hN) (hR0 N hN) hc ha (htail N hN)).2

end Tails

end Ripple.Kurtz.StrongApprox.SectionFourAssembly

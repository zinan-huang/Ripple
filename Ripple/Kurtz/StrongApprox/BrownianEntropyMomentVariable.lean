-- Ripple/Kurtz/StrongApprox/BrownianEntropyMomentVariable.lean
import Ripple.Kurtz.StrongApprox.BrownianEntropyModulus

/-!
# The entropy modulus as a random variable, and its exponential moment

For a path family `W` with the `DyadicBrownianOn` interface, the dyadic cell
control of `BrownianEntropyModulus` holds at level `a` outside the measurable
set `brownianDyadicFailure W H a`.  The random variable
`brownianEntropyLevel W H` is the least rational level at which it holds.

* it is measurable (the failure sets are measurable because every
  `W t` is measurable);
* if the level is below `a`, the entropy modulus bound holds with tail
  parameter `max a 2` (this is `a` when `a ≥ 2`; the chaining lemma needs
  `2 ≤ a`), for every continuous path;
* `P(a < level) ≤ exp (-a)` for `a ≥ 0` and every horizon `H > 0`;
* `E exp (λ · level) ≤ 1 / (1 - λ)` for `0 < λ < 1`, uniformly in `H > 0`.

The literal all-pairs failure set `brownianEntropyFailure` is not shown
measurable; its monotonicity in the tail parameter is proved here, but the
random variable is defined through the dyadic certificate, whose failure set is
measurable.  Premises are those of `law_brownianEntropyFailure_le`:
`DyadicBrownianOn P W H` (produced by `brownianPath_dyadicBrownianOn` and
`arbitraryHorizonBrownian_dyadicBrownianOn`).
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Monotonicity in the tail parameter -/

theorem brownianEntropyBound_mono_param
    {H a b h : ℝ} (hh : 0 ≤ h) (hab : a ≤ b) :
    brownianEntropyBound H a h ≤ brownianEntropyBound H b h := by
  unfold brownianEntropyBound brownianEntropyCore brownianEntropyConstant
  split_ifs with h0
  · linarith
  · have hs : Real.sqrt (h * (Real.log (H / h) + a)) ≤
        Real.sqrt (h * (Real.log (H / h) + b)) :=
      Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left (by linarith) hh)
    linarith

theorem brownianEntropyFailure_antitone
    (W : ℝ → Ω → ℝ) (H : ℝ) {a b : ℝ} (hab : a ≤ b) :
    brownianEntropyFailure W H b ⊆ brownianEntropyFailure W H a := by
  rintro omega ⟨u, hu, v, hv, hlt⟩
  exact ⟨u, hu, v, hv,
    lt_of_le_of_lt
      (brownianEntropyBound_mono_param (abs_nonneg _) hab) hlt⟩

theorem brownianDyadicThreshold_mono
    {H a b : ℝ} (hH : 0 ≤ H) (m : ℕ) (hab : a ≤ b) :
    brownianDyadicThreshold H a m ≤ brownianDyadicThreshold H b m := by
  unfold brownianDyadicThreshold
  have hmesh : 0 ≤ brownianDyadicMesh H m := by
    unfold brownianDyadicMesh
    positivity
  have hs : Real.sqrt (brownianDyadicMesh H m * (a + m + 1)) ≤
      Real.sqrt (brownianDyadicMesh H m * (b + m + 1)) :=
    Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (by linarith) hmesh)
  linarith

theorem brownianDyadicFailure_antitone
    (W : ℝ → Ω → ℝ) {H a b : ℝ} (hH : 0 ≤ H) (hab : a ≤ b) :
    brownianDyadicFailure W H b ⊆ brownianDyadicFailure W H a := by
  intro omega hbad
  unfold brownianDyadicFailure at hbad ⊢
  rw [Set.mem_iUnion] at hbad ⊢
  obtain ⟨m, k, hk, hlt⟩ := hbad
  exact ⟨m, k, hk,
    lt_of_le_of_lt (brownianDyadicThreshold_mono hH m hab) hlt⟩

theorem measurableSet_brownianDyadicFailure
    {W : ℝ → Ω → ℝ} (hW : ∀ t, Measurable (W t)) (H a : ℝ) :
    MeasurableSet (brownianDyadicFailure W H a) := by
  unfold brownianDyadicFailure
  refine MeasurableSet.iUnion fun m => ?_
  have hset : brownianDyadicLevelFailure W H a m =
      ⋃ k : ℕ, ⋃ _ : k < 2 ^ m,
        {omega | brownianDyadicThreshold H a m <
          |W (brownianDyadicPoint H m (k + 1)) omega -
            W (brownianDyadicPoint H m k) omega|} := by
    ext omega
    simp [brownianDyadicLevelFailure]
  rw [hset]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_lt measurable_const (((hW _).sub (hW _)).abs)

/-! ## The level as a random variable -/

/-- The least rational level at which the dyadic cell control holds. -/
def brownianEntropyLevel (W : ℝ → Ω → ℝ) (H : ℝ) (omega : Ω) : ℝ≥0∞ :=
  ⨅ q : ℚ, ⨅ (_ : 0 ≤ q ∧ omega ∉ brownianDyadicFailure W H (q : ℝ)),
    ENNReal.ofReal (q : ℝ)

theorem brownianEntropyLevel_le_of_not_mem
    {W : ℝ → Ω → ℝ} {H : ℝ} {omega : Ω} (q : ℚ) (hq : 0 ≤ q)
    (hnot : omega ∉ brownianDyadicFailure W H (q : ℝ)) :
    brownianEntropyLevel W H omega ≤ ENNReal.ofReal (q : ℝ) :=
  iInf_le_of_le q (iInf_le _ ⟨hq, hnot⟩)

theorem measurable_brownianEntropyLevel
    {W : ℝ → Ω → ℝ} (hW : ∀ t, Measurable (W t)) (H : ℝ) :
    Measurable (brownianEntropyLevel W H) := by
  classical
  refine Measurable.iInf fun q => ?_
  have hS : MeasurableSet
      {omega : Ω | 0 ≤ q ∧ omega ∉ brownianDyadicFailure W H (q : ℝ)} := by
    by_cases hq : 0 ≤ q
    · have hset : {omega : Ω | 0 ≤ q ∧
          omega ∉ brownianDyadicFailure W H (q : ℝ)} =
          (brownianDyadicFailure W H (q : ℝ))ᶜ := by
        ext omega
        simp [hq]
      rw [hset]
      exact (measurableSet_brownianDyadicFailure hW H (q : ℝ)).compl
    · have hset : {omega : Ω | 0 ≤ q ∧
          omega ∉ brownianDyadicFailure W H (q : ℝ)} = ∅ := by
        ext omega
        simp [hq]
      rw [hset]
      exact MeasurableSet.empty
  have h2 : Measurable (fun omega : Ω =>
      if omega ∈ {omega : Ω | 0 ≤ q ∧
          omega ∉ brownianDyadicFailure W H (q : ℝ)}
        then ENNReal.ofReal (q : ℝ) else (⊤ : ℝ≥0∞)) :=
    Measurable.ite hS measurable_const measurable_const
  convert h2 using 1
  funext omega
  by_cases h : 0 ≤ q ∧ omega ∉ brownianDyadicFailure W H (q : ℝ)
  · simp [h]
  · simp [h]

/-! ## Pathwise consequence -/

/-- Below level `a`, the entropy modulus holds with tail parameter `max a 2`
(that is `a` for `a ≥ 2`), for every continuous path. -/
theorem brownianEntropyLevel_pathwise
    {W : ℝ → Ω → ℝ} {H a : ℝ} {omega : Ω}
    (hH : 0 < H)
    (hcont : Continuous (fun t => W t omega))
    (hlev : brownianEntropyLevel W H omega < ENNReal.ofReal a) :
    ∀ u ∈ Icc (0 : ℝ) H, ∀ v ∈ Icc (0 : ℝ) H,
      |W u omega - W v omega| ≤
        brownianEntropyBound H (max a 2) |u - v| := by
  have hlev' : ∃ q : ℚ, ∃ _ : 0 ≤ q ∧
      omega ∉ brownianDyadicFailure W H (q : ℝ),
        ENNReal.ofReal (q : ℝ) < ENNReal.ofReal a := by
    unfold brownianEntropyLevel at hlev
    rw [iInf_lt_iff] at hlev
    obtain ⟨q, hq⟩ := hlev
    rw [iInf_lt_iff] at hq
    obtain ⟨hcond, hq2⟩ := hq
    exact ⟨q, hcond, hq2⟩
  obtain ⟨q, ⟨hq0, hqnot⟩, hqlt⟩ := hlev'
  have hqa : (q : ℝ) ≤ a := by
    by_contra hnot
    have hlt : a < (q : ℝ) := lt_of_not_ge hnot
    have : ENNReal.ofReal a ≤ ENNReal.ofReal (q : ℝ) :=
      ENNReal.ofReal_le_ofReal hlt.le
    exact absurd hqlt (not_lt.mpr this)
  have hqmax : (q : ℝ) ≤ max a 2 := hqa.trans (le_max_left _ _)
  have hgood : omega ∉ brownianDyadicFailure W H (max a 2) :=
    fun hbad => hqnot
      (brownianDyadicFailure_antitone W hH.le hqmax hbad)
  have hcell : BrownianDyadicCellControl (fun t => W t omega) H (max a 2) := by
    intro m k hk
    by_contra hfail
    apply hgood
    rw [brownianDyadicFailure, Set.mem_iUnion]
    exact ⟨m, k, hk, lt_of_not_ge hfail⟩
  exact brownianEntropyBound_of_dyadicCellControl hH (le_max_right _ _)
    hcont hcell

/-! ## Tail -/

theorem law_brownianEntropyLevel_gt
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ → Ω → ℝ} {H a : ℝ}
    (hH : 0 < H) (_ha : 0 ≤ a) (hW : DyadicBrownianOn P W H) :
    P {omega | ENNReal.ofReal a < brownianEntropyLevel W H omega} ≤
      ENNReal.ofReal (Real.exp (-a)) := by
  have key : ∀ ε : ℝ, ε ∈ Ioi (0 : ℝ) →
      P {omega | ENNReal.ofReal a < brownianEntropyLevel W H omega} ≤
        ENNReal.ofReal (Real.exp (ε - a)) := by
    intro ε hε
    have hε0 : 0 < ε := hε
    by_cases hεa : ε ≤ a
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show a - ε < a by linarith)
      have hq0r : (0 : ℝ) ≤ q := by linarith
      have hq0 : 0 ≤ q := by exact_mod_cast hq0r
      have hsub : {omega | ENNReal.ofReal a < brownianEntropyLevel W H omega} ⊆
          brownianDyadicFailure W H (q : ℝ) := by
        intro omega homega
        by_contra hnot
        have hle := brownianEntropyLevel_le_of_not_mem q hq0 hnot
        have : ENNReal.ofReal (q : ℝ) ≤ ENNReal.ofReal a :=
          ENNReal.ofReal_le_ofReal hq2.le
        exact absurd homega (not_lt.mpr (hle.trans this))
      calc
        P {omega | ENNReal.ofReal a < brownianEntropyLevel W H omega} ≤
            P (brownianDyadicFailure W H (q : ℝ)) := measure_mono hsub
        _ ≤ ENNReal.ofReal (Real.exp (-(q : ℝ))) :=
          law_brownianDyadicFailure_le hH hq0r hW
        _ ≤ ENNReal.ofReal (Real.exp (ε - a)) :=
          ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.mpr (by linarith))
    · calc
        P {omega | ENNReal.ofReal a < brownianEntropyLevel W H omega} ≤ 1 :=
          prob_le_one
        _ ≤ ENNReal.ofReal (Real.exp (ε - a)) := by
          rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          exact Real.one_le_exp (by linarith [not_le.mp hεa])
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp (ε - a)))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (Real.exp (-a)))) := by
    have hc : Continuous (fun ε : ℝ => Real.exp (ε - a)) :=
      Real.continuous_exp.comp (continuous_id.sub continuous_const)
    have h0 : Tendsto (fun ε : ℝ => Real.exp (ε - a)) (𝓝 (0 : ℝ))
        (𝓝 (Real.exp (-a))) := by
      simpa using hc.tendsto 0
    exact (ENNReal.tendsto_ofReal (h0.mono_left nhdsWithin_le_nhds))
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

/-- The tail in the constants of `law_brownianEntropyFailure_le`. -/
theorem law_brownianEntropyLevel_gt_entropy
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ → Ω → ℝ} {H a : ℝ}
    (hH : 1 ≤ H) (ha : 0 ≤ a) (hW : DyadicBrownianOn P W H) :
    P {omega | ENNReal.ofReal a < brownianEntropyLevel W H omega} ≤
      ENNReal.ofReal (brownianEntropyTailConstant * Real.exp (-a)) := by
  refine (law_brownianEntropyLevel_gt (lt_of_lt_of_le zero_lt_one hH) ha hW).trans ?_
  apply ENNReal.ofReal_le_ofReal
  unfold brownianEntropyTailConstant
  have h1 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  nlinarith [Real.exp_pos (-a)]

/-- The level is almost surely finite. -/
theorem brownianEntropyLevel_ae_ne_top
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ → Ω → ℝ} {H : ℝ}
    (hH : 0 < H) (hW : DyadicBrownianOn P W H) :
    ∀ᵐ omega ∂P, brownianEntropyLevel W H omega ≠ ⊤ := by
  have hzero : P {omega | brownianEntropyLevel W H omega = ⊤} = 0 := by
    have hle : ∀ n : ℕ, P {omega | brownianEntropyLevel W H omega = ⊤} ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
      intro n
      refine le_trans (measure_mono ?_)
        (law_brownianEntropyLevel_gt hH (Nat.cast_nonneg n) hW)
      intro omega homega
      have h : brownianEntropyLevel W H omega = ⊤ := homega
      show ENNReal.ofReal (n : ℝ) < brownianEntropyLevel W H omega
      rw [h]
      exact ENNReal.ofReal_lt_top
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(n : ℝ))))
        atTop (𝓝 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        tendsto_natCast_atTop_atTop
      simpa using ENNReal.tendsto_ofReal h
    exact le_antisymm (ge_of_tendsto' hlim hle) bot_le
  rw [ae_iff]
  simpa using hzero

/-! ## Exponential moment -/

theorem lintegral_exp_brownianEntropyLevel_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ → Ω → ℝ} {H lam : ℝ}
    (hH : 0 < H) (hW : DyadicBrownianOn P W H)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∫⁻ omega, ENNReal.ofReal
        (Real.exp (lam * (brownianEntropyLevel W H omega).toReal)) ∂P ≤
      ENNReal.ofReal (1 / (1 - lam)) := by
  set f : Ω → ℝ := fun omega => (brownianEntropyLevel W H omega).toReal with hf
  have hfm : Measurable f :=
    (measurable_brownianEntropyLevel hW.eval_measurable H).ennreal_toReal
  have hf0 : ∀ omega, 0 ≤ f omega := fun omega => ENNReal.toReal_nonneg
  set g : ℝ → ℝ := fun t => lam * Real.exp (lam * t) with hg
  have hgc : Continuous g := by
    simp only [hg]
    fun_prop
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul P
    (Filter.Eventually.of_forall hf0) hfm.aemeasurable
    (fun t _ => hgc.intervalIntegrable 0 t)
    (Filter.Eventually.of_forall fun t => by simp only [hg]; positivity)
  have hprim : ∀ s : ℝ, ∫ t in (0 : ℝ)..s, g t = Real.exp (lam * s) - 1 := by
    intro s
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) s,
        HasDerivAt (fun x => Real.exp (lam * x)) (g x) x := by
      intro x _
      have h1 : HasDerivAt (fun x : ℝ => lam * x) lam x := by
        simpa using (hasDerivAt_id x).const_mul lam
      have h2 := (Real.hasDerivAt_exp (lam * x)).comp x h1
      simpa [hg, mul_comm] using h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (hgc.intervalIntegrable 0 s)]
    simp
  have hlhs : ∀ omega, ENNReal.ofReal (∫ t in (0 : ℝ)..f omega, g t) =
      ENNReal.ofReal (Real.exp (lam * f omega) - 1) := by
    intro omega
    rw [hprim]
  -- tail bound on the layer-cake side
  have htail : ∀ t ∈ Ioi (0 : ℝ),
      P {omega | t < f omega} * ENNReal.ofReal (g t) ≤
        ENNReal.ofReal (lam * Real.exp (-(1 - lam) * t)) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hsub : {omega | t < f omega} ⊆
        {omega | ENNReal.ofReal t < brownianEntropyLevel W H omega} := by
      intro omega homega
      have h1 : t < (brownianEntropyLevel W H omega).toReal := homega
      have hne : brownianEntropyLevel W H omega ≠ ⊤ := by
        intro htop
        rw [htop] at h1
        simp at h1
        linarith
      show ENNReal.ofReal t < brownianEntropyLevel W H omega
      calc ENNReal.ofReal t < ENNReal.ofReal
            (brownianEntropyLevel W H omega).toReal :=
            (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr h1
        _ = brownianEntropyLevel W H omega := ENNReal.ofReal_toReal hne
    calc
      P {omega | t < f omega} * ENNReal.ofReal (g t) ≤
          ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (g t) :=
        mul_le_mul_right'
          ((measure_mono hsub).trans
            (law_brownianEntropyLevel_gt hH ht0.le hW)) _
      _ = ENNReal.ofReal (lam * Real.exp (-(1 - lam) * t)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        congr 1
        simp only [hg]
        rw [mul_comm (Real.exp (-t)) (lam * Real.exp (lam * t)),
          mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hdecay : (0 : ℝ) < 1 - lam := by linarith
  have hint : ∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (lam * Real.exp (-(1 - lam) * t)) =
        ENNReal.ofReal (lam / (1 - lam)) := by
    have hI : IntegrableOn (fun t : ℝ => lam * Real.exp (-(1 - lam) * t))
        (Ioi (0 : ℝ)) volume := by
      exact (integrableOn_exp_mul_Ioi (a := -(1 - lam))
        (by linarith) (0 : ℝ)).const_mul lam
    have hval : ∫ t in Ioi (0 : ℝ), lam * Real.exp (-(1 - lam) * t) =
        lam / (1 - lam) := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (a := -(1 - lam)) (by linarith) (0 : ℝ)]
      simp only [mul_zero, Real.exp_zero]
      field_simp
      try ring
    rw [← hval]
    symm
    exact ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun t => by positivity)
  have hmain :
      ∫⁻ omega, ENNReal.ofReal (Real.exp (lam * f omega) - 1) ∂P ≤
        ENNReal.ofReal (lam / (1 - lam)) := by
    calc
      ∫⁻ omega, ENNReal.ofReal (Real.exp (lam * f omega) - 1) ∂P =
          ∫⁻ omega, ENNReal.ofReal (∫ t in (0 : ℝ)..f omega, g t) ∂P := by
        congr 1
        funext omega
        exact (hlhs omega).symm
      _ = ∫⁻ t in Ioi (0 : ℝ), P {omega | t < f omega} *
          ENNReal.ofReal (g t) := hlayer
      _ ≤ ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (lam * Real.exp (-(1 - lam) * t)) :=
        setLIntegral_mono' measurableSet_Ioi htail
      _ = ENNReal.ofReal (lam / (1 - lam)) := hint
  have hsplit : ∀ omega, ENNReal.ofReal (Real.exp (lam * f omega)) =
      1 + ENNReal.ofReal (Real.exp (lam * f omega) - 1) := by
    intro omega
    have h1 : (1 : ℝ) ≤ Real.exp (lam * f omega) :=
      Real.one_le_exp (mul_nonneg hlam0.le (hf0 omega))
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by linarith)]
    congr 1
    ring
  calc
    ∫⁻ omega, ENNReal.ofReal (Real.exp (lam * f omega)) ∂P =
        ∫⁻ omega, (1 + ENNReal.ofReal (Real.exp (lam * f omega) - 1)) ∂P := by
      congr 1
      funext omega
      exact hsplit omega
    _ = 1 + ∫⁻ omega, ENNReal.ofReal (Real.exp (lam * f omega) - 1) ∂P := by
      have h := lintegral_add_left (μ := P)
        (measurable_const (a := (1 : ℝ≥0∞)))
        (fun omega => ENNReal.ofReal (Real.exp (lam * f omega) - 1))
      simpa using h
    _ ≤ 1 + ENNReal.ofReal (lam / (1 - lam)) := by gcongr
    _ = ENNReal.ofReal (1 / (1 - lam)) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by
        have : 0 ≤ lam / (1 - lam) := div_nonneg hlam0.le hdecay.le
        exact this)]
      congr 1
      field_simp
      ring


/-- Real-valued form of the exponential moment, uniform in `H > 0`. -/
theorem integral_exp_brownianEntropyLevel_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ → Ω → ℝ} {H lam : ℝ}
    (hH : 0 < H) (hW : DyadicBrownianOn P W H)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Integrable (fun omega =>
        Real.exp (lam * (brownianEntropyLevel W H omega).toReal)) P ∧
      ∫ omega, Real.exp
          (lam * (brownianEntropyLevel W H omega).toReal) ∂P ≤
        1 / (1 - lam) := by
  have hfm : Measurable (fun omega =>
      (brownianEntropyLevel W H omega).toReal) :=
    (measurable_brownianEntropyLevel hW.eval_measurable H).ennreal_toReal
  have hmeas : Measurable (fun omega =>
      Real.exp (lam * (brownianEntropyLevel W H omega).toReal)) :=
    Real.measurable_exp.comp (measurable_const.mul hfm)
  have hnn : 0 ≤ᵐ[P] (fun omega =>
      Real.exp (lam * (brownianEntropyLevel W H omega).toReal)) :=
    Filter.Eventually.of_forall fun omega => (Real.exp_pos _).le
  have hbound := lintegral_exp_brownianEntropyLevel_le hH hW hlam0 hlam1
  have hint : Integrable (fun omega =>
      Real.exp (lam * (brownianEntropyLevel W H omega).toReal)) P :=
    ⟨hmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).mpr
        (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal
    (div_nonneg zero_le_one (by linarith)) hbound

end Ripple.Kurtz.StrongApprox

end

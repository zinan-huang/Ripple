/-
  Ripple.Core.SurrogateCompilationBlowup — bounded surrogate compilation at a finite blow-up

  [BAC] Prop 3.2 for `T* < ∞` and [BAC] Thm 3.4 (poles of GPAC-implementable functions are
  computable), repaired as in `docs/refactor/BC.md` §1.3.3 and §1.5 (errata E3, E5): with the
  joint clock `P(y) = 1 + Σ yᵢ^N`, an unbounded solution on `[0, T)` forces
  `θ(t) = ∫₀ᵗ P(y) → ∞` as `t → T⁻` (`|yᵢ(t) − yᵢ(0)| ≤ C_F θ(t)`), so the inverse time change
  `s : [0, ∞) → [0, T)` exists and `s → T`.

  - `bounded_compilation_of_blowup`: the output keeps its limit at `T⁻` (kept output, as in
    `jointSurrogateCompile`; it is bounded because it converges).
  - `isCRNComputable_blowupTime` ([BAC] Thm 3.4): the compiled system **without** the kept output,
    state `(s, (W_a)_a)`, `s' = W₀`, output `s` (`jointClockCompile`; review P1: the output
    coordinate itself may blow up, e.g. `x' = 1 + x²`).

  The hypothesis "`y` is unbounded on `[0, T)`" is the faithful form of "`T` is the finite
  maximal existence time" for a polynomial field.

  Numbering of [BAC]: the DNA 32 version, as in `docs/refactor/BC.md` (journal-draft labels in
  the header of `Ripple.Core.SurrogateCompilation`).
-/

import Ripple.Core.Compilation

namespace Ripple

open MvPolynomial Filter MeasureTheory

variable {d : ℕ}

/-! ## The field is bounded by the clock -/

/-- `|Fᵢ(y)| ≤ C_F · P(y)` when `deg Fᵢ ≤ N` (BC.md §1.4.2). -/
theorem abs_eval₂_le_jointClock {N : ℕ} (hN : Even N) (q : MvPolynomial (Fin d) ℚ)
    (hq : q.totalDegree ≤ N) (y : Fin d → ℝ) :
    |q.eval₂ (Rat.castHom ℝ) y| ≤
      (∑ b : MIndex d N, |((q.coeff b.toFinsupp : ℚ) : ℝ)|) * jointClock N y := by
  rw [eval₂_as_mindex_sum q hq y, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul]
  by_cases hb : b.degree ≤ N
  · exact mul_le_mul_of_nonneg_left (abs_eval_le_jointClock hN b hb y) (abs_nonneg _)
  · rw [coeff_toFinsupp_eq_zero hq hb]; simp

/-! ## The inverse time change on `(-∞, T)` -/

/-- [BAC] Prop 3.2 (`T* < ∞`), BC.md §1.3.3: for `ρ ≥ 1` continuous on `(-∞, T)` whose clock
`θ(t) = ∫₀ᵗ ρ` is unbounded on `[0, T)`, the inverse time change `s : ℝ → (-∞, T)` exists,
with `s(0) = 0`, `s' = 1/ρ(s)`, `s` strictly increasing, and `s → T⁻`. -/
theorem exists_inverse_timeChange_Iio {ρ : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hρ : ContinuousOn ρ (Set.Iio T)) (h1 : ∀ u, 1 ≤ ρ u)
    (hunb : ¬ BddAbove (clockIntegral ρ '' Set.Ico 0 T)) :
    ∃ s : ℝ → ℝ, s 0 = 0 ∧ (∀ τ, s τ < T) ∧ (∀ τ, HasDerivAt s (ρ (s τ))⁻¹ τ) ∧
      Continuous s ∧ StrictMono s ∧ Tendsto s atTop (nhdsWithin T (Set.Iio T)) ∧
      (∀ t, t < T → s (clockIntegral ρ t) = t) := by
  classical
  have hpos : ∀ u, 0 < ρ u := fun u => lt_of_lt_of_le zero_lt_one (h1 u)
  have hopen : IsOpen (Set.Iio T) := isOpen_Iio
  have hint : ∀ a b, a < T → b < T → IntervalIntegrable ρ volume a b := fun a b ha hb =>
    (hρ.mono fun u hu => by
      rcases Set.mem_uIcc.mp hu with h | h
      · exact lt_of_le_of_lt h.2 hb
      · exact lt_of_le_of_lt h.2 ha).intervalIntegrable
  have hLd : ∀ x, x < T → HasDerivAt (clockIntegral ρ) (ρ x) x := fun x hx =>
    intervalIntegral.integral_hasDerivAt_right (hint 0 x hT hx)
      (hρ.stronglyMeasurableAtFilter hopen x hx) (hρ.continuousAt (hopen.mem_nhds hx))
  have hLmono : StrictMonoOn (clockIntegral ρ) (Set.Iio T) := by
    intro a ha b hb hab
    have hsplit : clockIntegral ρ b = clockIntegral ρ a + ∫ u in a..b, ρ u := by
      unfold clockIntegral
      exact (intervalIntegral.integral_add_adjacent_intervals (hint 0 a hT ha)
        (hint a b ha hb)).symm
    have hp : 0 < ∫ u in a..b, ρ u :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hint a b ha hb)
        (fun x _ => hpos x) hab
    linarith
  have hLcont : ContinuousOn (clockIntegral ρ) (Set.Iio T) := fun x hx =>
    (hLd x hx).continuousAt.continuousWithinAt
  have hL0 : clockIntegral ρ 0 = 0 := clockIntegral_zero ρ
  have hLle : ∀ t, t ≤ 0 → clockIntegral ρ t ≤ t := by
    intro t ht
    have hmono : (∫ _u in t..0, (1 : ℝ)) ≤ ∫ u in t..0, ρ u :=
      intervalIntegral.integral_mono_on ht
        ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).intervalIntegrable t 0)
        (hint t 0 (lt_of_le_of_lt ht hT) hT) (fun u _ => h1 u)
    have hsymm : clockIntegral ρ t = - ∫ u in t..0, ρ u := by
      unfold clockIntegral; rw [intervalIntegral.integral_symm]
    have hone : (∫ _u in t..0, (1 : ℝ)) = -t := by simp
    linarith
  -- the restriction to `(-∞, T)` is an order isomorphism onto `ℝ`
  let f : Set.Iio T → ℝ := fun t => clockIntegral ρ t
  have hfmono : StrictMono f := fun a b hab => hLmono a.2 b.2 hab
  have hfsurj : Function.Surjective f := by
    intro y
    by_cases hy : 0 ≤ y
    · obtain ⟨b, hb, hyb⟩ : ∃ b ∈ Set.Ico 0 T, y ≤ clockIntegral ρ b := by
        by_contra h
        push Not at h
        exact hunb ⟨y, by rintro _ ⟨b, hb, rfl⟩; exact (h b hb).le⟩
      obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hb.1
        (hLcont.mono fun u hu => lt_of_le_of_lt hu.2 hb.2) ⟨by rw [hL0]; exact hy, hyb⟩
      exact ⟨⟨x, lt_of_le_of_lt hx.2 hb.2⟩, hxy⟩
    · have hylt : y < 0 := lt_of_not_ge hy
      obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hylt.le
        (hLcont.mono fun u hu => lt_of_le_of_lt hu.2 hT)
        ⟨hLle y hylt.le, by rw [hL0]; exact hylt.le⟩
      exact ⟨⟨x, lt_of_le_of_lt hx.2 hT⟩, hxy⟩
  let e : Set.Iio T ≃o ℝ := StrictMono.orderIsoOfSurjective f hfmono hfsurj
  let s : ℝ → ℝ := fun τ => (e.symm τ : ℝ)
  have hs_inv : ∀ τ, clockIntegral ρ (s τ) = τ := fun τ => e.apply_symm_apply τ
  have hsT : ∀ τ, s τ < T := fun τ => (e.symm τ).2
  have hs_left : ∀ t, t < T → s (clockIntegral ρ t) = t := by
    intro t ht
    have : e ⟨t, ht⟩ = clockIntegral ρ t := rfl
    show ((e.symm (clockIntegral ρ t) : Set.Iio T) : ℝ) = t
    rw [← this, e.symm_apply_apply]
  have hs_cont : Continuous s := continuous_subtype_val.comp e.symm.continuous
  have hs_mono : StrictMono s := fun a b hab => e.symm.strictMono hab
  have hs0 : s 0 = 0 := by
    have := hs_left 0 hT; rwa [hL0] at this
  refine ⟨s, hs0, hsT, ?_, hs_cont, hs_mono, ?_, hs_left⟩
  · intro τ
    have hev : ∀ᶠ y in nhds τ, clockIntegral ρ (s y) = y := Filter.Eventually.of_forall hs_inv
    exact HasDerivAt.of_local_left_inverse hs_cont.continuousAt (hLd (s τ) (hsT τ))
      (ne_of_gt (hpos (s τ))) hev
  · rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall hsT⟩
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => Filter.Eventually.of_forall fun τ => (hsT τ).trans hb⟩
    filter_upwards [Filter.eventually_gt_atTop (clockIntegral ρ a)] with τ hτ
    have := hs_mono hτ
    rwa [hs_left a ha] at this

/-! ## Extension of a solution on `[0, T)` to `(-∞, T)` -/

/-- A solution on `[0, T)` re-chosen linearly for `t < 0`: continuous on `(-∞, T)`, unchanged
on `[0, T)`. -/
theorem exists_extension_Iio {F : (Fin d → ℝ) → Fin d → ℝ} {T : ℝ} (hT : 0 < T)
    (y : ℝ → Fin d → ℝ) (hy : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (F (y t)) t) :
    ∃ y' : ℝ → Fin d → ℝ, ContinuousOn y' (Set.Iio T) ∧ (∀ t, 0 ≤ t → y' t = y t) ∧
      ∀ t ∈ Set.Ico 0 T, HasDerivAt y' (F (y' t)) t := by
  let v := F (y 0)
  let z : ℝ → Fin d → ℝ := fun t => if 0 ≤ t then y t else y 0 + t • v
  have hz_pos : ∀ t, 0 ≤ t → z t = y t := fun t ht => if_pos ht
  have hz_neg : ∀ t, t ≤ 0 → z t = y 0 + t • v := by
    intro t ht
    by_cases h : 0 ≤ t
    · have h0 : t = 0 := le_antisymm ht h
      subst h0; simp [z]
    · simp [z, h]
  have hlin : ∀ s : ℝ, HasDerivAt (fun t : ℝ => y 0 + t • v) v s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const v).const_add (y 0)
  have hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt z (F (z t)) t := by
    intro t ht
    rcases ht.1.lt_or_eq with htpos | ht0
    · have hEv : z =ᶠ[nhds t] y :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds htpos) fun s hs => hz_pos s (le_of_lt hs)
      rw [hz_pos t ht.1]
      exact (hy t ht).congr_of_eventuallyEq hEv
    · subst ht0
      rw [hz_pos 0 le_rfl]
      have hright : HasDerivWithinAt z (F (y 0)) (Set.Ici 0) 0 :=
        ((hy 0 ht).hasDerivWithinAt).congr (fun s hs => hz_pos s hs) (hz_pos 0 le_rfl)
      have hleft : HasDerivWithinAt z (F (y 0)) (Set.Iic 0) 0 :=
        ((hlin 0).hasDerivWithinAt).congr (fun s hs => hz_neg s hs) (hz_neg 0 le_rfl)
      simpa [Set.Iic_union_Ici] using hleft.union hright
  refine ⟨z, fun t ht => ?_, hz_pos, hderiv⟩
  by_cases ht0 : 0 ≤ t
  · exact (hderiv t ⟨ht0, ht⟩).continuousAt.continuousWithinAt
  · have hEv : (fun t : ℝ => y 0 + t • v) =ᶠ[nhds t] z :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds (lt_of_not_ge ht0))
        fun s hs => (hz_neg s (le_of_lt hs)).symm
    exact ((hlin t).continuousAt.congr hEv).continuousWithinAt

/-! ## The compiled solution on `[0, ∞)` from a blow-up on `[0, T)` -/

/-- The data of the time change for an unbounded solution on `[0, T)` (BC.md §1.5): the
re-chosen solution `y'`, the inverse time change `s` with values in `[0, T)` on `τ ≥ 0`, the
equation `z' = F(z)/P(z)` for `z = y' ∘ s`, and `s → T⁻`. -/
theorem exists_timeChange_of_blowup (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) {T : ℝ} (hT : 0 < T)
    (y : ℝ → Fin d → ℝ) (hy : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (P.evalField (y t)) t)
    (hunb : ¬ BddAbove ((fun t => ‖y t‖) '' Set.Ico 0 T)) :
    ∃ (y' : ℝ → Fin d → ℝ) (s : ℝ → ℝ), (∀ t, 0 ≤ t → y' t = y t) ∧ s 0 = 0 ∧
      (∀ τ, 0 ≤ τ → 0 ≤ s τ ∧ s τ < T) ∧ Continuous (fun τ => y' (s τ)) ∧
      Continuous s ∧ Tendsto s atTop (nhdsWithin T (Set.Iio T)) ∧
      (∀ τ, HasDerivAt s (jointClock N (y' (s τ)))⁻¹ τ) ∧
      (∀ τ, 0 ≤ τ → ∀ i, HasDerivAt (fun σ => y' (s σ) i)
        (P.evalField (y' (s τ)) i / jointClock N (y' (s τ))) τ) := by
  obtain ⟨y', hc, hagree, hd⟩ := exists_extension_Iio hT y hy
  have hρc : ContinuousOn (fun t => jointClock N (y' t)) (Set.Iio T) :=
    (continuous_jointClock N).comp_continuousOn hc
  have hρ1 : ∀ u, 1 ≤ (fun t => jointClock N (y' t)) u := fun u => jointClock_ge_one hN _
  -- the clock is unbounded on `[0, T)`: `|yᵢ(t) − yᵢ(0)| ≤ C_F θ(t)`
  have hθunb : ¬ BddAbove (clockIntegral (fun t => jointClock N (y' t)) '' Set.Ico 0 T) := by
    rintro ⟨K, hK⟩
    apply hunb
    let CF : ℝ := ∑ i, ∑ b : MIndex d N, |((((P.field i).coeff b.toFinsupp : ℚ)) : ℝ)|
    refine ⟨∑ i, |y 0 i| + CF * max K 0, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have hθt : clockIntegral (fun t => jointClock N (y' t)) t ≤ max K 0 :=
      (hK ⟨t, ht, rfl⟩).trans (le_max_left _ _)
    have hci : ∀ i, ContinuousOn (fun u => P.evalField (y' u) i) (Set.Icc 0 t) := fun i =>
      ((continuous_apply i).comp P.continuous_evalField).comp_continuousOn
        (hc.mono fun u hu => lt_of_le_of_lt hu.2 ht.2)
    have hcoord : ∀ i, |y t i| ≤ |y 0 i| + CF * max K 0 := by
      intro i
      have hderiv : ∀ u ∈ Set.uIcc 0 t, HasDerivAt (fun u => y' u i)
          (P.evalField (y' u) i) u := by
        intro u hu
        rw [Set.uIcc_of_le ht.1] at hu
        exact hasDerivAt_pi.mp (hd u ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩) i
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((hci i).intervalIntegrable_of_Icc ht.1)
      have hF : ∀ u ∈ Set.Icc 0 t, |P.evalField (y' u) i| ≤
          CF * jointClock N (y' u) := by
        intro u _
        refine (abs_eval₂_le_jointClock hN (P.field i) (hdeg i) (y' u)).trans ?_
        apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (jointClock_ge_one hN _))
        exact Finset.single_le_sum (f := fun i => ∑ b : MIndex d N,
          |((((P.field i).coeff b.toFinsupp : ℚ)) : ℝ)|)
          (fun i _ => Finset.sum_nonneg fun b _ => abs_nonneg _) (Finset.mem_univ i)
      have hCF : 0 ≤ CF := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun b _ => abs_nonneg _
      have hint : |∫ u in (0 : ℝ)..t, P.evalField (y' u) i| ≤
          CF * clockIntegral (fun t => jointClock N (y' t)) t := by
        calc |∫ u in (0 : ℝ)..t, P.evalField (y' u) i|
            ≤ ∫ u in (0 : ℝ)..t, |P.evalField (y' u) i| :=
              intervalIntegral.abs_integral_le_integral_abs ht.1
          _ ≤ ∫ u in (0 : ℝ)..t, CF * jointClock N (y' u) :=
              intervalIntegral.integral_mono_on ht.1
                (((hci i).abs).intervalIntegrable_of_Icc ht.1)
                ((((continuous_jointClock N).comp_continuousOn
                  (hc.mono fun u hu => lt_of_le_of_lt hu.2 ht.2)).const_smul CF).intervalIntegrable_of_Icc
                  ht.1)
                hF
          _ = CF * clockIntegral (fun t => jointClock N (y' t)) t := by
              unfold clockIntegral; exact intervalIntegral.integral_const_mul _ _
      rw [hftc, hagree t ht.1, hagree 0 le_rfl] at hint
      have := abs_sub_abs_le_abs_sub (y t i) (y 0 i)
      have := mul_le_mul_of_nonneg_left hθt hCF
      linarith
    show ‖y t‖ ≤ _
    refine (pi_norm_le_iff_of_nonneg ?_).2 fun i => ?_
    · exact add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
        (mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun b _ => abs_nonneg _)
          (le_max_right _ _))
    · rw [Real.norm_eq_abs]
      refine (hcoord i).trans ?_
      have : |y 0 i| ≤ ∑ j, |y 0 j| :=
        Finset.single_le_sum (f := fun j => |y 0 j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      linarith
  obtain ⟨s, hs0, hsT, hsd, hsc, hsm, hst, -⟩ := exists_inverse_timeChange_Iio hT hρc hρ1 hθunb
  have hs_nn : ∀ τ, 0 ≤ τ → 0 ≤ s τ := fun τ hτ => hs0 ▸ hsm.monotone hτ
  refine ⟨y', s, hagree, hs0, fun τ hτ => ⟨hs_nn τ hτ, hsT τ⟩, ?_, hsc, hst, hsd, ?_⟩
  · exact hc.comp_continuous hsc fun τ => hsT τ
  · intro τ hτ i
    have h := (hd (s τ) ⟨hs_nn τ hτ, hsT τ⟩).scomp τ (hsd τ)
    refine (hasDerivAt_pi.mp h i).congr_deriv ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_eq_inv_mul]

/-- A function continuous on `[0, T)` with a limit at `T⁻` is bounded on `[0, T)`. -/
theorem exists_abs_le_of_tendsto_Iio {f : ℝ → ℝ} {α T : ℝ} (hT : 0 < T)
    (hc : ∀ t ∈ Set.Ico 0 T, ContinuousAt f t)
    (hlim : Tendsto f (nhdsWithin T (Set.Iio T)) (nhds α)) :
    ∃ M, 0 < M ∧ ∀ t ∈ Set.Ico 0 T, |f t| ≤ M := by
  have hev : ∀ᶠ t in nhdsWithin T (Set.Iio T), |f t - α| < 1 := by
    have := (Metric.tendsto_nhds.mp hlim) 1 one_pos
    simpa [Real.dist_eq] using this
  obtain ⟨a, ha, hav⟩ := (mem_nhdsLT_iff_exists_Ioo_subset.mp hev)
  have hcont : ContinuousOn f (Set.Icc 0 (max a 0)) := fun t ht =>
    (hc t ⟨ht.1, lt_of_le_of_lt ht.2 (max_lt ha hT)⟩).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max (max C (|α| + 1)) 1, lt_max_of_lt_right one_pos, fun t ht => ?_⟩
  by_cases hta : t ≤ max a 0
  · have h := hC t ⟨ht.1, hta⟩
    rw [Real.norm_eq_abs] at h
    exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
  · push Not at hta
    have h1 : |f t - α| < 1 := hav ⟨(le_max_left a 0).trans_lt hta, ht.2⟩
    have h2 : |f t| ≤ |α| + 1 := by
      have := abs_sub_abs_le_abs_sub (f t) α
      linarith
    exact h2.trans ((le_max_right _ _).trans (le_max_left _ _))

/-- An unbounded solution on `[0, T)` forces `T > 0` (`[0, T)` is empty otherwise). -/
theorem pos_of_not_bddAbove {T : ℝ} {y : ℝ → Fin d → ℝ}
    (hunb : ¬ BddAbove ((fun t => ‖y t‖) '' Set.Ico 0 T)) : 0 < T := by
  by_contra h
  push Not at h
  apply hunb
  rw [Set.Ico_eq_empty (not_lt.mpr h), Set.image_empty]
  exact bddAbove_empty

/-! ## [BAC] Prop 3.2 at a finite blow-up: the output limit is kept -/

/-- [BAC] Prop 3.2 (`T* < ∞`) with Construction 3.1, BC.md §1.5: a ℚ-PIVP with a solution `y`
on `[0, T)` that is unbounded there and whose output tends to `α` as `t → T⁻` compiles, for
every even `N` at least the degree of the field, to the bounded ℚ-PIVP
`P.jointSurrogateCompile N`, which computes `α`. -/
theorem bounded_compilation_of_blowup_certified {α T : ℝ} (P : PolyPIVP d) {N : ℕ}
    (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N)
    (y : ℝ → Fin d → ℝ) (hy0 : y 0 = fun i => (P.init i : ℝ))
    (hy : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (P.evalField (y t)) t)
    (hunb : ¬ BddAbove ((fun t => ‖y t‖) '' Set.Ico 0 T))
    (hlim : Tendsto (fun t => y t P.output) (nhdsWithin T (Set.Iio T)) (nhds α)) :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim d N) α,
      btc.pivp = P.jointSurrogateCompile N := by
  have hT : 0 < T := pos_of_not_bddAbove hunb
  obtain ⟨y', s, hagree, hs0, hsT, hzc, -, hst, -, hz⟩ :=
    exists_timeChange_of_blowup P hN hdeg hT y hy hunb
  have hz0 : y' (s 0) = fun i => (P.init i : ℝ) := by rw [hs0, hagree 0 le_rfl, hy0]
  obtain ⟨sol', hout, hsur, hcont⟩ :=
    P.jointSurrogateCompile_solution_of_curve hN hdeg (fun σ => y' (s σ)) hz0 hz
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_tendsto_Iio hT
    (fun t ht => (continuous_apply P.output).continuousAt.comp (hy t ht).continuousAt) hlim
  have hbd := jointSurrogateCompile_isBounded P hN sol' (fun σ => y' (s σ))
    (fun τ _ => hout τ) (fun τ _ a => hsur τ a) (fun τ hτ => by
      change |y' (s τ) P.output| ≤ M
      rw [hagree _ (hsT τ hτ).1]
      exact hM _ (hsT τ hτ))
  have hlim' : Tendsto (fun τ => sol'.trajectory τ (P.jointSurrogateCompile N).output)
      atTop (nhds α) := by
    refine (hlim.comp hst).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    rw [hout τ]
    change y (s τ) P.output = y' (s τ) P.output
    rw [hagree _ (hsT τ hτ).1]
  obtain ⟨btc, hbtc, -⟩ :=
    CertifiedBoundedTimeComputable.exists_of_tendsto _ sol' hbd (hcont hzc) hlim'
  exact ⟨btc, hbtc⟩

/-- [BAC] Prop 3.2 (`T* < ∞`), existence form. -/
theorem bounded_compilation_of_blowup {α T : ℝ} (P : PolyPIVP d)
    (y : ℝ → Fin d → ℝ) (hy0 : y 0 = fun i => (P.init i : ℝ))
    (hy : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (P.evalField (y t)) t)
    (hunb : ¬ BddAbove ((fun t => ‖y t‖) '' Set.Ico 0 T))
    (hlim : Tendsto (fun t => y t P.output) (nhdsWithin T (Set.Iio T)) (nhds α)) :
    IsCRNComputable α := by
  have hdeg : ∀ i, (P.field i).totalDegree ≤ 2 * Finset.univ.sup fun j => (P.field j).totalDegree :=
    fun i => (Finset.le_sup (f := fun j => (P.field j).totalDegree) (Finset.mem_univ i)).trans
      (Nat.le_mul_of_pos_left _ two_pos)
  obtain ⟨btc, -⟩ :=
    bounded_compilation_of_blowup_certified P (even_two_mul _) hdeg y hy0 hy hunb hlim
  exact ⟨_, ⟨btc⟩⟩

/-! ## [BAC] Thm 3.4: the blow-up time, without the kept output (review P1) -/

/-- The clock-compiled field over the index type: `s' = W₀` on the clock coordinate (`none`)
and the surrogate lines on `some a`. -/
noncomputable def clockField (P : PolyPIVP d) (N : ℕ) :
    CompiledIndex d N → MvPolynomial (CompiledIndex d N) ℚ
  | none => X (some (SurrogateIndex.zero d N))
  | some a => surrogateField P N a

/-- The clock-compiled initial value: `s(0) = 0`, `W_a(0) = W_a(y₀)`. -/
noncomputable def clockInit (P : PolyPIVP d) (N : ℕ) : CompiledIndex d N → ℚ
  | none => 0
  | some a => surrogateInit P N a

/-- [BAC] Thm 3.4 construction (BC.md §1.5, review P1): state `(s, (W_a)_{|a| ≤ N})`,
`s' = W₀ = 1/P(y)`, output `s`. No original coordinate is kept, so the system is bounded even
when the output coordinate of `P` blows up. -/
noncomputable def PolyPIVP.jointClockCompile (P : PolyPIVP d) (N : ℕ) :
    PolyPIVP (jointDim d N) :=
  PolyPIVP.ofIndexed (clockField P N) (clockInit P N) none

theorem jointClockCompile_output (P : PolyPIVP d) (N : ℕ) :
    (P.jointClockCompile N).output = Fintype.equivFin (CompiledIndex d N) none := rfl

/-- The clock-compiled curve over the index type. -/
noncomputable def clockCurve (N : ℕ) (s : ℝ → ℝ) (z : ℝ → Fin d → ℝ) (τ : ℝ) :
    CompiledIndex d N → ℝ
  | none => s τ
  | some a => jointSurrogate N a (z τ)

/-- A time change `s` with `s(0) = 0`, `s' = 1/P(z)` and a curve `z` with `z(0) = y₀`,
`z' = F(z)/P(z)` give the solution `τ ↦ (s(τ), (W_a(z(τ)))_a)` of the clock-compiled system. -/
theorem PolyPIVP.jointClockCompile_solution_of_curve (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) (s : ℝ → ℝ) (z : ℝ → Fin d → ℝ)
    (hs0 : s 0 = 0) (hz0 : z 0 = fun i => (P.init i : ℝ))
    (hsd : ∀ τ, 0 ≤ τ → HasDerivAt s (jointClock N (z τ))⁻¹ τ)
    (hz : ∀ τ, 0 ≤ τ → ∀ i, HasDerivAt (fun σ => z σ i)
      (P.evalField (z τ) i / jointClock N (z τ)) τ) :
    ∃ sol' : PIVP.Solution (P.jointClockCompile N).toPIVP,
      (∀ τ, sol'.trajectory τ (P.jointClockCompile N).output = s τ) ∧
      (∀ τ (a : SurrogateIndex d N),
        sol'.trajectory τ (surrogateCoord a) = jointSurrogate N a (z τ)) ∧
      (Continuous s → Continuous z → Continuous sol'.trajectory) := by
  have hZ0 : ∀ k, clockCurve N s z 0 k = (clockInit P N k : ℝ) := by
    intro k
    cases k with
    | none => simp [clockCurve, clockInit, hs0]
    | some a => simp only [clockCurve, clockInit, hz0, surrogateInit_cast]
  have hZd : ∀ τ, 0 ≤ τ → ∀ k, HasDerivAt (fun σ => clockCurve N s z σ k)
      ((clockField P N k).eval₂ (Rat.castHom ℝ) (clockCurve N s z τ)) τ := by
    intro τ hτ k
    cases k with
    | none =>
      change HasDerivAt s ((X (some (SurrogateIndex.zero d N)) :
        MvPolynomial (CompiledIndex d N) ℚ).eval₂ (Rat.castHom ℝ) (clockCurve N s z τ)) τ
      rw [eval₂_X]
      change HasDerivAt s (jointSurrogate N (SurrogateIndex.zero d N) (z τ)) τ
      rw [jointSurrogate, SurrogateIndex.zero_eval, one_div]
      exact hsd τ hτ
    | some a =>
      exact hasDerivAt_jointSurrogate P hN hdeg a z τ (hz τ hτ) _ (fun _ => rfl)
  obtain ⟨sol', hsol'⟩ := PolyPIVP.ofIndexed_solution (clockField P N) (clockInit P N) none
    _ hZ0 hZd
  refine ⟨sol', fun τ => ?_, fun τ a => ?_, fun hsc hzc => ?_⟩
  · rw [hsol']
    simp only [jointClockCompile_output, Equiv.symm_apply_apply]
    rfl
  · rw [hsol']
    simp only [surrogateCoord, Equiv.symm_apply_apply]
    rfl
  · rw [hsol']
    refine continuous_pi fun j => ?_
    cases h : (Fintype.equivFin (CompiledIndex d N)).symm j with
    | none => simpa [clockCurve, h] using hsc
    | some a => simpa [clockCurve, h] using (continuous_jointSurrogate hN a).comp hzc

/-- [BAC] Thm 3.4 (blow-up times are computable), certified form, BC.md §1.5: if a ℚ-PIVP has a
solution `y` on `[0, T)` that is unbounded there (the maximal existence time is `T < ∞`), then
the bounded ℚ-PIVP `P.jointClockCompile N` computes `T`, for every even `N` at least the degree
of the field. -/
theorem isCRNComputable_blowupTime_certified {T : ℝ} (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N)
    (y : ℝ → Fin d → ℝ) (hy0 : y 0 = fun i => (P.init i : ℝ))
    (hy : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (P.evalField (y t)) t)
    (hunb : ¬ BddAbove ((fun t => ‖y t‖) '' Set.Ico 0 T)) :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim d N) T,
      btc.pivp = P.jointClockCompile N := by
  have hT : 0 < T := pos_of_not_bddAbove hunb
  obtain ⟨y', s, hagree, hs0, hsT, hzc, hsc, hst, hsd, hz⟩ :=
    exists_timeChange_of_blowup P hN hdeg hT y hy hunb
  have hz0 : y' (s 0) = fun i => (P.init i : ℝ) := by rw [hs0, hagree 0 le_rfl, hy0]
  obtain ⟨sol', hout, hsur, hcont⟩ := P.jointClockCompile_solution_of_curve hN hdeg s
    (fun σ => y' (s σ)) hs0 hz0 (fun τ _ => hsd τ) hz
  have hbd : (P.jointClockCompile N).toPIVP.IsBounded sol'.trajectory := by
    refine ⟨max T 1, lt_max_of_lt_right one_pos, fun τ hτ => ?_⟩
    refine (pi_norm_le_iff_of_nonneg (le_trans zero_le_one (le_max_right _ _))).2 fun j => ?_
    rw [Real.norm_eq_abs]
    rcases jointCoord_cases j with rfl | ⟨a, rfl⟩
    · rw [← jointClockCompile_output, hout τ, abs_of_nonneg (hsT τ hτ).1]
      exact (hsT τ hτ).2.le.trans (le_max_left _ _)
    · rw [hsur τ a]
      exact (jointSurrogate_abs_le_one hN a _).trans (le_max_right _ _)
  have hlim' : Tendsto (fun τ => sol'.trajectory τ (P.jointClockCompile N).output)
      atTop (nhds T) := by
    have hfun : (fun τ => sol'.trajectory τ (P.jointClockCompile N).output) = s := funext hout
    rw [hfun]
    exact (tendsto_nhdsWithin_iff.mp hst).1
  obtain ⟨btc, hbtc, -⟩ :=
    CertifiedBoundedTimeComputable.exists_of_tendsto _ sol' hbd (hcont hsc hzc) hlim'
  exact ⟨btc, hbtc⟩

/-- [BAC] Thm 3.4, existence form: the finite blow-up time of a ℚ-PIVP is CRN-computable. -/
theorem isCRNComputable_blowupTime {T : ℝ} (P : PolyPIVP d)
    (y : ℝ → Fin d → ℝ) (hy0 : y 0 = fun i => (P.init i : ℝ))
    (hy : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (P.evalField (y t)) t)
    (hunb : ¬ BddAbove ((fun t => ‖y t‖) '' Set.Ico 0 T)) :
    IsCRNComputable T := by
  have hdeg : ∀ i, (P.field i).totalDegree ≤ 2 * Finset.univ.sup fun j => (P.field j).totalDegree :=
    fun i => (Finset.le_sup (f := fun j => (P.field j).totalDegree) (Finset.mem_univ i)).trans
      (Nat.le_mul_of_pos_left _ two_pos)
  obtain ⟨btc, -⟩ := isCRNComputable_blowupTime_certified P (even_two_mul _) hdeg y hy0 hy hunb
  exact ⟨_, ⟨btc⟩⟩

end Ripple

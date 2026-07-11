import Ripple.CTMC.DensityDependentAbsorbing

open MeasureTheory

/-- Pathwise upper cap via last-entry-time argument: if a readout `φ` starts at or
below `β`, its drift `g` is at most `κ` wherever `φ > β` on `[0,T]`, and the
compensated residual `φ t - φ 0 - ∫₀ᵗ g` stays within `S`, then
`φ ≤ β + κ·T + 2S` throughout `[0,T]`. No continuity of `φ` is needed. -/
lemma scratch_pathwise_cap {φ g : ℝ → ℝ} {T S β κ Cg : ℝ}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hκ : 0 ≤ κ) (hCg : 0 ≤ Cg)
    (hφmeas : Measurable φ)
    (hgint : IntegrableOn g (Set.Icc 0 T) volume)
    (hres : ∀ t, 0 ≤ t → t ≤ T → |φ t - φ 0 - ∫ s in Set.Icc (0:ℝ) t, g s| ≤ S)
    (h0 : φ 0 ≤ β)
    (hg : ∀ s, 0 ≤ s → s ≤ T → β < φ s → g s ≤ κ)
    (hgbd : ∀ s, 0 ≤ s → s ≤ T → |g s| ≤ Cg) :
    ∀ t, 0 ≤ t → t ≤ T → φ t ≤ β + κ * T + 2 * S := by
  intro t ht0 htT
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set E : Set ℝ := {s | s ∈ Set.Icc (0:ℝ) t ∧ φ s ≤ β} with hEdef
  have hE0 : (0:ℝ) ∈ E := ⟨⟨le_refl 0, ht0⟩, h0⟩
  have hEne : E.Nonempty := ⟨0, hE0⟩
  have hEbdd : BddAbove E := ⟨t, fun s hs => hs.1.2⟩
  set τ := sSup E with hτdef
  have hτt : τ ≤ t := csSup_le hEne fun s hs => hs.1.2
  have hδpos : 0 < ε / (Cg + 1) := by positivity
  obtain ⟨u, huE, huτ⟩ : ∃ u ∈ E, τ - ε / (Cg + 1) < u :=
    exists_lt_of_lt_csSup hEne (by linarith : τ - ε / (Cg + 1) < τ)
  have huτ' : u ≤ τ := le_csSup hEbdd huE
  have hu0 : 0 ≤ u := huE.1.1
  have hut : u ≤ t := huE.1.2
  have huT : u ≤ T := le_trans hut htT
  -- split [0,t] = [0,u] ∪ (u,t]
  have hint_Icc_u : IntegrableOn g (Set.Icc 0 u) volume :=
    hgint.mono_set (Set.Icc_subset_Icc le_rfl huT)
  have hint_Ioc : IntegrableOn g (Set.Ioc u t) volume :=
    hgint.mono_set fun s hs => ⟨le_trans hu0 hs.1.le, le_trans hs.2 htT⟩
  have hdisj0 : Disjoint (Set.Icc (0:ℝ) u) (Set.Ioc u t) := by
    rw [Set.disjoint_left]
    rintro s ⟨_, hsu⟩ ⟨hus, _⟩
    exact absurd hsu (not_le.mpr hus)
  have hsplit : ∫ s in Set.Icc (0:ℝ) t, g s =
      (∫ s in Set.Icc (0:ℝ) u, g s) + ∫ s in Set.Ioc u t, g s := by
    rw [← Set.Icc_union_Ioc_eq_Icc hu0 hut]
    exact setIntegral_union hdisj0 measurableSet_Ioc hint_Icc_u hint_Ioc
  -- split (u,t] by the level β
  set A₁ : Set ℝ := Set.Ioc u t ∩ {s | φ s ≤ β} with hA₁def
  set A₂ : Set ℝ := Set.Ioc u t ∩ {s | β < φ s} with hA₂def
  have hA₁meas : MeasurableSet A₁ := measurableSet_Ioc.inter (hφmeas measurableSet_Iic)
  have hA₂meas : MeasurableSet A₂ := measurableSet_Ioc.inter (hφmeas measurableSet_Ioi)
  have hA_union : Set.Ioc u t = A₁ ∪ A₂ := by
    ext s
    constructor
    · intro hs
      by_cases hφs : φ s ≤ β
      · exact Or.inl ⟨hs, hφs⟩
      · exact Or.inr ⟨hs, lt_of_not_ge hφs⟩
    · rintro (⟨hs, _⟩ | ⟨hs, _⟩) <;> exact hs
  have hdisj12 : Disjoint A₁ A₂ := by
    rw [Set.disjoint_left]
    rintro s ⟨_, h₁⟩ ⟨_, h₂⟩
    simp only [Set.mem_setOf_eq] at h₁ h₂
    exact absurd h₁ (not_le.mpr h₂)
  have hsplit2 : ∫ s in Set.Ioc u t, g s = (∫ s in A₁, g s) + ∫ s in A₂, g s := by
    rw [hA_union]
    exact setIntegral_union hdisj12 hA₂meas
      (hint_Ioc.mono_set (hA_union ▸ Set.subset_union_left))
      (hint_Ioc.mono_set (hA_union ▸ Set.subset_union_right))
  -- A₁ sits inside (u, τ]
  have hA₁sub : A₁ ⊆ Set.Ioc u τ := by
    rintro s ⟨hs, hφs⟩
    exact ⟨hs.1, le_csSup hEbdd ⟨⟨le_trans hu0 hs.1.le, hs.2⟩, hφs⟩⟩
  have hvolA₁ : volume A₁ ≤ ENNReal.ofReal (τ - u) := by
    calc volume A₁ ≤ volume (Set.Ioc u τ) := measure_mono hA₁sub
      _ = ENNReal.ofReal (τ - u) := Real.volume_Ioc
  have hA₁lt_top : volume A₁ < ⊤ := lt_of_le_of_lt hvolA₁ ENNReal.ofReal_lt_top
  have hvolA₁real : volume.real A₁ ≤ τ - u := by
    rw [Measure.real_def]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) hvolA₁
  have hA₁bound : (∫ s in A₁, g s) ≤ Cg * (ε / (Cg + 1)) := by
    have h1 : ‖∫ s in A₁, g s‖ ≤ Cg * volume.real A₁ :=
      norm_setIntegral_le_of_norm_le_const hA₁lt_top fun s hs => by
        rw [Real.norm_eq_abs]
        exact hgbd s (le_trans hu0 hs.1.1.le) (le_trans hs.1.2 htT)
    have h2 : (∫ s in A₁, g s) ≤ Cg * volume.real A₁ :=
      le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at h1)
    calc (∫ s in A₁, g s) ≤ Cg * volume.real A₁ := h2
      _ ≤ Cg * (τ - u) := by
          exact mul_le_mul_of_nonneg_left hvolA₁real hCg
      _ ≤ Cg * (ε / (Cg + 1)) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hCg
  -- A₂ integral ≤ κ T
  have hA₂vol_lt_top : volume A₂ < ⊤ := by
    have : volume A₂ ≤ volume (Set.Ioc u t) :=
      measure_mono (hA_union ▸ Set.subset_union_right)
    calc volume A₂ ≤ volume (Set.Ioc u t) := this
      _ = ENNReal.ofReal (t - u) := Real.volume_Ioc
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hvolA₂real : volume.real A₂ ≤ t - u := by
    rw [Measure.real_def]
    refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
    calc volume A₂ ≤ volume (Set.Ioc u t) :=
          measure_mono (hA_union ▸ Set.subset_union_right)
      _ = ENNReal.ofReal (t - u) := Real.volume_Ioc
  have hA₂bound : (∫ s in A₂, g s) ≤ κ * T := by
    have hstep : (∫ s in A₂, g s) ≤ ∫ _s in A₂, κ := by
      refine setIntegral_mono_on
        (hint_Ioc.mono_set (hA_union ▸ Set.subset_union_right))
        (integrableOn_const hA₂vol_lt_top.ne)
        hA₂meas fun s hs => ?_
      exact hg s (le_trans hu0 hs.1.1.le) (le_trans hs.1.2 htT) hs.2
    have hconst : (∫ _s in A₂, κ) = volume.real A₂ * κ := by
      rw [setIntegral_const, smul_eq_mul]
    calc (∫ s in A₂, g s) ≤ volume.real A₂ * κ := hstep.trans_eq hconst
      _ ≤ (t - u) * κ := mul_le_mul_of_nonneg_right hvolA₂real hκ
      _ ≤ T * κ := by
          have : t - u ≤ T := by linarith
          exact mul_le_mul_of_nonneg_right this hκ
      _ = κ * T := mul_comm _ _
  -- assemble
  have hres_t := abs_le.mp (hres t ht0 htT)
  have hres_u := abs_le.mp (hres u hu0 huT)
  have hφu : φ u ≤ β := huE.2
  have hCgε : Cg * (ε / (Cg + 1)) ≤ ε := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Cg + 1)]
    nlinarith
  have key : φ t = φ u + ((φ t - φ 0 - ∫ s in Set.Icc (0:ℝ) t, g s)
      - (φ u - φ 0 - ∫ s in Set.Icc (0:ℝ) u, g s)) + ∫ s in Set.Ioc u t, g s := by
    rw [hsplit]; ring
  rw [key, hsplit2]
  linarith [hres_t.1, hres_t.2, hres_u.1, hres_u.2]

/-- Pathwise bound for the boundary part of a drift integral: if `g ≥ 0` on the
boundary set `B`, `g ≥ -εs` off `B`, and the running integral of `g` is at most `S`
at every boundary time, then the boundary part of the integral is at most `S + εs·T`. -/
lemma scratch_boundary_bound {g : ℝ → ℝ} {B : Set ℝ} {T S εs Cg : ℝ}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hεs : 0 ≤ εs) (hCg : 0 ≤ Cg)
    (hBmeas : MeasurableSet B)
    (hgint : IntegrableOn g (Set.Icc 0 T) volume)
    (hgbd : ∀ s, 0 ≤ s → s ≤ T → |g s| ≤ Cg)
    (hgoff : ∀ s, 0 ≤ s → s ≤ T → s ∉ B → -εs ≤ g s)
    (hup : ∀ u, 0 ≤ u → u ≤ T → u ∈ B → (∫ s in Set.Icc (0:ℝ) u, g s) ≤ S) :
    (∫ s in Set.Icc 0 T ∩ B, g s) ≤ S + εs * T := by
  by_cases hne : (Set.Icc (0:ℝ) T ∩ B).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [Measure.restrict_empty, integral_zero_measure]
    positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hbdd : BddAbove (Set.Icc (0:ℝ) T ∩ B) := ⟨T, fun s hs => hs.1.2⟩
  set τ := sSup (Set.Icc (0:ℝ) T ∩ B) with hτdef
  have hδpos : 0 < ε / (Cg + 1) := by positivity
  obtain ⟨u, huB, huτ⟩ : ∃ u ∈ Set.Icc (0:ℝ) T ∩ B, τ - ε / (Cg + 1) < u :=
    exists_lt_of_lt_csSup hne (by linarith : τ - ε / (Cg + 1) < τ)
  have huτ' : u ≤ τ := le_csSup hbdd huB
  have hu0 : 0 ≤ u := huB.1.1
  have huT : u ≤ T := huB.1.2
  -- split Icc 0 T ∩ B = (Icc 0 u ∩ B) ∪ (Ioc u T ∩ B)
  have hunion : Set.Icc (0:ℝ) T ∩ B = (Set.Icc (0:ℝ) u ∩ B) ∪ (Set.Ioc u T ∩ B) := by
    rw [← Set.Icc_union_Ioc_eq_Icc hu0 huT, Set.union_inter_distrib_right]
  have hint1 : IntegrableOn g (Set.Icc (0:ℝ) u ∩ B) volume :=
    hgint.mono_set fun s hs => ⟨hs.1.1, le_trans hs.1.2 huT⟩
  have hint2 : IntegrableOn g (Set.Ioc u T ∩ B) volume :=
    hgint.mono_set fun s hs => ⟨le_trans hu0 hs.1.1.le, hs.1.2⟩
  have hdisj : Disjoint (Set.Icc (0:ℝ) u ∩ B) (Set.Ioc u T ∩ B) := by
    rw [Set.disjoint_left]
    rintro s ⟨⟨_, hsu⟩, _⟩ ⟨⟨hus, _⟩, _⟩
    exact absurd hsu (not_le.mpr hus)
  have hsplit : (∫ s in Set.Icc (0:ℝ) T ∩ B, g s) =
      (∫ s in Set.Icc (0:ℝ) u ∩ B, g s) + ∫ s in Set.Ioc u T ∩ B, g s := by
    rw [hunion]
    exact setIntegral_union hdisj (measurableSet_Ioc.inter hBmeas) hint1 hint2
  -- tail piece is small: Ioc u T ∩ B ⊆ Ioc u τ
  have htail_sub : Set.Ioc u T ∩ B ⊆ Set.Ioc u τ := by
    rintro s ⟨hs, hsB⟩
    exact ⟨hs.1, le_csSup hbdd ⟨⟨le_trans hu0 hs.1.le, hs.2⟩, hsB⟩⟩
  have hvol_tail : volume (Set.Ioc u T ∩ B) ≤ ENNReal.ofReal (τ - u) := by
    calc volume (Set.Ioc u T ∩ B) ≤ volume (Set.Ioc u τ) := measure_mono htail_sub
      _ = ENNReal.ofReal (τ - u) := Real.volume_Ioc
  have htail_lt_top : volume (Set.Ioc u T ∩ B) < ⊤ :=
    lt_of_le_of_lt hvol_tail ENNReal.ofReal_lt_top
  have hvol_tail_real : volume.real (Set.Ioc u T ∩ B) ≤ τ - u := by
    rw [Measure.real_def]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) hvol_tail
  have htail_bound : (∫ s in Set.Ioc u T ∩ B, g s) ≤ Cg * (ε / (Cg + 1)) := by
    have h1 : ‖∫ s in Set.Ioc u T ∩ B, g s‖ ≤ Cg * volume.real (Set.Ioc u T ∩ B) :=
      norm_setIntegral_le_of_norm_le_const htail_lt_top fun s hs => by
        rw [Real.norm_eq_abs]
        exact hgbd s (le_trans hu0 hs.1.1.le) hs.1.2
    have h2 : (∫ s in Set.Ioc u T ∩ B, g s) ≤ Cg * volume.real (Set.Ioc u T ∩ B) :=
      le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at h1)
    calc (∫ s in Set.Ioc u T ∩ B, g s) ≤ Cg * volume.real (Set.Ioc u T ∩ B) := h2
      _ ≤ Cg * (τ - u) := mul_le_mul_of_nonneg_left hvol_tail_real hCg
      _ ≤ Cg * (ε / (Cg + 1)) := mul_le_mul_of_nonneg_left (by linarith) hCg
  -- head piece: ∫_{Icc 0 u ∩ B} g = ∫_{Icc 0 u} g - ∫_{Icc 0 u ∩ Bᶜ} g ≤ S + εs T
  have hint_u : IntegrableOn g (Set.Icc (0:ℝ) u) volume :=
    hgint.mono_set (Set.Icc_subset_Icc le_rfl huT)
  have hsplit_u : (∫ s in Set.Icc (0:ℝ) u, g s) =
      (∫ s in Set.Icc (0:ℝ) u ∩ B, g s) + ∫ s in Set.Icc (0:ℝ) u ∩ Bᶜ, g s := by
    rw [← setIntegral_union ?hd (measurableSet_Icc.inter hBmeas.compl)
      hint1 (hint_u.mono_set Set.inter_subset_left)]
    · congr 1
      rw [← Set.inter_union_distrib_left]
      simp
    case hd =>
      rw [Set.disjoint_left]
      rintro s ⟨_, hsB⟩ ⟨_, hsBc⟩
      exact hsBc hsB
  have hcomp_vol_real : volume.real (Set.Icc (0:ℝ) u ∩ Bᶜ) ≤ T := by
    rw [Measure.real_def]
    refine ENNReal.toReal_le_of_le_ofReal hT ?_
    calc volume (Set.Icc (0:ℝ) u ∩ Bᶜ) ≤ volume (Set.Icc (0:ℝ) T) :=
          measure_mono fun s hs => ⟨hs.1.1, le_trans hs.1.2 huT⟩
      _ = ENNReal.ofReal (T - 0) := Real.volume_Icc
      _ = ENNReal.ofReal T := by rw [sub_zero]
  have hcomp_lt_top : volume (Set.Icc (0:ℝ) u ∩ Bᶜ) < ⊤ := by
    calc volume (Set.Icc (0:ℝ) u ∩ Bᶜ) ≤ volume (Set.Icc (0:ℝ) u) :=
          measure_mono Set.inter_subset_left
      _ < ⊤ := measure_Icc_lt_top
  have hcomp_lb : -(εs * T) ≤ ∫ s in Set.Icc (0:ℝ) u ∩ Bᶜ, g s := by
    have hstep : (∫ _s in Set.Icc (0:ℝ) u ∩ Bᶜ, (-εs)) ≤
        ∫ s in Set.Icc (0:ℝ) u ∩ Bᶜ, g s := by
      refine setIntegral_mono_on (integrableOn_const hcomp_lt_top.ne)
        (hint_u.mono_set Set.inter_subset_left)
        (measurableSet_Icc.inter hBmeas.compl) fun s hs => ?_
      exact hgoff s hs.1.1 (le_trans hs.1.2 huT) hs.2
    have hconst : (∫ _s in Set.Icc (0:ℝ) u ∩ Bᶜ, (-εs)) =
        volume.real (Set.Icc (0:ℝ) u ∩ Bᶜ) * (-εs) := by
      rw [setIntegral_const, smul_eq_mul]
    have : -(εs * T) ≤ volume.real (Set.Icc (0:ℝ) u ∩ Bᶜ) * (-εs) := by
      have hvnn : 0 ≤ volume.real (Set.Icc (0:ℝ) u ∩ Bᶜ) := by
        rw [Measure.real_def]
        exact ENNReal.toReal_nonneg
      nlinarith
    linarith [hconst ▸ hstep]
  have hhead : (∫ s in Set.Icc (0:ℝ) u ∩ B, g s) ≤ S + εs * T := by
    have hup_u := hup u hu0 huT huB.2
    have := hsplit_u
    linarith
  have hCgε : Cg * (ε / (Cg + 1)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0:ℝ) < Cg + 1)]
    nlinarith
  rw [hsplit]
  linarith

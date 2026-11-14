-- Ripple/Kurtz/StrongApprox/CellStoppingLineAdapters.lean
import Ripple.Kurtz.StrongApprox.PoissonStoppingLine
import Ripple.Kurtz.StrongApprox.CellStoppingLineResiduals

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellStoppingLineAdapters

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

/-! ### Deterministic first-wait convergence along a decreasing line -/

section Deterministic

variable {Y : ℝ≥0 → ℕ}

/-- Shift of a right-eventually-constant path. -/
theorem rightConst_shift (hright : ∀ s, ∀ᶠ r in 𝓝[≥] s, Y r = Y s)
    (b s : ℝ≥0) : ∀ᶠ r in 𝓝[≥] s, Y (b + r) = Y (b + s) := by
  have hcont : Tendsto (fun r : ℝ≥0 => b + r) (𝓝[≥] s) (𝓝[≥] (b + s)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (tendsto_const_nhds.add tendsto_id).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      show b + s ≤ b + r
      have hr' : s ≤ r := hr
      gcongr
  exact hcont.eventually (hright (b + s))

theorem firstWait_char {D : ℝ≥0 → ℕ} (hmono : Monotone D) (hD0 : D 0 = 0)
    (hright : ∀ s, ∀ᶠ r in 𝓝[≥] s, D r = D s) (hnz : ∃ s, 0 < D s)
    (t : ℝ≥0) :
    (t : ℝ) < firstWait (fun s => (D s : ℝ)) ↔ D t = 0 :=
  ⟨count_eq_zero_of_lt_firstWait hmono hD0,
    lt_firstWait_of_count_eq_zero hmono hright hnz⟩

theorem firstWait_zero_of_forall {D : ℝ≥0 → ℕ} (h : ∀ s, D s = 0) :
    firstWait (fun s => (D s : ℝ)) = 0 := by
  unfold firstWait firstWaitENN
  have : (⨅ q : ℚ≥0, if 0 < q ∧ 0 < (D (q : ℝ≥0) : ℝ) then
      ((q : ℝ≥0) : ℝ≥0∞) else ⊤) = ⊤ := by
    apply le_antisymm le_top
    refine le_iInf fun q => ?_
    rw [if_neg]
    simp [h]
  rw [this]
  simp

/-- Core convergence: first waits after the decreasing line `a_m ↓ a`. -/
theorem firstWait_shift_tendsto
    (hmono : Monotone Y) (hright : ∀ s, ∀ᶠ r in 𝓝[≥] s, Y r = Y s)
    (a : ℝ≥0) (am : ℕ → ℝ≥0) (ha : ∀ m, a ≤ am m)
    (hlim : Tendsto (fun m => (am m : ℝ)) atTop (𝓝 (a : ℝ))) :
    Tendsto (fun m => firstWait (fun s => ((Y (am m + s) - Y (am m) : ℕ) : ℝ)))
      atTop (𝓝 (firstWait (fun s => ((Y (a + s) - Y a : ℕ) : ℝ)))) := by
  classical
  let D : ℝ≥0 → ℕ := fun s => Y (a + s) - Y a
  have hDmono : Monotone D := fun s t hst =>
    Nat.sub_le_sub_right (hmono (by gcongr)) _
  have hD0 : D 0 = 0 := by simp [D]
  have hDright : ∀ s, ∀ᶠ r in 𝓝[≥] s, D r = D s := by
    intro s
    filter_upwards [rightConst_shift hright a s] with r hr
    simp only [D, hr]
  by_cases hall : ∀ s, D s = 0
  · -- the path is constant after `a`
    have hconst : ∀ m s, Y (am m + s) = Y a := by
      intro m s
      have h1 := hall (am m - a + s)
      have e : a + (am m - a + s) = am m + s := by
        rw [← add_assoc, add_tsub_cancel_of_le (ha m)]
      simp only [D, e] at h1
      have h2 := hmono (le_add_of_nonneg_right zero_le :
        a ≤ a + (am m - a + s))
      rw [e] at h2
      omega
    have hzero : ∀ m s, Y (am m + s) - Y (am m) = 0 := by
      intro m s
      have h0 := hconst m 0
      simp only [add_zero] at h0
      rw [hconst m s, h0]
      simp
    have h1 : firstWait (fun s => ((D s : ℕ) : ℝ)) = 0 :=
      firstWait_zero_of_forall hall
    have h2 : ∀ m, firstWait (fun s => ((Y (am m + s) - Y (am m) : ℕ) : ℝ)) = 0 :=
      fun m => firstWait_zero_of_forall (hzero m)
    simp only [D] at h1
    rw [h1]
    simp only [h2]
    exact tendsto_const_nhds
  · push_neg at hall
    obtain ⟨s0, hs0⟩ := hall
    have hnz : ∃ s, 0 < D s := ⟨s0, Nat.pos_of_ne_zero hs0⟩
    set w := firstWait (fun s => (D s : ℝ)) with hw
    have hwpos : 0 < w := by
      have := (firstWait_char hDmono hD0 hDright hnz 0).2 hD0
      simpa using this
    have hchar := firstWait_char hDmono hD0 hDright hnz
    -- distance
    let d : ℕ → ℝ≥0 := fun m => am m - a
    have hdcoe : ∀ m, (d m : ℝ) = (am m : ℝ) - a := fun m => by
      simp only [d]
      rw [NNReal.coe_sub (ha m)]
    have hdlim : Tendsto (fun m => (d m : ℝ)) atTop (𝓝 0) := by
      have := hlim.sub_const (a : ℝ)
      simpa [hdcoe] using this
    have hdsmall : ∀ᶠ m in atTop, (d m : ℝ) < w :=
      (tendsto_order.1 hdlim).2 w hwpos
    have hform : ∀ m, (d m : ℝ) < w →
        firstWait (fun s => ((Y (am m + s) - Y (am m) : ℕ) : ℝ)) = w - d m := by
      intro m hm
      let Dm : ℝ≥0 → ℕ := fun s => Y (am m + s) - Y (am m)
      have hamEq : ∀ t : ℝ≥0, a + (d m + t) = am m + t := by
        intro t
        rw [← add_assoc]
        simp only [d, add_tsub_cancel_of_le (ha m)]
      have hY0 : Y (am m) = Y a := by
        have h1 := (hchar (d m)).1 hm
        simp only [D] at h1
        have h2 : a + d m = am m := by simp only [d, add_tsub_cancel_of_le (ha m)]
        rw [h2] at h1
        have h3 := hmono (le_add_of_nonneg_right zero_le : a ≤ a + d m)
        rw [h2] at h3
        omega
      have hDmzero : ∀ t : ℝ≥0, Dm t = 0 ↔ (t : ℝ) < w - d m := by
        intro t
        constructor
        · intro h
          by_contra hge
          push_neg at hge
          have hnot : ¬ ((d m + t : ℝ≥0) : ℝ) < w := by
            rw [NNReal.coe_add]
            linarith
          have hpos : D (d m + t) ≠ 0 := fun h0 => hnot ((hchar _).2 h0)
          simp only [D, hamEq] at hpos
          simp only [Dm, hY0] at h
          omega
        · intro h
          have hlt : ((d m + t : ℝ≥0) : ℝ) < w := by
            rw [NNReal.coe_add]
            linarith
          have h1 := (hchar _).1 hlt
          simp only [D, hamEq] at h1
          simp only [Dm, hY0]
          omega
      have hDmmono : Monotone Dm := fun s t hst =>
        Nat.sub_le_sub_right (hmono (by gcongr)) _
      have hDm0 : Dm 0 = 0 := by simp [Dm]
      have hDmright : ∀ s, ∀ᶠ r in 𝓝[≥] s, Dm r = Dm s := by
        intro s
        filter_upwards [rightConst_shift hright (am m) s] with r hr
        simp only [Dm, hr]
      have hDmnz : ∃ s, 0 < Dm s := by
        refine ⟨Real.toNNReal (w - d m), Nat.pos_of_ne_zero fun h0 => ?_⟩
        have hlt := (hDmzero _).1 h0
        rw [Real.coe_toNNReal _ (by linarith)] at hlt
        exact lt_irrefl _ hlt
      have hc := firstWait_char hDmmono hDm0 hDmright hDmnz
      have hvnn : 0 ≤ firstWait (fun s => (Dm s : ℝ)) := by
        unfold firstWait
        split_ifs
        · exact le_rfl
        · exact ENNReal.toReal_nonneg
      show firstWait (fun s => (Dm s : ℝ)) = w - d m
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        have h1 := (hc (Real.toNNReal (w - d m))).1 (by
          rw [Real.coe_toNNReal _ (by linarith)]
          exact hlt)
        have h2 := (hDmzero _).1 h1
        rw [Real.coe_toNNReal _ (by linarith)] at h2
        exact lt_irrefl _ h2
      · by_contra hlt
        push_neg at hlt
        have h1 : Dm (Real.toNNReal (firstWait (fun s => (Dm s : ℝ)))) = 0 := by
          apply (hDmzero _).2
          rw [Real.coe_toNNReal _ hvnn]
          exact hlt
        have h2 := (hc _).2 h1
        rw [Real.coe_toNNReal _ hvnn] at h2
        exact lt_irrefl _ h2
    have hev : ∀ᶠ m in atTop,
        firstWait (fun s => ((Y (am m + s) - Y (am m) : ℕ) : ℝ)) = w - d m := by
      filter_upwards [hdsmall] with m hm using hform m hm
    have hlimit : Tendsto (fun m => w - (d m : ℝ)) atTop (𝓝 w) := by
      simpa using (tendsto_const_nhds (x := w)).sub hdlim
    exact hlimit.congr' (hev.mono fun m hm => hm.symm)

end Deterministic

/-! ### Bridge between the cell-family residual and the flat-driver residual -/

section Bridge

open CellRandomTimeEvaluation CellStoppingLineFreshness CellStoppingLineResiduals

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem firstWait_eq_toReal (Y : ℝ≥0 → ℝ) :
    firstWait Y = (firstWaitENN Y).toReal := by
  unfold firstWait
  split_ifs with h
  · simp [h]
  · rfl

theorem cell_residualWait_eq_firstWait
    (σ : CellFamily ι → ι → ℝ≥0) (c : CellFamily ι) (l : ι) :
    CellRandomTimeEvaluation.residualWait σ c l =
      firstWait (fun s : ℝ≥0 => (shiftedCount σ c l s : ℝ)) := by
  unfold CellRandomTimeEvaluation.residualWait residualWaitE
  rw [firstWait_eq_toReal]
  unfold firstWaitENN
  congr 1
  refine iInf_congr fun q => ?_
  simp only [Nat.cast_pos]

theorem shiftedCount_eq_path
    (σ : CellFamily ι → ι → ℝ≥0) (c : CellFamily ι) (l : ι) (s : ℝ≥0) :
    shiftedCount σ c l s =
      cellPath ((σ c l + s : ℝ≥0) : ℝ) (c l) - cellPath ((σ c l : ℝ≥0) : ℝ) (c l) := by
  unfold shiftedCount
  rw [NNReal.coe_add]

theorem deterministicResidual_eq (u : ι → ℝ≥0) (c : CellFamily ι) (l : ι) :
    deterministicResidual u c l =
      Ripple.Kurtz.StrongApprox.residualWait u (flatCellDriver c) l := by
  unfold deterministicResidual residualVector
  rw [cell_residualWait_eq_firstWait]
  show firstWait _ = firstWait _
  congr 1
  funext s
  rw [shiftedCount_eq_path]
  simp only [shiftDriver, flatCellDriver]
  rw [Nat.cast_sub (Ripple.Kurtz.StrongApprox.cellPath_mono (by
    rw [NNReal.coe_add]
    exact le_add_of_nonneg_right s.2) (c l))]

theorem cellPast_le_comap (u : ι → ℝ≥0) :
    cellPast u ≤ MeasurableSpace.comap
      (fun c : CellFamily ι => completePast u (flatCellDriver c))
      inferInstance := by
  unfold cellPast
  refine iSup_le fun l => iSup_le fun s => iSup_le fun hs => ?_
  intro S hS
  obtain ⟨T, hT, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hS
  refine (MeasurableSpace.measurableSet_comap).2
    ⟨{Y : FlatDriver ι | Y (l, s) ∈ ((↑) : ℕ → ℝ) '' T}, ?_, ?_⟩
  · exact (measurable_pi_apply (l, s)) (((Set.to_countable T).image _).measurableSet)
  · ext c
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [completePast_apply_of_le u _ hs]
    exact Nat.cast_injective.mem_set_image

theorem deterministicResidualFresh :
    DeterministicResidualFresh (ι := ι) := by
  refine ⟨measurable_deterministicResidual, ?_⟩
  intro u A B hA hB
  let μ := cellFamilyLaw ι
  let Φ : CellFamily ι → FlatDriver ι := fun c => completePast u (flatCellDriver c)
  obtain ⟨A', hA', hAeq⟩ :=
    (MeasurableSpace.measurableSet_comap).1 (cellPast_le_comap u A hA)
  let S : Set (FlatDriver ι) :=
    {Y | completePast u Y ∈ A' ∧ Ripple.Kurtz.StrongApprox.residualWait u Y ∈ B}
  have hpair : Measurable fun Y : FlatDriver ι =>
      (completePast u Y, Ripple.Kurtz.StrongApprox.residualWait u Y) :=
    (measurable_completePast u).prodMk (measurable_residualWait u)
  have hSm : MeasurableSet S := hpair (hA'.prod hB)
  have hset : A ∩ deterministicResidual u ⁻¹' B = flatCellDriver ⁻¹' S := by
    ext c
    have hres : deterministicResidual u c =
        Ripple.Kurtz.StrongApprox.residualWait u (flatCellDriver c) :=
      funext (deterministicResidual_eq u c)
    simp only [Set.mem_inter_iff, Set.mem_preimage, S, Set.mem_setOf_eq, hres]
    rw [← hAeq]
    rfl
  have hflat : flatPoissonLaw ι S = flatPoissonLaw ι (completePast u ⁻¹' A') * ExponentialRace.clockLaw ι B := by
    have h := congrArg (fun ρ : Measure (FlatDriver ι × (ι → ℝ)) => ρ (A' ×ˢ B))
      (deterministic_past_wait_law (ι := ι) u)
    dsimp only at h
    rw [Measure.map_apply hpair (hA'.prod hB), Measure.prod_prod,
      Measure.map_apply (measurable_completePast u) hA'] at h
    exact h
  have hA2 : flatPoissonLaw ι (completePast u ⁻¹' A') = μ A := by
    unfold flatPoissonLaw
    rw [Measure.map_apply measurable_flatCellDriver
      ((measurable_completePast u) hA')]
    rw [← hAeq]
    rfl
  calc
    μ (A ∩ deterministicResidual u ⁻¹' B) = μ (flatCellDriver ⁻¹' S) := by rw [hset]
    _ = flatPoissonLaw ι S := by
      unfold flatPoissonLaw
      rw [Measure.map_apply measurable_flatCellDriver hSm]
    _ = μ A * ExponentialRace.clockLaw ι B := by rw [hflat, hA2]

end Bridge

/-! ### Rounded-residual convergence -/

section Convergence

open CellRandomTimeEvaluation CellStoppingLineFreshness CellStoppingLineResiduals

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem roundedResidualConvergence (σ : CellFamily ι → ι → ℝ≥0) :
    RoundedResidualConvergence σ := by
  refine Eventually.of_forall fun c => ?_
  rw [tendsto_pi_nhds]
  intro l
  let Y : ℝ≥0 → ℕ := fun s => cellPath (s : ℝ) (c l)
  have hmono : Monotone Y := fun s t h =>
    Ripple.Kurtz.StrongApprox.cellPath_mono (by exact_mod_cast h) (c l)
  have hright : ∀ s, ∀ᶠ r in 𝓝[≥] s, Y r = Y s := by
    intro s
    have hcont : Tendsto (fun r : ℝ≥0 => (r : ℝ)) (𝓝[≥] s) (𝓝[≥] (s : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact_mod_cast hr
    exact hcont.eventually
      (Ripple.Kurtz.StrongApprox.cellPath_eventually_right (s : ℝ) (c l))
  have hlim : Tendsto (fun m => (upperDyadicTime m (σ c l) : ℝ)) atTop
      (𝓝 ((σ c l : ℝ≥0) : ℝ)) :=
    (upperDyadicTime_tendsto_right (σ c l)).mono_right nhdsWithin_le_nhds
  have key := firstWait_shift_tendsto hmono hright (σ c l)
    (fun m => upperDyadicTime m (σ c l)) (fun m => le_upperDyadicTime m (σ c l)) hlim
  have hround : ∀ m, roundedResidual m σ c l =
      firstWait (fun s : ℝ≥0 => ((Y (upperDyadicTime m (σ c l) + s) -
        Y (upperDyadicTime m (σ c l)) : ℕ) : ℝ)) := by
    intro m
    unfold roundedResidual deterministicResidual residualVector
    rw [cell_residualWait_eq_firstWait]
    congr 1
  have hstop : stoppingResidual σ c l =
      firstWait (fun s : ℝ≥0 => ((Y (σ c l + s) - Y (σ c l) : ℕ) : ℝ)) := by
    unfold stoppingResidual residualVector
    rw [cell_residualWait_eq_firstWait]
    congr 1
  simp only [hround, hstop]
  exact key

end Convergence

/-! ### Final theorem with the adapters discharged -/

section Final

open CellStoppingLineFreshness CellStoppingLineResiduals

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- **Strong memorylessness at a cell stopping line.**  Only the stopping-line
property of `σ` and the measurability of the record prefix in the stopped past
remain as hypotheses. -/
theorem cellStoppingLine_freshResidualsAt_final
    {R : CellFamily ι → ℕ → ℝ × S} {k : ℕ}
    {σ : CellFamily ι → ι → ℝ≥0} (hσ : CellStoppingLine σ)
    (hHistory : Measurable[cellStoppedPast σ hσ] (recordPrefix R k)) :
    FreshResidualsAt (cellFamilyLaw ι) R (stoppingResidual σ) k :=
  cellStoppingLine_freshResidualsAt hσ hHistory deterministicResidualFresh
    (roundedResidualConvergence σ)

/-- A constant line is a stopping line (non-vacuity of the hypothesis). -/
theorem constantLine_isStoppingLine (u0 : ι → ℝ≥0) :
    CellStoppingLine (fun (_ : CellFamily ι) => u0) := by
  classical
  refine ⟨measurable_const, fun u => ?_⟩
  by_cases h : ∀ l, u0 l ≤ u l
  · have : lineBelow (fun (_ : CellFamily ι) => u0) u = Set.univ := by
      ext c; simp [lineBelow, h]
    rw [this]
    exact @MeasurableSet.univ _ (cellPast u)
  · have : lineBelow (fun (_ : CellFamily ι) => u0) u = ∅ := by
      ext c; simp [lineBelow, h]
    rw [this]
    exact @MeasurableSet.empty _ (cellPast u)

end Final

end Ripple.Kurtz.StrongApprox.CellStoppingLineAdapters

end

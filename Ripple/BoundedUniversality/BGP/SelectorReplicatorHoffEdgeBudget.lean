import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledResidual

/-!
# Hoff edge field-cap budget residual

The canonical `hoff` no-split surface uses actual left/right field caps.  For
proof development it is often cleaner to prove scalar upper bounds for those
two caps first, then compare the sum of those bounds and the middle envelope to
`selectorReplicatorHoldEnvelope`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance
open scoped BigOperators Topology

/-- Canonical full middle-window cap for the scalar `hoff` z-off envelope. -/
def selectorMUHoffMiddleEnvelopeFullCap (j : ℕ) : ℝ :=
  ∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j), selectorMUHoffMiddleEnvelope τ

private theorem selectorMUHoffMiddleEnvelope_eq_exp (τ : ℝ) :
    selectorMUHoffMiddleEnvelope τ = Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) * τ)) := by
  unfold selectorMUHoffMiddleEnvelope
  norm_num [bgpParams38]

private theorem bgpParams38_chiLeakRate_eq_200 :
    bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα = 200 := by
  norm_num [bgpParams38]

private theorem selectorMUZOffEnd_sub_start (j : ℕ) :
    selectorMUZOffEnd j - selectorMUZOffStart j = Real.pi := by
  unfold selectorMUZOffEnd selectorMUZOffStart
  ring

/-- The canonical full middle-window envelope is bounded by the exact exponential
tail coefficient `1 / 200` at its left endpoint. -/
theorem selectorMUHoffMiddleEnvelopeFullCap_le_one_div_200 (j : ℕ) :
    selectorMUHoffMiddleEnvelopeFullCap j ≤
      (1 / 200 : ℝ) *
        Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) *
        (2 * Real.pi * (j : ℝ) + Real.pi))) := by
  let a : ℝ := selectorMUZOffStart j
  let b : ℝ := selectorMUZOffEnd j
  let r : ℝ := bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα
  let F : ℝ → ℝ := fun τ => -Real.exp (-(r * τ)) / r
  have hr_eq : r = 200 := by
    norm_num [r, bgpParams38]
  have hr_pos : 0 < r := by
    simp [hr_eq]
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hderiv : deriv F = fun τ : ℝ => Real.exp (-(r * τ)) := by
    funext τ
    have harg : HasDerivAt (fun x : ℝ => -(r * x)) (-r) τ := by
      simpa using ((hasDerivAt_id τ).const_mul r).neg
    have hexp :
        HasDerivAt (fun x : ℝ => Real.exp (-(r * x)))
          (Real.exp (-(r * τ)) * (-r)) τ :=
      by
        simpa [Function.comp_def] using
          (Real.hasDerivAt_exp (-(r * τ))).comp τ harg
    have hF :
        HasDerivAt F (Real.exp (-(r * τ)) : ℝ) τ := by
      dsimp [F]
      convert hexp.neg.div_const r using 1
      field_simp [hr_ne]
    exact hF.deriv
  have hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ F x := by
    intro x _hx
    have harg : HasDerivAt (fun y : ℝ => -(r * y)) (-r) x := by
      simpa using ((hasDerivAt_id x).const_mul r).neg
    have hexp :
        HasDerivAt (fun y : ℝ => Real.exp (-(r * y)))
          (Real.exp (-(r * x)) * (-r)) x :=
      by
        simpa [Function.comp_def] using
          (Real.hasDerivAt_exp (-(r * x))).comp x harg
    simpa [F] using (hexp.neg.div_const r).differentiableAt
  have hcont : ContinuousOn (fun τ : ℝ => Real.exp (-(r * τ))) (uIcc a b) := by
    fun_prop
  have hint :
      (∫ τ in a..b, Real.exp (-(r * τ))) =
        F b - F a :=
    intervalIntegral.integral_deriv_eq_sub' F hderiv hdiff hcont
  have htail_nonneg : 0 ≤ Real.exp (-(r * b)) / r :=
    div_nonneg (Real.exp_pos _).le hr_pos.le
  have hbound :
      F b - F a ≤ (1 / 200 : ℝ) * Real.exp (-(r * a)) := by
    dsimp [F]
    rw [hr_eq]
    have htail_nonneg_200 : 0 ≤ Real.exp (-(200 * b)) / (200 : ℝ) := by
      positivity
    nlinarith
  calc
    selectorMUHoffMiddleEnvelopeFullCap j
        = ∫ τ in a..b, selectorMUHoffMiddleEnvelope τ := by
          simp [selectorMUHoffMiddleEnvelopeFullCap, a, b]
    _ = ∫ τ in a..b, Real.exp (-(r * τ)) := by
          simp [selectorMUHoffMiddleEnvelope_eq_exp, r]
    _ = F b - F a := hint
    _ ≤ (1 / 200 : ℝ) * Real.exp (-(r * a)) := hbound
    _ = (1 / 200 : ℝ) * Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) *
        (2 * Real.pi * (j : ℝ) + Real.pi))) := by
          simp [r, a, selectorMUZOffStart]

/-- Compatibility bound for older callers that budgeted the middle cap with the
coarser coefficient `8`. -/
theorem selectorMUHoffMiddleEnvelopeFullCap_le_eight (j : ℕ) :
    selectorMUHoffMiddleEnvelopeFullCap j ≤
      (8 : ℝ) * Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) *
        (2 * Real.pi * (j : ℝ) + Real.pi))) := by
  have hcap := selectorMUHoffMiddleEnvelopeFullCap_le_one_div_200 j
  have hE :
      0 ≤ Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) *
        (2 * Real.pi * (j : ℝ) + Real.pi))) :=
    (Real.exp_pos _).le
  exact hcap.trans
    (mul_le_mul_of_nonneg_right (by norm_num : (1 / 200 : ℝ) ≤ 8) hE)

theorem selectorMUHoffMiddleEnvelopeFullCap_nonneg (j : ℕ) :
    0 ≤ selectorMUHoffMiddleEnvelopeFullCap j := by
  unfold selectorMUHoffMiddleEnvelopeFullCap
  apply intervalIntegral.integral_nonneg (selectorMUZOffStart_le_zOffEnd j)
  intro τ _hτ
  rw [selectorMUHoffMiddleEnvelope_eq_exp]
  exact (Real.exp_pos _).le

/-- Scalar reserve left for the Hoff left/right edge caps after the canonical
middle interval consumes `(1 / 200) * exp(-rate * t)` from the hold envelope. -/
def selectorMUHoffEdgeBudgetCoeff : ℝ :=
  selectorReplicatorHoldEnvelopeCoeff - (1 / 200 : ℝ)

theorem selectorMUHoffEdgeBudgetCoeff_nonneg :
    0 ≤ selectorMUHoffEdgeBudgetCoeff := by
  unfold selectorMUHoffEdgeBudgetCoeff
  linarith [selectorReplicatorHoldEnvelopeCoeff_ge_eight]

/-- Remaining scalar edge budget after the canonical middle cap. -/
def selectorMUHoffEdgeBudget (j : ℕ) : ℝ :=
  selectorMUHoffEdgeBudgetCoeff *
    Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) * (2 * Real.pi * (j : ℝ) + Real.pi)))

theorem selectorMUHoffMiddleEnvelopeFullCap_le_holdEnvelope (j : ℕ) :
    selectorMUHoffMiddleEnvelopeFullCap j ≤ selectorReplicatorHoldEnvelope j := by
  let T : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi
  let E : ℝ := Real.exp (-(200 * T))
  have hE_eq :
      E = Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L -
        bgpParams38.cα) * T)) := by
    dsimp [E]
    rw [bgpParams38_chiLeakRate_eq_200]
  have hcap : selectorMUHoffMiddleEnvelopeFullCap j ≤ (1 / 200 : ℝ) * E := by
    simpa [T, hE_eq] using selectorMUHoffMiddleEnvelopeFullCap_le_one_div_200 j
  have hcoeff : (1 / 200 : ℝ) ≤ selectorReplicatorHoldEnvelopeCoeff := by
    exact le_trans (by norm_num : (1 / 200 : ℝ) ≤ 8)
      selectorReplicatorHoldEnvelopeCoeff_ge_eight
  have hE : 0 ≤ E := (Real.exp_pos _).le
  calc selectorMUHoffMiddleEnvelopeFullCap j
      ≤ (1 / 200 : ℝ) * E := hcap
    _ ≤ selectorReplicatorHoldEnvelopeCoeff * E :=
        mul_le_mul_of_nonneg_right hcoeff hE
    _ = selectorReplicatorHoldEnvelope j := by
      simp [selectorReplicatorHoldEnvelope, T, hE_eq]

/-- After reserving the canonical middle cap, the coarse scalar edge budget
still fits inside the hold envelope. -/
theorem selectorMUHoffMiddleEnvelopeFullCap_add_edgeBudget_le_holdEnvelope (j : ℕ) :
    selectorMUHoffMiddleEnvelopeFullCap j + selectorMUHoffEdgeBudget j ≤
      selectorReplicatorHoldEnvelope j := by
  let T : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi
  let E : ℝ := Real.exp (-(200 * T))
  have hE_eq :
      E = Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L -
        bgpParams38.cα) * T)) := by
    dsimp [E]
    rw [bgpParams38_chiLeakRate_eq_200]
  have hcap : selectorMUHoffMiddleEnvelopeFullCap j ≤ (1 / 200 : ℝ) * E := by
    simpa [T, hE_eq] using selectorMUHoffMiddleEnvelopeFullCap_le_one_div_200 j
  have hbudget :
      selectorMUHoffEdgeBudget j = selectorMUHoffEdgeBudgetCoeff * E := by
    simp [selectorMUHoffEdgeBudget, T, hE_eq]
  calc
    selectorMUHoffMiddleEnvelopeFullCap j + selectorMUHoffEdgeBudget j
        = selectorMUHoffMiddleEnvelopeFullCap j +
            selectorMUHoffEdgeBudgetCoeff * E := by rw [hbudget]
    _ ≤ (1 / 200 : ℝ) * E + selectorMUHoffEdgeBudgetCoeff * E := by
          exact add_le_add hcap le_rfl
    _ = selectorReplicatorHoldEnvelopeCoeff * E := by
          unfold selectorMUHoffEdgeBudgetCoeff
          ring
    _ = selectorReplicatorHoldEnvelope j := by
      simp [selectorReplicatorHoldEnvelope, T, hE_eq]

/-- Compatibility alias for older callers.  The reserve is no longer the fixed
numeric `3992`; it is the current envelope coefficient minus the middle cap. -/
def selectorMUHoffEdgeBudget3992 (j : ℕ) : ℝ :=
  selectorMUHoffEdgeBudget j

theorem selectorMUHoffCapLeftField_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w j : ℕ) :
    0 ≤ selectorMUHoffCapLeftField sol w j := by
  unfold selectorMUHoffCapLeftField
  apply intervalIntegral.integral_nonneg (selectorMUInterReadStart_le_zOffStart j)
  intro τ _hτ
  exact abs_nonneg _

theorem selectorMUHoffCapRightField_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w j : ℕ) :
    0 ≤ selectorMUHoffCapRightField sol w j := by
  unfold selectorMUHoffCapRightField
  apply intervalIntegral.integral_nonneg (selectorMUZOffEnd_le_nextWriteStart j)
  intro τ _hτ
  exact abs_nonneg _

theorem selectorMUHoffCapLeftField_le_gate_full
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) (w j : ℕ) :
    selectorMUHoffCapLeftField sol w j ≤
      ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
        selectorMUHoffGateCoeff sol w τ := by
  let gateCap : ℕ → ℕ → ℝ := fun w j =>
    ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
      selectorMUHoffGateCoeff sol w τ
  have hgateLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j)
      (selectorMUZOffStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffGateCoeff sol w τ) ≤ gateCap w j := by
    intro w j t ht
    let f : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
    have hf_cont : Continuous f := by
      simpa [f, selectorMUHoffGateCoeff] using
        selector_replicator_gateZ_integrand_continuous (sol w)
    have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
      fun x y => hf_cont.intervalIntegrable x y
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hI (selectorMUInterReadStart j) t)
      (hI t (selectorMUZOffStart j))
    have htail_nonneg : 0 ≤ ∫ τ in t..selectorMUZOffStart j, f τ := by
      apply intervalIntegral.integral_nonneg ht.2
      intro τ hτ
      have ha0 : 0 ≤ selectorMUInterReadStart j := by
        unfold selectorMUInterReadStart selectorMUWriteReadTime
        positivity
      have hτ0 : 0 ≤ τ := le_trans ha0 (le_trans ht.1 hτ.1)
      simpa [f, selectorMUHoffGateCoeff] using
        selector_replicator_gateZ_integrand_nonneg (sol w)
          selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
    change (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤ gateCap w j
    dsimp [gateCap]
    change (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤
      ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ
    linarith
  have hfield :=
    selectorMUHoff_hcapLeft_of_gate boxInputs (capLeft := gateCap) hgateLeft
      w j (selectorMUZOffStart j)
      ⟨selectorMUInterReadStart_le_zOffStart j, le_rfl⟩
  simpa [gateCap, selectorMUHoffCapLeftField] using hfield

theorem selectorMUHoffCapRightField_le_gate_full
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) (henc_const : selectorMUHaltEncConstW solMUReplStaticCfg w j) :
    selectorMUHoffCapRightField sol w j ≤
      ∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ := by
  let gateCap : ℕ → ℕ → ℝ := fun w j =>
    ∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
      selectorMUHoffGateCoeff sol w τ
  have hgateRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUZOffEnd j)..t,
        selectorMUHoffGateCoeff sol w τ) ≤ gateCap w j := by
    intro w j _henc t ht
    let f : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
    have hf_cont : Continuous f := by
      simpa [f, selectorMUHoffGateCoeff] using
        selector_replicator_gateZ_integrand_continuous (sol w)
    have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
      fun x y => hf_cont.intervalIntegrable x y
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hI (selectorMUZOffEnd j) t)
      (hI t (selectorMUNextWriteStart j))
    have htail_nonneg : 0 ≤ ∫ τ in t..selectorMUNextWriteStart j, f τ := by
      apply intervalIntegral.integral_nonneg ht.2
      intro τ hτ
      have ha0 : 0 ≤ selectorMUZOffEnd j := by
        unfold selectorMUZOffEnd
        positivity
      have hτ0 : 0 ≤ τ := le_trans ha0 (le_trans ht.1 hτ.1)
      simpa [f, selectorMUHoffGateCoeff] using
        selector_replicator_gateZ_integrand_nonneg (sol w)
          selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
    change (∫ τ in (selectorMUZOffEnd j)..t, f τ) ≤ gateCap w j
    dsimp [gateCap]
    change (∫ τ in (selectorMUZOffEnd j)..t, f τ) ≤
      ∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j), f τ
    linarith
  have hfield :=
    selectorMUHoff_hcapRight_of_gate boxInputs (capRight := gateCap) hgateRight
      w j henc_const (selectorMUNextWriteStart j)
      ⟨selectorMUZOffEnd_le_nextWriteStart j, le_rfl⟩
  simpa [gateCap, selectorMUHoffCapRightField] using hfield

/-- Pure scalar reduction: once the two actual edge caps fit in the `3992E`
reserve, the canonical middle cap and edge reserve fit in the hold envelope. -/
theorem selectorMUHoff_actual_cap_sum_le_holdEnvelope_of_edges_le_3992
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w j : ℕ)
    (hedge :
      selectorMUHoffCapLeftField sol w j +
        selectorMUHoffCapRightField sol w j ≤
          selectorMUHoffEdgeBudget3992 j) :
    selectorMUHoffCapLeftField sol w j +
      selectorMUHoffMiddleEnvelopeFullCap j +
      selectorMUHoffCapRightField sol w j ≤
        selectorReplicatorHoldEnvelope j := by
  calc
    selectorMUHoffCapLeftField sol w j + selectorMUHoffMiddleEnvelopeFullCap j +
        selectorMUHoffCapRightField sol w j
        = selectorMUHoffMiddleEnvelopeFullCap j +
            (selectorMUHoffCapLeftField sol w j +
              selectorMUHoffCapRightField sol w j) := by ring
    _ ≤ selectorMUHoffMiddleEnvelopeFullCap j + selectorMUHoffEdgeBudget3992 j :=
      add_le_add le_rfl hedge
    _ ≤ selectorReplicatorHoldEnvelope j := by
      simpa [selectorMUHoffEdgeBudget3992] using
        selectorMUHoffMiddleEnvelopeFullCap_add_edgeBudget_le_holdEnvelope j

/-- Existing gate-full estimates combine to a two-edge gate upper bound.  This
adapter is intentionally coarse; the active right interval still needs a real
scalar estimate before it can close the exact Hoff budget. -/
theorem selectorMUHoffCapEdges_le_gate_full_sum
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ)
    (henc : selectorMUHaltEncConstW solMUReplStaticCfg w j) :
    selectorMUHoffCapLeftField sol w j +
      selectorMUHoffCapRightField sol w j ≤
        (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          selectorMUHoffGateCoeff sol w τ) +
        (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
          selectorMUHoffGateCoeff sol w τ) := by
  have hleft := selectorMUHoffCapLeftField_le_gate_full
    (sol := sol) boxInputs w j
  have hright := selectorMUHoffCapRightField_le_gate_full
    (sol := sol) boxInputs w j henc
  linarith

theorem selectorMUHoffCapRightPrefix_le_initial_add_target
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (s M : ℝ)
    (hs : selectorMUZOffEnd j ≤ s) :
    (∫ τ in (selectorMUZOffEnd j)..s,
      selectorMUHoffIntegrand sol w τ) ≤
      |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
        2 * (∫ τ in (selectorMUZOffEnd j)..s,
          selectorMUHoffGateCoeff sol w τ *
            |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) := by
  let a : ℝ := selectorMUZOffEnd j
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  have hab : a ≤ s := by simpa [a] using hs
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous m := by
    simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by
    simpa [y] using (sol w).cont_z haltCoordU
  have hk_nonneg : ∀ τ ∈ Set.Icc a s, 0 ≤ k τ := by
    intro τ hτ
    have ha0 : 0 ≤ a := by
      simp [a, selectorMUZOffEnd]
      positivity
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hy_ode : ∀ τ ∈ Set.Icc a s,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have ha0 : 0 ≤ a := by
      simp [a, selectorMUZOffEnd]
      positivity
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeff] using
      (sol w).z_hasDeriv τ (selectorSchedule_domain_of_nonneg_structural τ hτ0) haltCoordU
  have herrorInt :
      (∫ τ in a..s, k τ * |y τ - M|) ≤
        |y a - M| + (∫ τ in a..s, k τ * |m τ - M|) := by
    exact stack_write_error_integral_le_initial_add_target
      y m k M a s hab hk_cont hk_nonneg hy_cont hm_cont hy_ode
  have hfield :
      (∫ τ in a..s, k τ * |m τ - y τ|) ≤
        |y a - M| + 2 * (∫ τ in a..s, k τ * |m τ - M|) :=
    stack_write_field_cap_bound_of_error_integral
      y m k M a s hab hk_cont hk_nonneg hy_cont hm_cont herrorInt
  have hcap_le :
      (∫ τ in a..s, selectorMUHoffIntegrand sol w τ) ≤
        ∫ τ in a..s, k τ * |m τ - y τ| := by
    have hleft_int : IntervalIntegrable
        (fun τ => selectorMUHoffIntegrand sol w τ) MeasureTheory.volume a s := by
      exact (selectorMUHoffIntegrand_continuous (sol := sol) w).intervalIntegrable a s
    have hright_int : IntervalIntegrable (fun τ => k τ * |m τ - y τ|)
        MeasureTheory.volume a s := by
      exact (hk_cont.mul ((hm_cont.sub hy_cont).abs)).intervalIntegrable a s
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro τ hτ
    have hk0 : 0 ≤ k τ := hk_nonneg τ hτ
    calc
      selectorMUHoffIntegrand sol w τ
          = |k τ * (m τ - y τ)| := by
            simp [selectorMUHoffIntegrand, selectorMUHoffGateCoeff, k, m, y]
      _ = k τ * |m τ - y τ| := by
            rw [abs_mul, abs_of_nonneg hk0]
      _ ≤ k τ * |m τ - y τ| := le_rfl
  exact le_trans hcap_le (by simpa [a, y, m, k] using hfield)

/-- If a genuine scalar estimate puts the two edge gate integrals within the
`3992E` reserve, then the canonical actual-cap sum follows. -/
theorem selectorMUHoff_actual_cap_sum_le_holdEnvelope_of_gate_edges_le_3992
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ)
    (henc : selectorMUHaltEncConstW solMUReplStaticCfg w j)
    (hgate :
      (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          selectorMUHoffGateCoeff sol w τ) +
        (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
          selectorMUHoffGateCoeff sol w τ) ≤
          selectorMUHoffEdgeBudget3992 j) :
    selectorMUHoffCapLeftField sol w j +
      selectorMUHoffMiddleEnvelopeFullCap j +
      selectorMUHoffCapRightField sol w j ≤
        selectorReplicatorHoldEnvelope j := by
  refine selectorMUHoff_actual_cap_sum_le_holdEnvelope_of_edges_le_3992
    (sol := sol) w j ?_
  exact le_trans
    (selectorMUHoffCapEdges_le_gate_full_sum
      (sol := sol) boxInputs w j henc)
    hgate

/-- Exact additive split of the actual right Hoff cap.  Splitting at
`selectorMUSelectStartTime (j + 1)` isolates the current pre-floor obstruction. -/
theorem selectorMUHoffCapRightField_split_at
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (s : ℝ) :
    selectorMUHoffCapRightField sol w j =
      (∫ τ in (selectorMUZOffEnd j)..s,
        selectorMUHoffIntegrand sol w τ) +
      (∫ τ in s..(selectorMUNextWriteStart j),
        selectorMUHoffIntegrand sol w τ) := by
  let f : ℝ → ℝ := fun τ => selectorMUHoffIntegrand sol w τ
  have hf_cont : Continuous f := by
    simpa [f] using selectorMUHoffIntegrand_continuous (sol := sol) w
  have hI : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => hf_cont.intervalIntegrable a b
  unfold selectorMUHoffCapRightField
  simpa [f] using
    (intervalIntegral.integral_add_adjacent_intervals
      (hI (selectorMUZOffEnd j) s)
      (hI s (selectorMUNextWriteStart j))).symm

/-- Bound the right actual cap from separate early/late estimates after a split. -/
theorem selectorMUHoffCapRightField_le_of_split_bounds
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (s A B : ℝ)
    (hearly :
      (∫ τ in (selectorMUZOffEnd j)..s,
        selectorMUHoffIntegrand sol w τ) ≤ A)
    (hlate :
      (∫ τ in s..(selectorMUNextWriteStart j),
        selectorMUHoffIntegrand sol w τ) ≤ B) :
    selectorMUHoffCapRightField sol w j ≤ A + B := by
  rw [selectorMUHoffCapRightField_split_at (sol := sol) w j s]
  exact add_le_add hearly hlate

theorem selectorMUHoffCapRightField_le_of_prewrite_source_and_late_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (s M A B : ℝ)
    (hs : selectorMUZOffEnd j ≤ s)
    (hpre :
      |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
        2 * (∫ τ in (selectorMUZOffEnd j)..s,
          selectorMUHoffGateCoeff sol w τ *
            |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) ≤ A)
    (hlate :
      (∫ τ in s..(selectorMUNextWriteStart j),
        selectorMUHoffIntegrand sol w τ) ≤ B) :
    selectorMUHoffCapRightField sol w j ≤ A + B := by
  have hearly :=
    (selectorMUHoffCapRightPrefix_le_initial_add_target
      (sol := sol) w j s M hs).trans hpre
  exact selectorMUHoffCapRightField_le_of_split_bounds
    (sol := sol) w j s A B hearly hlate

/-- Bound the full right actual cap from a source estimate on the prefix
`[ZOffEnd, s]` and a target-mix estimate on the suffix `[s, NextWriteStart]`.

This keeps the ODE field-cap argument global, so the suffix does not need a
separate bound on the intermediate endpoint `z s`. -/
theorem selectorMUHoffCapRightField_le_of_prewrite_source_and_target_late_bound
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (s M A B : ℝ)
    (hpre :
      |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
        2 * (∫ τ in (selectorMUZOffEnd j)..s,
          selectorMUHoffGateCoeff sol w τ *
            |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) ≤ A)
    (hlate :
      (∫ τ in s..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) ≤ B) :
    selectorMUHoffCapRightField sol w j ≤ A + 2 * B := by
  let Z : ℝ := selectorMUZOffEnd j
  let N : ℝ := selectorMUNextWriteStart j
  let f : ℝ → ℝ := fun τ =>
    selectorMUHoffGateCoeff sol w τ *
      |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|
  have hcap := selectorMUHoffCapRightField_le_initial_add_target
    (sol := sol) w j M
  have hf_cont : Continuous f := by
    dsimp [f]
    exact (selector_replicator_gateZ_integrand_continuous (sol w)).mul
      (((sol w).cont_mixTarget haltCoordU).sub continuous_const).abs
  have hI : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => hf_cont.intervalIntegrable a b
  have hsplit :
      (∫ τ in Z..N, f τ) = (∫ τ in Z..s, f τ) + (∫ τ in s..N, f τ) :=
    (intervalIntegral.integral_add_adjacent_intervals (hI Z s) (hI s N)).symm
  have hmain :
      |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          2 * (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
            selectorMUHoffGateCoeff sol w τ *
              |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|)
        ≤ A + 2 * B := by
    have hsplit' :
        (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
          selectorMUHoffGateCoeff sol w τ *
            |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|)
          =
        (∫ τ in (selectorMUZOffEnd j)..s,
          selectorMUHoffGateCoeff sol w τ *
            |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) +
        (∫ τ in s..(selectorMUNextWriteStart j),
          selectorMUHoffGateCoeff sol w τ *
            |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) := by
      simpa [Z, N, f] using hsplit
    rw [hsplit']
    nlinarith [hpre, hlate]
  exact le_trans hcap hmain

/-- The full middle-window integral canonically bounds every partial middle
integral because the envelope is nonnegative. -/
def selectorMUHoffMiddleEnvelopeFullResidual :
    SelectorMUHoffMiddleEnvelopeResidual where
  capMid := fun _w j => selectorMUHoffMiddleEnvelopeFullCap j
  henvInt := by
    intro _w j t ht
    have hcont : Continuous selectorMUHoffMiddleEnvelope := by
      unfold selectorMUHoffMiddleEnvelope
      fun_prop
    unfold selectorMUHoffMiddleEnvelopeFullCap
    apply intervalIntegral.integral_mono_interval
    · exact le_rfl
    · exact ht.1
    · exact ht.2
    · exact Filter.Eventually.of_forall fun τ => by
        have hA : 0 ≤ bgpParams38.A := by norm_num [bgpParams38]
        unfold selectorMUHoffMiddleEnvelope
        exact mul_nonneg hA (Real.exp_pos _).le
    · exact hcont.intervalIntegrable _ _

theorem selectorMUHoffMiddleFieldPrefix_le_fullCap
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) :
    ∀ t ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (∫ τ in (selectorMUZOffStart j)..t,
        selectorMUHoffIntegrand sol w τ) ≤
        selectorMUHoffMiddleEnvelopeFullCap j := by
  intro t ht
  have hmid := selectorMUHoff_middle_offphase_of_envelope
    (sol := sol) boxInputs selectorMUHoffMiddleEnvelopeFullResidual
    w j t ht
  simpa [selectorMUHoffMiddleEnvelopeFullResidual] using hmid

theorem selectorMUHoffFieldIntegral_interRead_to_zOffEnd_le_left_middle
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) :
    ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffEnd j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffIntegrand sol w τ) ≤
        selectorMUHoffCapLeftField sol w j +
          selectorMUHoffMiddleEnvelopeFullCap j := by
  intro t ht
  let f : ℝ → ℝ := fun τ => selectorMUHoffIntegrand sol w τ
  have hf_cont : Continuous f := by
    simpa [f] using selectorMUHoffIntegrand_continuous (sol := sol) w
  have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  change (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤
    selectorMUHoffCapLeftField sol w j +
      selectorMUHoffMiddleEnvelopeFullCap j
  by_cases ht_left : t ≤ selectorMUZOffStart j
  · have htail_nonneg : 0 ≤
        ∫ τ in t..(selectorMUZOffStart j), f τ := by
      apply intervalIntegral.integral_nonneg ht_left
      intro τ _hτ
      exact abs_nonneg _
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hI (selectorMUInterReadStart j) t)
      (hI t (selectorMUZOffStart j))
    have hprefix :
        (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤
          selectorMUHoffCapLeftField sol w j := by
      calc
        (∫ τ in (selectorMUInterReadStart j)..t, f τ)
            ≤ ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ := by
              linarith
        _ = selectorMUHoffCapLeftField sol w j := by
              simp [selectorMUHoffCapLeftField, f]
    have hmid_nonneg := selectorMUHoffMiddleEnvelopeFullCap_nonneg j
    linarith
  · have hstart_t : selectorMUZOffStart j ≤ t := le_of_not_ge ht_left
    have hleft_full :
        (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) ≤
          selectorMUHoffCapLeftField sol w j := by
      simp [selectorMUHoffCapLeftField, f]
    have hmid :=
      selectorMUHoffMiddleFieldPrefix_le_fullCap
        (sol := sol) boxInputs w j t ⟨hstart_t, ht.2⟩
    have hmid' :
        (∫ τ in (selectorMUZOffStart j)..t, f τ) ≤
          selectorMUHoffMiddleEnvelopeFullCap j := by
      simpa [f] using hmid
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hI (selectorMUInterReadStart j) (selectorMUZOffStart j))
      (hI (selectorMUZOffStart j) t)
    calc
      (∫ τ in (selectorMUInterReadStart j)..t, f τ)
          = (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) +
            (∫ τ in (selectorMUZOffStart j)..t, f τ) := by
              exact hadd.symm
      _ ≤ selectorMUHoffCapLeftField sol w j +
            selectorMUHoffMiddleEnvelopeFullCap j :=
          add_le_add hleft_full hmid'

theorem selectorMUHoff_drift_interRead_to_zOffEnd_le_left_middle
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) :
    |(sol w).z (selectorMUZOffEnd j) haltCoordU -
      (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorMUHoffCapLeftField sol w j +
          selectorMUHoffMiddleEnvelopeFullCap j := by
  have hIE : selectorMUInterReadStart j ≤ selectorMUZOffEnd j :=
    le_trans (selectorMUInterReadStart_le_zOffStart j)
      (selectorMUZOffStart_le_zOffEnd j)
  have ha0 : 0 ≤ selectorMUInterReadStart j := by
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  have hdom : ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffEnd j),
      t ∈ selectorSchedule.domain := by
    intro t ht
    exact selectorSchedule_domain_of_nonneg_structural t (le_trans ha0 ht.1)
  have hfieldInt : ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffEnd j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        |bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ *
          (selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
            (sol w).z τ haltCoordU)|) ≤
        selectorMUHoffCapLeftField sol w j +
          selectorMUHoffMiddleEnvelopeFullCap j := by
    intro t ht
    have h := selectorMUHoffFieldIntegral_interRead_to_zOffEnd_le_left_middle
      (sol := sol) boxInputs w j t ht
    simpa [selectorMUHoffIntegrand] using h
  have h := flag_drift_bound_on_interval_repl (sol w) haltCoordU
    hIE hdom (selector_replicator_gateZ_integrand_continuous (sol w))
    hfieldInt (selectorMUZOffEnd j) ⟨hIE, le_rfl⟩
  simpa using h

theorem selectorMUHoff_zOffEnd_error_le_interRead_error_add_left_middle
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) (M : ℝ) :
    |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| ≤
      |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
        selectorMUHoffCapLeftField sol w j +
          selectorMUHoffMiddleEnvelopeFullCap j := by
  have hdrift :=
    selectorMUHoff_drift_interRead_to_zOffEnd_le_left_middle
      (sol := sol) boxInputs w j
  have htri :
      |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| ≤
        |(sol w).z (selectorMUZOffEnd j) haltCoordU -
          (sol w).z (selectorMUInterReadStart j) haltCoordU| +
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| := by
    have hsum :
        (sol w).z (selectorMUZOffEnd j) haltCoordU - M =
          ((sol w).z (selectorMUZOffEnd j) haltCoordU -
            (sol w).z (selectorMUInterReadStart j) haltCoordU) +
          ((sol w).z (selectorMUInterReadStart j) haltCoordU - M) := by
      ring
    rw [hsum]
    exact abs_add_le _ _
  calc
    |(sol w).z (selectorMUZOffEnd j) haltCoordU - M|
        ≤ |(sol w).z (selectorMUZOffEnd j) haltCoordU -
            (sol w).z (selectorMUInterReadStart j) haltCoordU| +
          |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| := htri
    _ ≤ (selectorMUHoffCapLeftField sol w j +
            selectorMUHoffMiddleEnvelopeFullCap j) +
          |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| :=
        add_le_add hdrift le_rfl
    _ = |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          selectorMUHoffCapLeftField sol w j +
            selectorMUHoffMiddleEnvelopeFullCap j := by
      ring

/-- Modular budget residual for the two `hoff` edge field caps plus the middle
z-off envelope. -/
structure SelectorMUHoffEdgeFieldCapBudgetResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  env : SelectorMUHoffMiddleEnvelopeResidual
  capLeftBound : ℕ → ℕ → ℝ
  capRightBound : ℕ → ℕ → ℝ
  hcapLeftField : ∀ w j,
    selectorMUHoffCapLeftField sol w j ≤ capLeftBound w j
  hcapRightField : ∀ w j,
    selectorMUHoffCapRightField sol w j ≤ capRightBound w j
  hsum_le : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
    capLeftBound w j + env.capMid w j + capRightBound w j ≤
      selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffEdgeFieldCapBudgetResidual

/-- Convert edge-cap scalar bounds to the canonical actual-field-cap no-split
`hoff` residual. -/
def toFieldCapNoSplit
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (R : SelectorMUHoffEdgeFieldCapBudgetResidual sol) :
    SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual sol where
  env := R.env
  hsum_le := by
    intro w j henc_const
    have hL := R.hcapLeftField w j
    have hR := R.hcapRightField w j
    have hsum := R.hsum_le w j henc_const
    linarith

end SelectorMUHoffEdgeFieldCapBudgetResidual

/-- Edge field-cap budget with the middle cap fixed to the canonical full
middle-window envelope integral. -/
structure SelectorMUHoffCanonicalEdgeFieldCapBudgetResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  capLeftBound : ℕ → ℕ → ℝ
  capRightBound : ℕ → ℕ → ℝ
  hcapLeftField : ∀ w j,
    selectorMUHoffCapLeftField sol w j ≤ capLeftBound w j
  hcapRightField : ∀ w j,
    selectorMUHoffCapRightField sol w j ≤ capRightBound w j
  hsum_le : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
    capLeftBound w j + selectorMUHoffMiddleEnvelopeFullCap j + capRightBound w j ≤
      selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffCanonicalEdgeFieldCapBudgetResidual

/-- Build the canonical edge-budget residual from the single actual-field cap
sum. -/
def of_actual_cap_sum
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (hsum : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
      selectorMUHoffCapLeftField sol w j + selectorMUHoffMiddleEnvelopeFullCap j +
        selectorMUHoffCapRightField sol w j ≤ selectorReplicatorHoldEnvelope j) :
    SelectorMUHoffCanonicalEdgeFieldCapBudgetResidual sol where
  capLeftBound := fun w j => selectorMUHoffCapLeftField sol w j
  capRightBound := fun w j => selectorMUHoffCapRightField sol w j
  hcapLeftField := by
    intro _w _j
    exact le_rfl
  hcapRightField := by
    intro _w _j
    exact le_rfl
  hsum_le := hsum

/-- Project the canonical-middle edge budget to the general edge-budget surface. -/
def toEdgeFieldCapBudgetResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (R : SelectorMUHoffCanonicalEdgeFieldCapBudgetResidual sol) :
    SelectorMUHoffEdgeFieldCapBudgetResidual sol where
  env := selectorMUHoffMiddleEnvelopeFullResidual
  capLeftBound := R.capLeftBound
  capRightBound := R.capRightBound
  hcapLeftField := R.hcapLeftField
  hcapRightField := R.hcapRightField
  hsum_le := by
    intro w j henc_const
    simpa [selectorMUHoffMiddleEnvelopeFullResidual] using R.hsum_le w j henc_const

/-- Convert directly to the canonical actual-field-cap no-split `hoff` residual. -/
def toFieldCapNoSplit
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (R : SelectorMUHoffCanonicalEdgeFieldCapBudgetResidual sol) :
    SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual sol :=
  R.toEdgeFieldCapBudgetResidual.toFieldCapNoSplit

end SelectorMUHoffCanonicalEdgeFieldCapBudgetResidual

end Ripple.BoundedUniversality.BGP

import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledFinal
import Ripple.BoundedUniversality.BGP.SelectorReplicatorStatic
import Ripple.BoundedUniversality.BGP.SelectorReplicatorConcSchedule
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledZ
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
# MUReplicatorSettledConstruction

Parametric construction of `MUReplicatorSettledFacts` from the concrete
solution family `solMURepl`.

Tracking radii (ρu, Bzu, Bz, δnext, holdPrefix) are carried as parameters,
matching the selector architecture.  The construction has 0 `sorry`
(hKreset, hloser, hδw_nonneg) and 0 zero-radius bugs.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine Filter Set
open scoped Topology

/-- **Parametric construction of the halt-coordinate settled facts.**

This is the shape-correct construction consumed by
`bgp_MU_replicator_settled`: it carries the λ-concentration, z-write, and
self-hold premises needed at `haltCoordU`, but does not require settled
u-tubes, z-u tubes, or non-halt branch-spread bounds.
-/
def muReplicatorSettledHaltFacts_param
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j)) t)
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t))
    (Bz : ℕ → ℕ → ℝ) (Bzmax : ℝ)
    (δnext : ℕ → ℕ → ℝ) (holdPrefix : ℕ → ℕ → ℝ)
    (hBz_nonneg : ∀ w j, 0 ≤ Bz w j)
    (hBz_bdd : ∀ w, ∀ᶠ j in atTop, Bz w j ≤ Bzmax)
    (hδnext : ∀ w, Tendsto (δnext w) atTop (𝓝 0))
    (hδnext_nonneg : ∀ w j, 0 ≤ δnext w j)
    (hholdPrefix_nonneg : ∀ w j, 0 ≤ holdPrefix w j)
    (p_hz_start : ∀ w j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz w j)
    (p_hoff : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
        Icc (selectorMUInterReadStart j)
        (selectorMUNextWriteStart j),
      |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j)
    (p_hnextWrite : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤ δnext w j)
    (p_hfiniteHold : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j)
        (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ holdPrefix w j)
    (p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
          epsLamSettled (V := UniversalLocalView)
            (1 / (Fintype.card UniversalLocalView : ℝ))
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ)
            (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
              Real.exp ((selectorReplicatorGapVal eta heta) *
                ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
                (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)))
            (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)) :
    MUReplicatorSettledHaltFacts sol := by
  exact
  { cfg := solMUReplStaticCfg
    hcfg := solMUReplStaticCfg_eq
    hcfg_step := solMUReplStaticCfg_step
    inputs :=
      { Lmin := fun _ _ => 1 / (Fintype.card UniversalLocalView : ℝ)
        gap := fun _ _ => selectorReplicatorGapVal eta heta
        R0 := fun _ _ => (Fintype.card UniversalLocalView : ℝ)
        Kreset := fun w j =>
          ∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
            Real.exp ((selectorReplicatorGapVal eta heta) *
              ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
              (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
        hLmin_pos := fun _ _ => solMURepl_concLmin_floor
        hqL := hqL_full
        hgap := selector_replicator_hgap_of_utube herr hutube_win
        hRa := fun w j v hv =>
          solMURepl_concR0_card_bound boxInputs w j
            (hqL_full w j _ ⟨le_refl _, selectorMUWriteStart_le_read j⟩) v hv
        hKreset := fun _ _ => le_refl _
      }
    Λ := fun _w j => selectorSettledWriteIntLower j
    Bz := Bz
    δnext := δnext
    holdPrefix := holdPrefix
    Bzmax := Bzmax
    R0max := Fintype.card UniversalLocalView
    hg₀ := solMURepl_static_hg0 hg₀
    hgap0 := solMURepl_static_hgap0 eta heta herr
    hgap_lb := by
      intro w; filter_upwards [] with j; exact le_refl _
    hLmin_lb := by
      intro w; filter_upwards [] with j; exact le_refl _
    hR0_nonneg := by
      intro w; filter_upwards [] with j; positivity
    hR0_bound := by
      intro w; filter_upwards [] with j; exact le_refl _
    hKreset_eq := fun _ _ => rfl
    hκ₀_nonneg := solMURepl_static_hkappa_nonneg hκ₀_nonneg
    hCratio_nonneg := solMURepl_static_hCratio_nonneg
    hratio_bound := solMURepl_static_hratio_bound hκ₀_nonneg hg₀.le hscale
    hdom_write := solMURepl_static_hdom_write
    hgZ_cont := solMURepl_static_hgZ_cont sol
    hgZ0 := solMURepl_static_hgZ0 sol
    hsum := solMURepl_static_hsum boxInputs
    hlam_nonneg := solMURepl_static_hlam_nonneg boxInputs
    hloser := by
      intro w j t ht
      simpa [solMUReplSettledHaltEpsLam] using p_hloser w j t ht
    hz_start := p_hz_start
    hΛ_lower := by
      intro w j
      have hdom_nonneg := solMURepl_static_hdom_nonneg
      have hgZ_cont := solMURepl_static_hgZ_cont sol w
      have hgZ0 := solMURepl_static_hgZ0 sol
      have hsub := selector_settled_writeIntegral_lower_lbd_repl (sol w) j
        hdom_nonneg hgZ_cont
      have hcont_int : ∀ a b : ℝ,
          IntervalIntegrable
            (fun t : ℝ => bgpParams38.A * (sol w).α t *
              bGateZ bgpParams38.L ((sol w).μ t) t)
            MeasureTheory.volume a b :=
        fun a b => hgZ_cont.intervalIntegrable a b
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hcont_int (selectorMUWriteHoldTime j) (selectorMUSettledWriteSubEnd j))
        (hcont_int (selectorMUSettledWriteSubEnd j) (selectorMUWriteReadTime j))
      have htail_nonneg :
          0 ≤ ∫ t in selectorMUSettledWriteSubEnd j..selectorMUWriteReadTime j,
              bgpParams38.A * (sol w).α t *
                bGateZ bgpParams38.L ((sol w).μ t) t := by
        apply intervalIntegral.integral_nonneg (selectorMUSettledSubEnd_le_read j)
        intro t ht
        exact hgZ0 w j t
          ⟨le_trans (selectorMUWriteHold_le_settledSubEnd j) ht.1, ht.2⟩
      linarith
    hΛ := by
      intro w; exact selectorSettledWriteIntLower_tendsto_atTop
    hBz_nonneg := hBz_nonneg
    hBz_bdd := hBz_bdd
    hδnext := hδnext
    hδnext_nonneg := hδnext_nonneg
    hholdPrefix_nonneg := hholdPrefix_nonneg
    hoff := p_hoff
    hnextWrite := p_hnextWrite
    hfiniteHold := p_hfiniteHold
  }

/-- **Parametric construction of `MUReplicatorSettledFacts`.**

Tracking radii are explicit parameters.  The zero-radius bug (Bz=ρu=δnext=
holdPrefix=Bzu=0) is fixed: these are carried parameters with their own
convergence/nonnegativity hypotheses.  Tracking bounds (hutube_write, hzu,
hz_start, hoff, hnextWrite, hfiniteHold, hspread) are explicit hypotheses. -/
def muReplicatorSettledFacts_param
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (Rbr : ℝ) (hRbr_nonneg : 0 ≤ Rbr)
    (hbranch : ∀ w j i (v : UniversalLocalView),
      |BranchData.evalBranch (branchU v) ((sol w).u (selectorMUWriteHoldTime j)) i| ≤ Rbr)
    (hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j)) t)
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t))
    -- Tracking parameters (was zero, now carried)
    (ρu : ℕ → ℕ → ℝ) (Bzu : ℝ) (Bz : ℕ → ℕ → ℝ) (Bzmax : ℝ)
    (δnext : ℕ → ℕ → ℝ) (holdPrefix : ℕ → ℕ → ℝ)
    -- Tracking convergence/nonnegativity
    (hρu : ∀ w, Tendsto (ρu w) atTop (𝓝 0))
    (hρu_nonneg : ∀ w j, 0 ≤ ρu w j)
    (hBzu0 : 0 ≤ Bzu)
    (hBz_nonneg : ∀ w j, 0 ≤ Bz w j)
    (hBz_bdd : ∀ w, ∀ᶠ j in atTop, Bz w j ≤ Bzmax)
    (hδnext : ∀ w, Tendsto (δnext w) atTop (𝓝 0))
    (hδnext_nonneg : ∀ w j, 0 ≤ δnext w j)
    (hholdPrefix_nonneg : ∀ w j, 0 ≤ holdPrefix w j)
    -- Tracking bounds (carried Reach premises)
    (p_hspread : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j), ∀ i, ∀ v : UniversalLocalView,
      v ≠ localViewU (solMUReplStaticCfg w j) →
        |BranchData.evalBranch (branchU v) ((sol w).u t) i
          - BranchData.evalBranch (branchU (localViewU (solMUReplStaticCfg w j)))
              ((sol w).u t) i| ≤ 2 * Rbr)
    (p_hutube_write : ∀ w j, ∀ i,
      |(sol w).u (selectorMUWriteHoldTime j) i -
        stackMachineEncodingU.enc (solMUReplStaticCfg w j) i| ≤ ρu w j)
    (p_hzu : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j), ∀ i,
      |(sol w).z t i - (sol w).u t i| ≤ Bzu)
    (p_hz_start : ∀ w j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz w j)
    (p_hoff : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
        Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j)
    (p_hnextWrite : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤ δnext w j)
    (p_hfiniteHold : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ holdPrefix w j)
    -- Concentration bound (carried — depends on ConcInputs.hKreset design resolution)
    (p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
          epsLamSettled (V := UniversalLocalView)
            (1 / (Fintype.card UniversalLocalView : ℝ))
            (selectorReplicatorGapVal eta heta)
            (Fintype.card UniversalLocalView : ℝ)
            (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
              Real.exp ((selectorReplicatorGapVal eta heta) *
                ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
                (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)))
            (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)) :
    MUReplicatorSettledFacts sol := by
  let static := solMURepl_settled_static_facts sol boxInputs herr hκ₀_nonneg hg₀ hscale
  exact
  { cfg := solMUReplStaticCfg
    hcfg := solMUReplStaticCfg_eq
    hcfg_step := solMUReplStaticCfg_step
    inputs :=
      { Lmin := fun _ _ => 1 / (Fintype.card UniversalLocalView : ℝ)
        gap := fun _ _ => selectorReplicatorGapVal eta heta
        R0 := fun _ _ => (Fintype.card UniversalLocalView : ℝ)
        Kreset := fun w j =>
          ∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
            Real.exp ((selectorReplicatorGapVal eta heta) *
              ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
              (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
        Rspread := fun _ _ => 2 * Rbr
        hLmin_pos := fun _ _ => solMURepl_concLmin_floor
        hqL := hqL_full
        hgap := selector_replicator_hgap_of_utube herr hutube_win
        hRa := fun w j v hv =>
          solMURepl_concR0_card_bound boxInputs w j
            (hqL_full w j _ ⟨le_refl _, selectorMUWriteStart_le_read j⟩) v hv
        hKreset := fun _ _ => le_refl _
        hRspread_nonneg := fun _ _ => by positivity
        hspread := fun w j i v _hv => by
          have h1 := hbranch w j i v
          have h2 := hbranch w j i (localViewU (solMUReplStaticCfg w j))
          let a := BranchData.evalBranch (branchU v) ((sol w).u (selectorMUWriteHoldTime j)) i
          let b := BranchData.evalBranch (branchU (localViewU (solMUReplStaticCfg w j)))
            ((sol w).u (selectorMUWriteHoldTime j)) i
          show |a - b| ≤ 2 * Rbr
          have htri : |a - b| ≤ |a| + |b| := by
            calc |a - b| = |a + (-b)| := by rw [sub_eq_add_neg]
              _ ≤ |a| + |-b| := abs_add_le a (-b)
              _ = |a| + |b| := by rw [abs_neg]
          linarith
      }
    Λ := fun _w j => selectorSettledWriteIntLower j
    Bz := Bz
    ρu := ρu
    δnext := δnext
    holdPrefix := holdPrefix
    Rspread := 2 * Rbr
    mult := selectorMUHStartMult
    Bzu := Bzu
    Bzmax := Bzmax
    R0max := Fintype.card UniversalLocalView
    hg₀ := solMURepl_static_hg0 hg₀
    hgap0 := solMURepl_static_hgap0 eta heta herr
    hgap_lb := by
      intro w; filter_upwards [] with j; exact le_refl _
    hLmin_lb := by
      intro w; filter_upwards [] with j; exact le_refl _
    hR0_nonneg := by
      intro w; filter_upwards [] with j; positivity
    hR0_bound := by
      intro w; filter_upwards [] with j; exact le_refl _
    hKreset_eq := fun _ _ => rfl
    hκ₀_nonneg := solMURepl_static_hkappa_nonneg hκ₀_nonneg
    hCratio_nonneg := solMURepl_static_hCratio_nonneg
    hratio_bound := solMURepl_static_hratio_bound hκ₀_nonneg hg₀.le hscale
    hdom_nonneg := solMURepl_static_hdom_nonneg
    hdom_write := solMURepl_static_hdom_write
    hgZ_cont := solMURepl_static_hgZ_cont sol
    hgZ0 := solMURepl_static_hgZ0 sol
    hmult0 := solMURepl_static_hmult0
    hmultbound := solMURepl_static_hmultbound
    hsum := solMURepl_static_hsum boxInputs
    hlam_nonneg := solMURepl_static_hlam_nonneg boxInputs
    hloser := p_hloser
    hRspread_nonneg := by positivity
    hspread := p_hspread
    hutube_write := p_hutube_write
    hBzu0 := hBzu0
    hzu := p_hzu
    hz_start := p_hz_start
    hΛ_lower := by
      intro w j
      have hdom_nonneg := solMURepl_static_hdom_nonneg
      have hgZ_cont := solMURepl_static_hgZ_cont sol w
      have hgZ0 := solMURepl_static_hgZ0 sol
      have hsub := selector_settled_writeIntegral_lower_lbd_repl (sol w) j
        hdom_nonneg hgZ_cont
      have hcont_int : ∀ a b : ℝ,
          IntervalIntegrable
            (fun t : ℝ => bgpParams38.A * (sol w).α t *
              bGateZ bgpParams38.L ((sol w).μ t) t)
            MeasureTheory.volume a b :=
        fun a b => hgZ_cont.intervalIntegrable a b
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hcont_int (selectorMUWriteHoldTime j) (selectorMUSettledWriteSubEnd j))
        (hcont_int (selectorMUSettledWriteSubEnd j) (selectorMUWriteReadTime j))
      have htail_nonneg :
          0 ≤ ∫ t in selectorMUSettledWriteSubEnd j..selectorMUWriteReadTime j,
              bgpParams38.A * (sol w).α t *
                bGateZ bgpParams38.L ((sol w).μ t) t := by
        apply intervalIntegral.integral_nonneg (selectorMUSettledSubEnd_le_read j)
        intro t ht
        exact hgZ0 w j t
          ⟨le_trans (selectorMUWriteHold_le_settledSubEnd j) ht.1, ht.2⟩
      linarith
    hΛ := by
      intro w; exact selectorSettledWriteIntLower_tendsto_atTop
    hBz_nonneg := hBz_nonneg
    hBz_bdd := hBz_bdd
    hρu := hρu
    hδw_nonneg := by
      intro w j
      unfold δwSettled δuSettled
      apply add_nonneg
      · apply mul_nonneg (by positivity : 0 ≤ 2 * Rbr)
        unfold solMUReplSettledEpsLam epsLamSettled selectorSettledRatioEps
            selectorSettledRatioCoeff
        apply mul_nonneg
        · have : (1 : ℝ) ≤ Fintype.card UniversalLocalView := by
            exact_mod_cast @Fintype.card_pos UniversalLocalView _ ⟨defaultLocalViewU⟩
          linarith
        · apply mul_nonneg
          · apply add_nonneg
            · positivity
            · apply div_nonneg
              · apply intervalIntegral.integral_nonneg (selectorMUWriteStart_le_hold j)
                intro t _ht
                apply mul_nonneg (Real.exp_nonneg _)
                exact mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) _)
                  hκ₀_nonneg
              · apply mul_nonneg
                · exact_mod_cast Nat.zero_le _
                · exact div_nonneg (by norm_num : (0:ℝ) ≤ 1) (by positivity)
          · exact Real.exp_nonneg _
      · apply mul_nonneg solMURepl_static_hmult0
        apply add_nonneg (hρu_nonneg w j)
        apply mul_nonneg hBzu0
        apply mul_nonneg (by positivity : 0 ≤ Real.pi / 3)
        exact Real.exp_nonneg _
    hδnext := hδnext
    hδnext_nonneg := hδnext_nonneg
    hholdPrefix_nonneg := hholdPrefix_nonneg
    hoff := p_hoff
    hnextWrite := p_hnextWrite
    hfiniteHold := p_hfiniteHold
  }

#print axioms muReplicatorSettledHaltFacts_param
#print axioms muReplicatorSettledFacts_param

end Ripple.BoundedUniversality.BGP

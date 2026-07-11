import Ripple.BoundedUniversality.BGP.HeadlineHoffNW
import Ripple.BoundedUniversality.BGP.HeadlineNWMigration
import Ripple.BoundedUniversality.BGP.HeadlineNextWriteNW
import Ripple.BoundedUniversality.BGP.SelectorReplicatorCCPresenter

/-!
# NW flip assembly

Diagonal NW capstones that let `paper3AnalyticResidualDischargeNW_of_diagonal`
consume the landed NW producers, en route to flipping the public
`paper3_headline_unconditional` onto the word-coupled family.

This file is the single home for the flip wiring, kept separate from
`HeadlineNW2` (which carries the S4 analytic leaves) so the two can be built
independently.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance UniversalMachine Filter
open scoped BigOperators Topology

/-- **NW box inputs**: the word-coupled instance of `MUReplicatorBoxInputsP`.
All fields are structural — gate continuity / nonnegativity and the simplex
initial data — mirroring `paper3HeadlineBoxInputs` at the 38 family. -/
def paper3HeadlineBoxInputsNW (w : ℕ) : Paper3HeadlineHoffBoxInputsNW w := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  refine
  { hcr_cont := by fun_prop
    hcg_cont := by fun_prop
    hP_cont := ?_
    hcr_nonneg := ?_
    hlam_sum0 := ?_
    hlam_init_nonneg := ?_
    hz0 := ?_ }
  · intro w' v
    exact paper3UniversalPval_continuous_of_cont_u v
      (fun i => ((paper3HeadlineSolFamNW w) w').cont_u i)
  · intro t
    exact mul_nonneg
      (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) paper3HeadlineM)
      (by norm_num [paper3HeadlineKappa])
  · intro w'
    calc
      (∑ v : UniversalLocalView, ((paper3HeadlineSolFamNW w) w').lam v 0)
          = ∑ _v : UniversalLocalView,
              ((1 / (Fintype.card UniversalLocalView : ℚ)) : ℝ) := by
            apply Finset.sum_congr rfl
            intro v _hv
            exact (paper3HeadlineSolFamNW_initial_values w w').2.2.1 v
      _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        norm_num
  · intro w' v
    rw [(paper3HeadlineSolFamNW_initial_values w w').2.2.1 v]
    have hcard_pos_q : (0 : ℚ) < Fintype.card UniversalLocalView := by
      exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
        0 < Fintype.card UniversalLocalView)
    exact_mod_cast (div_nonneg zero_le_one hcard_pos_q.le)
  · intro w'
    rw [(paper3HeadlineSolFamNW_initial_values w w').1 haltCoordU,
      selectorInitX0_cast_enc]
    exact paper3_enc_haltCoordU_mem_unit (selectorInitConfig w')

/-- `0 ≤ (bgpParamsNW w).A` — the NW gate amplitude is nonnegative.  Feeds the
P-generic box-method units (`halt_z_mem_Icc`, `hz_writeHold_static_next_le_one`,
`hfiniteHold_one`). -/
theorem bgpParamsNW_A_nonneg (w : ℕ) : 0 ≤ (bgpParamsNW w).A := by
  rw [bgpParamsNW_A_eq]; norm_num

/-- **Diagonal NW eventual late-start halt facts.**  Mirror of
`paper3HeadlineEventualLateStartFromAnalyticResidual` at the word-coupled family:
the recovery data is reused (structural), the cg-gate lower bound is the NW
`paper3RecoveryCgMinLeNW`, the settled analytic package is `paper3SettledAnalyticNW`,
the box inputs are `paper3HeadlineBoxInputsNW`, the u-tube is the Seg C seam, the
next-write convergence is `paper3HeadlineNextWriteNW`, and the halt-field Hoff
drift `p_hoff` comes from the Hoff residual (the S4 edge caps), taken here as a
hypothesis. -/
def paper3HeadlineEventualLateStartNW
    (hoffRes : Paper3HeadlineHoffFieldIntegralResidualNW) :
    ∀ w, EventualLateStartHaltFactsAt (paper3HeadlineSolFamNW w) w := by
  intro w
  -- `paper3HeadlineNextWriteNW w` is a Prop-valued `∃`; the target structure
  -- carries data (`δnext`), so extract via `Classical.choose` (allowed in a
  -- Type-valued def under `noncomputable section`) rather than `obtain`
  -- (which would be large elimination from `Prop`).
  have hNW := paper3HeadlineNextWriteNW w
  have hδn_tend := hNW.choose_spec.1
  have hδn_nonneg := hNW.choose_spec.2.1
  have hδn_bound := hNW.choose_spec.2.2
  exact
    EventualLateStartHaltFactsAt.ofLateStart <|
      muReplicatorLateStartHaltFactsAt_shifted_P
        (sol := paper3HeadlineSolFamNW w) (w := w)
        (paper3SettledAnalyticNW w)
        (bgpParamsNW_A_nonneg w)
        (paper3HeadlineBoxInputsNW w)
        paper3HeadlineHerr
        (paper3RecoveryCrMin w) (paper3RecoveryCrMax w)
        (paper3RecoveryCgMin w) (paper3RecoveryGap w)
        (paper3RecoveryB w) (paper3RecoveryK w)
        paper3HeadlineHCardTwo
        (paper3RecoveryCrMin_pos w) (paper3RecoveryCrMin_le_crMax w)
        (paper3RecoveryCgMin_nonneg w) (paper3RecoveryGap_nonneg w)
        (paper3RecoveryGap_le_gapVal w) (paper3RecoveryB_eq w)
        (paper3RecoveryB_pos w) (paper3RecoveryBDelta w)
        (paper3RecoveryPow w) (paper3RecoveryCrBounds w)
        (paper3RecoveryCgMinLeNW w)
        ((paper3F1FullUTubeResidualNW_all w).hutube_win)
        (Bz := fun _ => (1 : ℝ)) (Bzmax := (1 : ℝ))
        (δnext := hNW.choose) (holdPrefix := fun _ => (1 : ℝ))
        (by intro j; norm_num)
        (Filter.Eventually.of_forall fun j => le_rfl)
        hδn_tend
        hδn_nonneg
        (by intro j; norm_num)
        ((paper3HeadlineBoxInputsNW w).hz_writeHold_static_next_le_one
          (bgpParamsNW_A_nonneg w) w)
        (paper3HeadlineHoffNW hoffRes w)
        hδn_bound
        ((paper3HeadlineBoxInputsNW w).hfiniteHold_one (bgpParamsNW_A_nonneg w) w)

/-- **The NW-route headline, modulo the S4 edge caps.**  Given the Hoff
field-integral residual (the closed S4 edge caps), the word-coupled family
simulates the universal machine — the diagonal NW readout of the eventual
late-start halt facts. -/
theorem paper3_headline_unconditional_of_hoffResidualNW
    (hoffRes : Paper3HeadlineHoffFieldIntegralResidualNW) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P undecidableMachine) := by
  have late := paper3HeadlineEventualLateStartNW hoffRes
  refine paper3_headline_unconditional_of_NW_readout ?_ ?_
  · intro w hw
    have hwU : M_U.haltsOn w := by simpa using hw
    exact (late w).correct_halt_z_P
      (fun t ht =>
        ((paper3HeadlineBoxInputsNW w).halt_z_mem_Icc (bgpParamsNW_A_nonneg w)
          w t ht).2)
      hwU
  · intro w hw
    have hwU : ¬ M_U.haltsOn w := by simpa using hw
    exact (late w).correct_nonhalt_z_P
      (fun t ht =>
        ((paper3HeadlineBoxInputsNW w).halt_z_mem_Icc (bgpParamsNW_A_nonneg w)
          w t ht).1)
      hwU

end Ripple.BoundedUniversality.BGP

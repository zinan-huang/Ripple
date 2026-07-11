import Ripple.BoundedUniversality.BGP.SelectorReplicatorMargin

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorAvgGap
------------------------------------
Average payoff-gap discharge for the simplex replicator.

The only content is finite-sum algebra: if the winner beats every loser by
`gap` and the selector weights form a nonnegative simplex, then the winner also
beats the weighted average by `gap` times the loser mass.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MachineInstance

theorem selector_replicator_avg_gap_of_pointwise
    {V : Type} [Fintype V]
    (lam P : V → ℝ) (vstar : V) {gap : ℝ}
    (hsum : (∑ v : V, lam v) = 1)
    (hlam_nonneg : ∀ v : V, 0 ≤ lam v)
    (hgap : ∀ v : V, v ≠ vstar → gap ≤ P vstar - P v) :
    gap * (1 - lam vstar) ≤ P vstar - ∑ v : V, lam v * P v := by
  classical
  have hrewrite :
      P vstar - ∑ v : V, lam v * P v =
        ∑ v : V, lam v * (P vstar - P v) := by
    calc
      P vstar - ∑ v : V, lam v * P v
          = (∑ v : V, lam v) * P vstar - ∑ v : V, lam v * P v := by
              rw [hsum]
              ring
      _ = ∑ v : V, lam v * (P vstar - P v) := by
              rw [Finset.sum_mul]
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro v _
              ring
  have hdrop :
      (∑ v : V, lam v * (P vstar - P v)) =
        (Finset.univ.erase vstar).sum (fun v => lam v * (P vstar - P v)) := by
    rw [← Finset.add_sum_erase _ (fun v => lam v * (P vstar - P v))
      (Finset.mem_univ vstar)]
    simp
  have hsum_erase :
      (Finset.univ.erase vstar).sum (fun v : V => lam v) = 1 - lam vstar := by
    calc
      (Finset.univ.erase vstar).sum (fun v : V => lam v)
          = (∑ v : V, lam v) - lam vstar := by
              rw [← Finset.add_sum_erase _ (fun v : V => lam v)
                (Finset.mem_univ vstar)]
              ring
      _ = 1 - lam vstar := by rw [hsum]
  have hleft :
      gap * (1 - lam vstar) =
        (Finset.univ.erase vstar).sum (fun v : V => lam v * gap) := by
    calc
      gap * (1 - lam vstar) = (1 - lam vstar) * gap := by ring
      _ = ((Finset.univ.erase vstar).sum (fun v : V => lam v)) * gap := by
            rw [hsum_erase]
      _ = (Finset.univ.erase vstar).sum (fun v : V => lam v * gap) := by
            rw [Finset.sum_mul]
  have hterm :
      (Finset.univ.erase vstar).sum (fun v : V => lam v * gap) ≤
        (Finset.univ.erase vstar).sum (fun v : V => lam v * (P vstar - P v)) := by
    refine Finset.sum_le_sum ?_
    intro v hv
    exact mul_le_mul_of_nonneg_left (hgap v (Finset.mem_erase.mp hv).1)
      (hlam_nonneg v)
  calc
    gap * (1 - lam vstar)
        = (Finset.univ.erase vstar).sum (fun v : V => lam v * gap) := hleft
    _ ≤ (Finset.univ.erase vstar).sum (fun v : V => lam v * (P vstar - P v)) := hterm
    _ = ∑ v : V, lam v * (P vstar - P v) := by rw [hdrop]
    _ = P vstar - ∑ v : V, lam v * P v := by rw [hrewrite]

/-- Concrete `M_U` average-gap discharge from the encoding tube.

`hgap_le` lets callers use any recovery gap no larger than the tube-derived
selector gap `selectorReplicatorGapVal eta heta`. -/
theorem selector_replicator_havg_gap_of_utube
    {eta : ℚ} {heta : 0 < eta}
    {lam : UniversalLocalView → ℝ} {u : Fin d_U → ℝ} {c : UConf} {gap : ℝ}
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (htube : UTube r_LE_U c u)
    (hgap_le : gap ≤ selectorReplicatorGapVal eta heta)
    (hsum : (∑ v : UniversalLocalView, lam v) = 1)
    (hlam_nonneg : ∀ v : UniversalLocalView, 0 ≤ lam v) :
    gap * (1 - lam (localViewU c)) ≤
      universalPval eta heta (localViewU c) u -
        ∑ v : UniversalLocalView, lam v * universalPval eta heta v u := by
  classical
  have hmargins :=
    universal_selector_margins_of_tube (eta := eta) (heta := heta)
      (c := c) (Z := u) htube herr
  refine
    selector_replicator_avg_gap_of_pointwise
      (lam := lam)
      (P := fun v : UniversalLocalView => universalPval eta heta v u)
      (vstar := localViewU c)
      (gap := gap)
      hsum hlam_nonneg ?_
  intro v hv
  have hwinner :
      1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel ≤
        universalPval eta heta (localViewU c) u := by
    simpa [universalPval] using hmargins.1
  have hloser :
      universalPval eta heta v u ≤
        -(1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel) := by
    simpa [universalPval] using hmargins.2 v hv
  have hgapVal_le :
      selectorReplicatorGapVal eta heta ≤
        universalPval eta heta (localViewU c) u - universalPval eta heta v u := by
    dsimp [selectorReplicatorGapVal]
    linarith
  exact le_trans hgap_le hgapVal_le

#print axioms selector_replicator_avg_gap_of_pointwise
#print axioms selector_replicator_havg_gap_of_utube

end Ripple.BoundedUniversality.BGP

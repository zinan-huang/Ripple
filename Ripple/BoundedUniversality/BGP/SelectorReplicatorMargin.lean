import Ripple.BoundedUniversality.BGP.SelectorReplicatorMixReduce

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorMargin
------------------------------------
Readout-margin discharge for the concrete `M_U` replicator concentration inputs.

The gap is not an independent concentration assumption: it is the universal
selector `Pval` margin, reused pointwise from the rail-agnostic tube lemma.
The only dynamic hypothesis carried here is the config `u`-tube over the write
window; the selector atom sharpness remains the static `errSel < 1/2` fact.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance

/-- The concrete readout gap used by the replicator concentration estimate. -/
def selectorReplicatorGapVal (eta : ℚ) (heta : 0 < eta) : ℝ :=
  1 - 2 * (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel

/-- Positivity of the concrete readout gap is exactly the selector sharpness
condition `errSel < 1/2`. -/
theorem selectorReplicatorGapVal_pos
    (eta : ℚ) (heta : 0 < eta)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2) :
    0 < selectorReplicatorGapVal eta heta := by
  dsimp [selectorReplicatorGapVal]
  linarith

/-- Discharge the `SelectorReplicatorConcInputs.hgap` field from the carried
config `u`-tube and the static universal selector sharpness.

Instantiating `gap w j := selectorReplicatorGapVal eta heta = 1 - 2*errSel`,
the loser/winner readout difference is bounded by `-gap` throughout each write
window. -/
theorem selector_replicator_hgap_of_utube
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    {cfg : ℕ → ℕ → UConf}
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hutube_win : ∀ w j, ∀ t ∈
      Ico (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
        UTube r_LE_U (cfg w j) ((sol w).u t)) :
    ∀ w j, ∀ v : UniversalLocalView, v ≠ localViewU (cfg w j) →
      ∀ t ∈ Ico (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
        universalPval eta heta v ((sol w).u t)
          - universalPval eta heta (localViewU (cfg w j)) ((sol w).u t) ≤
            -((fun _w _j => selectorReplicatorGapVal eta heta) w j) := by
  intro w j v hv t ht
  have hmargins :=
    universal_selector_margins_of_tube (eta := eta) (heta := heta)
      (c := cfg w j) (Z := (sol w).u t) (hutube_win w j t ht) herr
  have hwinner :
      1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel ≤
        universalPval eta heta (localViewU (cfg w j)) ((sol w).u t) := by
    simpa [universalPval] using hmargins.1
  have hloser :
      universalPval eta heta v ((sol w).u t) ≤
        -(1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel) := by
    simpa [universalPval] using hmargins.2 v hv
  change
    universalPval eta heta v ((sol w).u t)
        - universalPval eta heta (localViewU (cfg w j)) ((sol w).u t) ≤
      -selectorReplicatorGapVal eta heta
  dsimp [selectorReplicatorGapVal]
  linarith

/-- Pointwise pairwise selector gap for a two-view safe set from two tube facts.

This is the payoff-gap input needed by aggregate old/new bad-mass estimates.
It deliberately leaves the real dynamic work explicit: callers must prove that
the same state lies in both the old and new `UTube`s on the interval in question. -/
theorem universalPval_pairwise_gap_bad_to_old_new_of_tubes
    {eta : ℚ} {heta : 0 < eta}
    {cold cnew : UConf} {Z : Fin d_U → ℝ} {gap : ℝ}
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hgap_le : gap ≤ selectorReplicatorGapVal eta heta)
    (hUold : UTube r_LE_U cold Z)
    (hUnew : UTube r_LE_U cnew Z) :
    ∀ v : UniversalLocalView,
      v ∉ ({localViewU cold, localViewU cnew} : Finset UniversalLocalView) →
    ∀ u : UniversalLocalView,
      u ∈ ({localViewU cold, localViewU cnew} : Finset UniversalLocalView) →
      universalPval eta heta v Z - universalPval eta heta u Z ≤ -gap := by
  classical
  intro v hv u hu
  have hu_cases : u = localViewU cold ∨ u = localViewU cnew := by
    simpa using hu
  rcases hu_cases with rfl | rfl
  · have hvne : v ≠ localViewU cold := by
      intro h
      apply hv
      simp [h]
    have hmargins :=
      universal_selector_margins_of_tube (eta := eta) (heta := heta)
        (c := cold) (Z := Z) hUold herr
    have hwinner :
        1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel ≤
          universalPval eta heta (localViewU cold) Z := by
      simpa [universalPval] using hmargins.1
    have hloser :
        universalPval eta heta v Z ≤
          -(1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel) := by
      simpa [universalPval] using hmargins.2 v hvne
    have hgapVal_le :
        selectorReplicatorGapVal eta heta ≤
          universalPval eta heta (localViewU cold) Z -
            universalPval eta heta v Z := by
      dsimp [selectorReplicatorGapVal]
      linarith
    have hgap' :
        gap ≤ universalPval eta heta (localViewU cold) Z -
          universalPval eta heta v Z :=
      le_trans hgap_le hgapVal_le
    linarith
  · have hvne : v ≠ localViewU cnew := by
      intro h
      apply hv
      simp [h]
    have hmargins :=
      universal_selector_margins_of_tube (eta := eta) (heta := heta)
        (c := cnew) (Z := Z) hUnew herr
    have hwinner :
        1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel ≤
          universalPval eta heta (localViewU cnew) Z := by
      simpa [universalPval] using hmargins.1
    have hloser :
        universalPval eta heta v Z ≤
          -(1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel) := by
      simpa [universalPval] using hmargins.2 v hvne
    have hgapVal_le :
        selectorReplicatorGapVal eta heta ≤
          universalPval eta heta (localViewU cnew) Z -
            universalPval eta heta v Z := by
      dsimp [selectorReplicatorGapVal]
      linarith
    have hgap' :
        gap ≤ universalPval eta heta (localViewU cnew) Z -
          universalPval eta heta v Z :=
      le_trans hgap_le hgapVal_le
    linarith

/-- Simultaneous old/new `UTube` is impossible whenever the local views differ.
The `errSel < 1/2` hypothesis is `bgpHeadlineHerr` at the concrete level. -/
theorem no_dual_utube_of_view_ne
    (eta : ℚ) (heta : 0 < eta)
    (cold cnew : UConf)
    (hne : localViewU cold ≠ localViewU cnew)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (Z : Fin d_U → ℝ)
    (hold : UTube r_LE_U cold Z)
    (hnew : UTube r_LE_U cnew Z) :
    False := by
  have hmOld :=
    universal_selector_margins_of_tube (eta := eta) (heta := heta)
      (c := cold) (Z := Z) hold herr
  have hmNew :=
    universal_selector_margins_of_tube (eta := eta) (heta := heta)
      (c := cnew) (Z := Z) hnew herr
  have hlow :
      1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel ≤
        universalPval eta heta (localViewU cold) Z := by
    simpa [universalPval] using hmOld.1
  have hup :
      universalPval eta heta (localViewU cold) Z ≤
        -(1 / 2 - (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel) := by
    simpa [universalPval] using hmNew.2 (localViewU cold) hne
  linarith

#print axioms selectorReplicatorGapVal
#print axioms selectorReplicatorGapVal_pos
#print axioms selector_replicator_hgap_of_utube
#print axioms no_dual_utube_of_view_ne

end Ripple.BoundedUniversality.BGP

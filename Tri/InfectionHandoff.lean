/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionKernel
import Tri.Step

/-!
# Handoff from the infection protocol to ordinary Tri

Once every molecule is active, the infection scheduler has only its first four
event classes left.  Those classes are exactly the four triple compositions of
ordinary Tri.  This file records the equality first at the event level and then
at the state-step level.
-/

namespace Tri

open scoped ENNReal

/-- Every molecule in an infection configuration is active. -/
def InfectionCfg.AllActive (s : InfectionCfg) : Prop :=
  s.ix = 0 ∧ s.iy = 0

/-- Forget the infection-specific refinement of a triple event.  Mixed and
all-inactive events are sent to an arbitrary inert class; under `AllActive`
they have zero mass. -/
def InfectionEvent.toTripleKind : InfectionEvent → TripleKind
  | .activeXXX => .xxx
  | .activeXXY => .xxy
  | .activeXYY => .xyy
  | .activeYYY => .yyy
  | .activateOneX
  | .activateOneY
  | .activateTwoXX
  | .activateTwoXY
  | .activateTwoYY
  | .inactiveOnly => .xxx

/-- With no inactive molecules, the infection event scheduler projects exactly
to the ordinary four-composition scheduler. -/
theorem infectionEventPMF_map_allActive
    (s : InfectionCfg) (h : 3 ≤ s.total) (hs : s.AllActive) :
    (infectionEventPMF s h).map InfectionEvent.toTripleKind =
      interactionPMF s.ax s.ay (by
        rcases hs with ⟨hix, hiy⟩
        simpa [InfectionCfg.total, InfectionCfg.active,
          InfectionCfg.inactive, hix, hiy] using h) := by
  rcases hs with ⟨hix, hiy⟩
  ext k
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset InfectionEvent) =
    {InfectionEvent.activeXXX, InfectionEvent.activeXXY,
      InfectionEvent.activeXYY, InfectionEvent.activeYYY,
      InfectionEvent.activateOneX, InfectionEvent.activateOneY,
      InfectionEvent.activateTwoXX, InfectionEvent.activateTwoXY,
      InfectionEvent.activateTwoYY, InfectionEvent.inactiveOnly} from rfl]
  cases k <;>
    simp [InfectionEvent.toTripleKind, infectionEventPMF_apply,
      InfectionEvent.weight, interactionPMF_apply, TripleKind.weight,
      InfectionCfg.total, InfectionCfg.active, InfectionCfg.inactive, hix, hiy]

/-- A zero-weight infection event has zero scheduler mass. -/
theorem infectionEventPMF_zero_of_weight_zero
    {s : InfectionCfg} {h : 3 ≤ s.total} {e : InfectionEvent}
    (he : InfectionEvent.weight s e = 0) :
    infectionEventPMF s h e = 0 := by
  rw [infectionEventPMF_apply, he]
  simp

/-- On every positive-mass event after full activation, the active-`X` update
agrees with the ordinary Tri update. -/
theorem InfectionEvent.next_ax_allActive
    (s : InfectionCfg) (e : InfectionEvent) (hs : s.AllActive)
    (he : InfectionEvent.weight s e ≠ 0) :
    (InfectionEvent.next s e).ax =
      nextX s.ax e.toTripleKind := by
  rcases hs with ⟨hix, hiy⟩
  cases e <;>
    simp [InfectionEvent.weight, InfectionCfg.active,
      InfectionEvent.next, InfectionEvent.toTripleKind, nextX, hix, hiy] at he ⊢

/-- The subtype guard is invisible to the active-`X` projection on every
positive-mass event. -/
theorem InfectionEvent.nextState_ax_allActive
    {n : ℕ} (s : InfectionState n) (e : InfectionEvent)
    (hs : s.1.AllActive) (he : InfectionEvent.weight s.1 e ≠ 0) :
    (InfectionEvent.nextState s e).1.ax =
      nextX s.1.ax e.toTripleKind := by
  rw [InfectionEvent.nextState, dif_neg he]
  exact InfectionEvent.next_ax_allActive s.1 e hs he

/-- Once all molecules are active, one infection step projected to the number
of active `X` molecules is exactly one ordinary Tri step. -/
theorem infectionStateStep_map_ax_allActive
    (n : ℕ) (h3 : 3 ≤ n) (s : InfectionState n)
    (hs : s.1.AllActive) :
    (infectionStateStep n h3 s).map (fun z => z.1.ax) =
      triStep s.1.ax s.1.ay (by
        have hinv := s.2
        rcases hs with ⟨hix, hiy⟩
        simp only [InfectionCfg.Inv, InfectionCfg.total,
          InfectionCfg.active, InfectionCfg.inactive] at hinv
        omega) := by
  have htotal : 3 ≤ s.1.total := by
    have hinv := s.2
    simp only [InfectionCfg.Inv] at hinv
    omega
  unfold infectionStateStep
  rw [PMF.map_comp]
  calc
    (infectionEventPMF s.1 htotal).map
        ((fun z : InfectionState n => z.1.ax) ∘
          InfectionEvent.nextState s) =
        (infectionEventPMF s.1 htotal).map
          (fun e => nextX s.1.ax e.toTripleKind) := by
            ext z
            rw [PMF.map_apply, PMF.map_apply]
            apply tsum_congr
            intro e
            by_cases he : InfectionEvent.weight s.1 e = 0
            · rw [infectionEventPMF_zero_of_weight_zero he]
              simp
            · have hnext :=
                InfectionEvent.nextState_ax_allActive s e hs he
              simp only [Function.comp_apply]
              simp [hnext]
    _ = ((infectionEventPMF s.1 htotal).map
          InfectionEvent.toTripleKind).map (nextX s.1.ax) := by
            rw [PMF.map_comp]
            rfl
    _ = triStep s.1.ax s.1.ay _ := by
            rw [infectionEventPMF_map_allActive s.1 htotal hs]
            rfl

end Tri

#print axioms Tri.infectionEventPMF_map_allActive
#print axioms Tri.InfectionEvent.nextState_ax_allActive
#print axioms Tri.infectionStateStep_map_ax_allActive

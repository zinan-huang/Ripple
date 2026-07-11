/-
Ripple.BoundedUniversality.HenonSelector.SelectorConsequences
-----------------------------------------
F4: T1 (Algebraic Horseshoe Rigidity) ⇒ no algebraic selector
    for families requiring nonperiodic itineraries.

This is the core structural no-go theorem: if all Q-algebraic
horseshoe points are periodic, then any algebraic selector can
only produce periodic itineraries.
-/

import Ripple.BoundedUniversality.HenonSelector.Selector

namespace Ripple.BoundedUniversality.HenonSelector

theorem T1_forces_selected_itineraries_periodic
    (hc : HenonCoding) (fam : UniversalItineraryFamily)
    (hT1 : AlgebraicHorseshoeRigidity hc)
    (sel : AlgebraicSelector hc fam) :
    ∀ n : ℕ, IsPeriodicSeq (fam.s n) := by
  intro n
  have hin : InOmega hc (sel.φ n) :=
    ⟨fam.s n, (sel.realizes n).symm⟩
  have hper_z : IsHenonPeriodic (sel.φ n) :=
    hT1 (sel.φ n) hin (sel.alg n)
  have hper_omega : IsHenonPeriodic (hc.omega (fam.s n)) := by
    rwa [← sel.realizes n]
  exact henon_periodic_omega_to_shift_periodic hc hper_omega

theorem T1_no_selector_if_nonperiodic_required
    (hc : HenonCoding) (fam : UniversalItineraryFamily)
    (hT1 : AlgebraicHorseshoeRigidity hc)
    (hNP : NonperiodicRequired fam) :
    IsEmpty (AlgebraicSelector hc fam) := by
  constructor
  intro sel
  rcases hNP with ⟨n, hn⟩
  exact hn (T1_forces_selected_itineraries_periodic hc fam hT1 sel n)

end Ripple.BoundedUniversality.HenonSelector

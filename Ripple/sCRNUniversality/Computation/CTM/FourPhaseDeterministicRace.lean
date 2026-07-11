import Ripple.sCRNUniversality.Stochastic.JumpPathLaw
import Ripple.sCRNUniversality.Computation.CTM.FourPhaseMacroModule

namespace Ripple.sCRNUniversality

namespace CTM

universe u

namespace FourPhaseDeterministicRace

variable {Q : Type u} [Fintype Q] [DecidableEq Q] {s : Nat}

def deterministicRace (M : Binary Q) :
    Stochastic.RacePredicate (FourPhaseMacroModule.network (s := s) M) where
  winsAt path t i := path.fired t = some i
  wins_fired := fun h => h

theorem deterministicRace_winsListAt_of_firesListAt
    (M : Binary Q)
    (path : (FourPhaseMacroModule.network (s := s) M).Path)
    (t : Nat) :
    ∀ (is : List (FourPhaseMacroModule.network (s := s) M).I),
    path.FiresListAt t is →
    (deterministicRace (s := s) M).WinsListAt path t is
  | [], _ => trivial
  | i :: is, ⟨hfired, hrest⟩ =>
    ⟨hfired, deterministicRace_winsListAt_of_firesListAt M path (t + 1) is hrest⟩

theorem deterministicRace_trivial_bound
    {Omega : Type*}
    (M : Binary Q)
    (L : Stochastic.JumpPathLaw (FourPhaseMacroModule.network (s := s) M) Omega)
    {z0 z1 : State (FourPhaseSpecies Q)}
    (I : (FourPhaseMacroModule.network (s := s) M).IntendedSchedule z0 z1)
    (t : Nat) :
    Probability.ErrorEvent
      (fun omega =>
        (deterministicRace (s := s) M).WinsListAt
          (L.path omega) t I.schedule) ⊆
      Probability.ErrorEvent
        (fun omega =>
          (L.path omega).FiresListAt t I.schedule) := by
  intro omega hnotWins hFires
  exact hnotWins
    (deterministicRace_winsListAt_of_firesListAt M (L.path omega) t
      I.schedule hFires)

end FourPhaseDeterministicRace

end CTM

end Ripple.sCRNUniversality

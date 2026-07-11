import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.RankingBound

namespace SSEM

open scoped ENNReal

variable {n : ℕ}

/-- The ranking-initialization target requested in the handoff. -/
def RankingInitTarget (C : Config (AgentState n) Opinion n) : Prop :=
  FreshRankingStart C ∨ IsConsensusConfig C ∨ InSrank C

/-- An all-`Resetting` nonempty configuration is not already at the requested target. -/
theorem not_rankingInitTarget_of_all_resetting
    (hn0 : 0 < n) (C : Config (AgentState n) Opinion n)
    (hAllR : ∀ w : Fin n, (C w).1.role = .Resetting) :
    ¬ RankingInitTarget C := by
  intro hTarget
  rcases hTarget with hFresh | hConsensus | hSrank
  · obtain ⟨root, hroot, _hrank, _hchildren, _hothers⟩ := hFresh
    rw [hAllR root] at hroot
    cases hroot
  · let w : Fin n := ⟨0, hn0⟩
    have hbad : Role.Resetting = Role.Settled := by
      rw [← hAllR w]
      exact hConsensus.allSettled w
    cases hbad
  · let w : Fin n := ⟨0, hn0⟩
    have hbad : Role.Resetting = Role.Settled := by
      rw [← hAllR w]
      exact hSrank.allSettled w
    cases hbad

end SSEM

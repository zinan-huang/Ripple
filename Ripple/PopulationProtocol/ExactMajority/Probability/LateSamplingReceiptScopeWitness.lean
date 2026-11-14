import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingReceiptScope

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingReceiptScope

open TimeTheorem

private theorem tie_cfg (m : ℕ) :
    ∃ init : InputCfg (2 * m), validInitial init ∧ init.card = 2 * m ∧
      gapMagnitude init = 0 := by
  let a : AgentState (PhaseThreeModel.Numeric.hourIndex (2 * m)) 256 :=
    canonicalInitialAgent _ _
  let b : AgentState (PhaseThreeModel.Numeric.hourIndex (2 * m)) 256 :=
    { a with input := .B, smallBias := ⟨2, by decide⟩ }
  refine ⟨Multiset.replicate m a + Multiset.replicate m b, ?_, ?_, ?_⟩
  · intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]
      simp [a, canonicalInitialAgent]
    · rw [Multiset.eq_of_mem_replicate hx]
      simp [b, a, canonicalInitialAgent]
  · simp; omega
  · have h1 : Multiset.filter (fun x => x.input = .A) (Multiset.replicate m a)
        = Multiset.replicate m a :=
      Multiset.filter_eq_self.mpr fun x hx => by
        rw [Multiset.eq_of_mem_replicate hx]; rfl
    have h2 : Multiset.filter (fun x => x.input = .A) (Multiset.replicate m b)
        = 0 :=
      Multiset.filter_eq_nil.mpr fun x hx => by
        rw [Multiset.eq_of_mem_replicate hx]; simp [b]
    have h3 : Multiset.filter (fun x => x.input = .B) (Multiset.replicate m a)
        = 0 :=
      Multiset.filter_eq_nil.mpr fun x hx => by
        rw [Multiset.eq_of_mem_replicate hx]; simp [a, canonicalInitialAgent]
    have h4 : Multiset.filter (fun x => x.input = .B) (Multiset.replicate m b)
        = Multiset.replicate m b :=
      Multiset.filter_eq_self.mpr fun x hx => by
        rw [Multiset.eq_of_mem_replicate hx]
    unfold gapMagnitude initialGap
    rw [Multiset.filter_add, Multiset.filter_add, h1, h2, h3, h4]
    simp

private theorem strong_cfg (m : ℕ) :
    ∃ init : InputCfg m, validInitial init ∧ init.card = m ∧
      m ≤ 40 * gapMagnitude init := by
  refine ⟨Multiset.replicate m (canonicalInitialAgent _ _),
    validInitial_replicate_canonicalInitialAgent _ _ _, by simp, ?_⟩
  have h1 : Multiset.filter (fun x => x.input = .A)
      (Multiset.replicate m (canonicalInitialAgent (PhaseThreeModel.Numeric.hourIndex m) 256))
        = Multiset.replicate m (canonicalInitialAgent _ _) :=
    Multiset.filter_eq_self.mpr fun x hx => by
      rw [Multiset.eq_of_mem_replicate hx]; rfl
  have h3 : Multiset.filter (fun x => x.input = .B)
      (Multiset.replicate m (canonicalInitialAgent (PhaseThreeModel.Numeric.hourIndex m) 256))
        = 0 :=
    Multiset.filter_eq_nil.mpr fun x hx => by
      rw [Multiset.eq_of_mem_replicate hx]; simp [canonicalInitialAgent]
  unfold gapMagnitude initialGap
  rw [h1, h3]
  simp
  omega

/-- Non-vacuity of the tie obstruction: a GoodInput configuration with equal
A and B counts exists (at population twice the threshold, symbolically). -/
theorem exists_tie_goodInput :
    ∃ n : ℕ, ∃ init : InputCfg n,
      ThresholdEpidemic.GoodInput n init ∧ gapMagnitude init = 0 := by
  obtain ⟨init, hv, hc, hg⟩ := tie_cfg TimeTheorem.timePopulationThreshold
  exact ⟨_, init, ⟨by omega, hv, hc⟩, hg⟩

/-- Non-vacuity of the strong-gap obstruction. -/
theorem exists_strongGap_goodInput :
    ∃ n : ℕ, ∃ init : InputCfg n,
      ThresholdEpidemic.GoodInput n init ∧ n ≤ 40 * gapMagnitude init := by
  obtain ⟨init, hv, hc, hg⟩ := strong_cfg TimeTheorem.timePopulationThreshold
  exact ⟨_, init, ⟨le_rfl, hv, hc⟩, hg⟩

#print axioms exists_tie_goodInput
#print axioms exists_strongGap_goodInput

end Ripple.PopulationProtocol.ExactMajority.LateSamplingReceiptScope

end

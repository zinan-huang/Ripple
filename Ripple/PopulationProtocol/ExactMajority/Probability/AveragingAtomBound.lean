-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingAtomBound.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingLogPotentialTail

/-!
# Actual atom bounds from old-index extinction

An extinct lower augmented potential also excludes pending nonzero mass.
Thus its consequence for a higher potential applies to the same physical
configuration, including agents which have not yet activated.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingAtomBound

open TimeTheorem AveragingIntegerPotential AveragingPotentialService
open AveragingNumerics AveragingPotentialDrift AveragingLogPotentialTail

variable {L : ℕ}

theorem smallBias_natAbs_le_one (a : AgentState L 256) (ha : PotentialAgent a) :
    (AgentState.smallBiasInt a).natAbs ≤ 1 := by
  have hs := ha.safe
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with hs | hs | hs <;>
    norm_num [AgentState.smallBiasInt, hs]

theorem active_atom_le (h : ℕ) (a : AgentState L 256) :
    activeAgentPhiNat h a ≤ 4 ^ (h - 1) := by
  cases hb : a.bias with
  | zero => simp [activeAgentPhiNat, hb]
  | dyadic sigma j =>
      by_cases hj : j.val < h
      · simpa only [activeAgentPhiNat, hb, if_pos hj] using
          (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 4)
            (show h - 1 - j.val ≤ h - 1 from Nat.sub_le _ _))
      · simp [activeAgentPhiNat, hb, hj]

theorem augmented_atom_le (h : ℕ) (a : AgentState L 256) (ha : PotentialAgent a) :
    augmentedAgentPhiNat h a ≤ 2 * 4 ^ (h - 1) := by
  by_cases hp : a.phase.val < 3
  · have hmul := Nat.mul_le_mul_left (2 * 4 ^ (h - 1)) (smallBias_natAbs_le_one a ha)
    simpa only [augmentedAgentPhiNat, if_pos hp, mul_one] using hmul
  · have hactive := active_atom_le h a
    simp only [augmentedAgentPhiNat, if_neg hp]
    omega

theorem agentPhiNat_le_total (h : ℕ) (c : Cfg L 256)
    (a : AgentState L 256) (ha : a ∈ c) :
    augmentedAgentPhiNat h a ≤ augmentedPhiNat h c := by
  revert a
  induction c using Multiset.induction_on with
  | empty => intro a ha; simp at ha
  | cons b c ih =>
      intro a ha
      simp only [augmentedPhiNat, Multiset.map_cons, Multiset.sum_cons]
      rcases Multiset.mem_cons.mp ha with hab | hac
      · subst a
        exact Nat.le_add_right _ _
      · exact (ih a hac).trans (Nat.le_add_left _ _)

theorem old_agent_atom_zero (r : ℕ) (c : Cfg L 256)
    (hz : augmentedPhiNat r c = 0) (a : AgentState L 256) (ha : a ∈ c) :
    augmentedAgentPhiNat r a = 0 := by
  have hle := agentPhiNat_le_total r c a ha
  rw [hz] at hle
  omega

theorem pending_natAbs_zero_of_old_atom_zero (r : ℕ) (a : AgentState L 256)
    (hp : a.phase.val < 3) (hz : augmentedAgentPhiNat r a = 0) :
    (AgentState.smallBiasInt a).natAbs = 0 := by
  simp only [augmentedAgentPhiNat, if_pos hp] at hz
  have hcoeff : 0 < 2 * (4 : ℕ) ^ (r - 1) := by positivity
  exact (Nat.mul_eq_zero.mp hz).resolve_left (Nat.ne_of_gt hcoeff)

/-- Every pending nonzero is excluded by the old augmented potential, as
well as every active token below its cutoff. -/
theorem atom_le_of_old_zero (h q : ℕ) (hhq : q < h)
    (a : AgentState L 256) (hz : augmentedAgentPhiNat (h - q) a = 0) :
    augmentedAgentPhiNat h a ≤ 4 ^ (q - 1) := by
  by_cases hp : a.phase.val < 3
  · have habs := pending_natAbs_zero_of_old_atom_zero (h - q) a hp hz
    simp [augmentedAgentPhiNat, hp, habs]
  · cases hb : a.bias with
    | zero => simp [augmentedAgentPhiNat, hp, activeAgentPhiNat, hb]
    | dyadic sigma j =>
        have hjold : h - q ≤ j.val := by
          by_contra hj
          have hjlt : j.val < h - q := by omega
          have hzero : (4 : ℕ) ^ (h - q - 1 - j.val) = 0 := by
            simpa only [augmentedAgentPhiNat, if_neg hp, activeAgentPhiNat, hb,
              if_pos hjlt] using hz
          have hpos : 0 < (4 : ℕ) ^ (h - q - 1 - j.val) := by positivity
          omega
        by_cases hj : j.val < h
        · have he : h - 1 - j.val ≤ q - 1 := by omega
          simpa only [augmentedAgentPhiNat, if_neg hp, activeAgentPhiNat, hb,
            if_pos hj] using
            (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 4) he)
        · simp [augmentedAgentPhiNat, hp, activeAgentPhiNat, hb, hj]

theorem four_pred_mul (k : ℕ) (hk : 1 ≤ k) :
    (4 : ℕ) ^ (k - 1) * 4 = 4 ^ k := by
  simpa only [Nat.sub_add_cancel hk] using (pow_succ (4 : ℕ) (k - 1)).symm

theorem pair_atoms_le_cutoff (h q : ℕ) (hh : 1 ≤ h) (hq : 1 ≤ q)
    (c : Cfg L 256) (hc : PotentialDomain c)
    (hold : h ≤ q ∨ augmentedPhiNat (h - q) c = 0)
    (s : AgentState L 256) (hs : s ∈ c)
    (t : AgentState L 256) (ht : t ∈ c) :
    augmentedAgentPhiNat h s + augmentedAgentPhiNat h t ≤ 4 ^ q := by
  by_cases hearly : h ≤ q
  · have hleft := augmented_atom_le h s (hc s hs)
    have hright := augmented_atom_le h t (hc t ht)
    have heq := four_pred_mul h hh
    have hpow : (4 : ℕ) ^ h ≤ 4 ^ q :=
      pow_le_pow_right₀ (by norm_num) hearly
    omega
  · have hz : augmentedPhiNat (h - q) c = 0 := hold.resolve_left hearly
    have hleft := atom_le_of_old_zero h q (by omega) s
      (old_agent_atom_zero (h - q) c hz s hs)
    have hright := atom_le_of_old_zero h q (by omega) t
      (old_agent_atom_zero (h - q) c hz t ht)
    have heq := four_pred_mul q hq
    omega

theorem pair_atoms_le_population_bound {n : ℕ}
    (hn : timePopulationThreshold ≤ n) (h : ℕ) (hh : 1 ≤ h)
    (c : Cfg L 256) (hc : PotentialDomain c)
    (hold : h ≤ oldCutoff n ∨ augmentedPhiNat (h - oldCutoff n) c = 0)
    (s : AgentState L 256) (hs : s ∈ c)
    (t : AgentState L 256) (ht : t ∈ c) :
    (augmentedAgentPhiNat h s : ℝ) + (augmentedAgentPhiNat h t : ℝ) ≤ atomBound n := by
  have hq := oldCutoff_lower hn
  have hpair := pair_atoms_le_cutoff h (oldCutoff n) hh (by omega) c hc hold s hs t ht
  have hreal :
      (augmentedAgentPhiNat h s : ℝ) + (augmentedAgentPhiNat h t : ℝ) ≤
        (4 : ℝ) ^ oldCutoff n := by exact_mod_cast hpair
  exact hreal.trans (old_atom_bound hn)

/-- The atom hypothesis in the actual logarithmic tail is now a consequence
of a concrete extinct old potential, or the early-hour cutoff inequality. -/
theorem logGate_of_old_extinction {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (h : ℕ) (hh : 1 ≤ h)
    (c : Cfg L 256) (hc : PotentialDomain c) (hpop : c.card = n)
    (hready : (17 / 100 : ℝ) * M ≤ (readyZeroCount h c : ℝ))
    (hold : h ≤ oldCutoff n ∨ augmentedPhiNat (h - oldCutoff n) c = 0) :
    LogGate n M h c :=
  ⟨hc, hpop, hready,
    fun s hs t ht => pair_atoms_le_population_bound hn h hh c hc hold s hs t ht⟩

end Ripple.PopulationProtocol.ExactMajority.AveragingAtomBound

end

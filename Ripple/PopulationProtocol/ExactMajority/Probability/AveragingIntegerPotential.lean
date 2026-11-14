import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingMixedPotentialTransitions

/-!
# The integer-valued augmented averaging potential

The rational ledger has an exact natural-number representation, including
twice the pending mass. This supplies the integer-valued process needed by
extinction estimates and identifies it with the literal readout potential
after initialization. It proves no conditional drift or extinction tail.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingIntegerPotential

open TimeTheorem StageEventSpec P3DeterministicAlgebra
open AveragingMixedAlgebra AveragingMixedLedgers

variable {L K : ℕ}

def activeAgentPhiNat (h : ℕ) (a : AgentState L K) : ℕ :=
  match a.bias with
  | .zero => 0
  | .dyadic _ j => if j.val < h then 4 ^ (h - 1 - j.val) else 0

def augmentedAgentPhiNat (h : ℕ) (a : AgentState L K) : ℕ :=
  if a.phase.val < 3 then
    2 * 4 ^ (h - 1) * (AgentState.smallBiasInt a).natAbs
  else activeAgentPhiNat h a

def augmentedPhiNat (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  (c.map (augmentedAgentPhiNat h)).sum

theorem activeAgentPhiNat_cast (h : ℕ) (a : AgentState L K) :
    (activeAgentPhiNat h a : ℚ) = agentPhiAboveQ h a := by
  cases hb : a.bias with
  | zero =>
      simp [activeAgentPhiNat, agentPhiAboveQ, phiBiasWeightQ, hb]
  | dyadic sigma j =>
      by_cases hj : j.val < h <;>
        simp [activeAgentPhiNat, agentPhiAboveQ, phiBiasWeightQ, hb, hj]

/-- This identity does not need a safety assumption; safety is needed for
the actual mixed-transition inequalities that consume it. -/
theorem augmentedAgentPhiNat_cast (h : ℕ) (a : AgentState L K) :
    (augmentedAgentPhiNat h a : ℚ) = augmentedAgentPhi h a := by
  by_cases hp : a.phase.val < 3
  · simp only [augmentedAgentPhiNat, augmentedAgentPhi, if_pos hp,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pendingPotentialWeight,
      PhaseTwoSparse.rational_natAbs]
  · simpa only [augmentedAgentPhiNat, augmentedAgentPhi, if_neg hp] using
      activeAgentPhiNat_cast h a

theorem augmentedPhiNat_cast (h : ℕ) (c : Config (AgentState L K)) :
    (augmentedPhiNat h c : ℚ) = augmentedPhi h c := by
  induction c using Multiset.induction_on with
  | empty => simp [augmentedPhiNat, augmentedPhi]
  | cons a c ih =>
      have hadd := congrArg₂ (fun x y : ℚ => x + y)
        (augmentedAgentPhiNat_cast h a) ih
      simpa only [augmentedPhiNat, augmentedPhi, Multiset.map_cons,
        Multiset.sum_cons, Nat.cast_add] using hadd

theorem augmentedPhiNat_zero_iff (h : ℕ) (c : Config (AgentState L K)) :
    augmentedPhiNat h c = 0 ↔ augmentedPhi h c = 0 := by
  constructor
  · intro hz
    rw [← augmentedPhiNat_cast, hz] <;> norm_num
  · intro hz
    have hcast : (augmentedPhiNat h c : ℚ) = 0 :=
      (augmentedPhiNat_cast h c).trans hz
    exact_mod_cast hcast

/-- The complete mixed-transition monotonicity also holds for the exact
natural-number potential on the actual trace. -/
theorem trace_augmentedPhiNat_le
    (h : ℕ) (hh : 1 ≤ h)
    (init : Cfg L 256) (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    augmentedPhiNat h (trace init ω t) ≤
      augmentedPhiNat h (trace init ω s) := by
  have hrat :=
    AveragingMixedPotentialTransitions.trace_augmentedPhi_le
      h hh init ω s t hst hrange hsafe hcarrier
  have hcast :
      (augmentedPhiNat h (trace init ω t) : ℚ) ≤
        (augmentedPhiNat h (trace init ω s) : ℚ) := by
    simpa only [augmentedPhiNat_cast] using hrat
  exact_mod_cast hcast

open Classical in
theorem activeAgentPhiNat_eq_role_filtered
    (h : ℕ) (a : AgentState L K)
    (hcarrier : a.role ≠ .main → a.bias = .zero) :
    activeAgentPhiNat h a =
      if a.role = .main then
        match a.bias with
        | .zero => 0
        | .dyadic _ j => if j.val < h then 4 ^ (h - j.val - 1) else 0
      else 0 := by
  by_cases hm : a.role = .main
  · rw [if_pos hm]
    cases hb : a.bias with
    | zero => simp [activeAgentPhiNat, hb]
    | dyadic sigma j =>
        have hexp : h - 1 - j.val = h - j.val - 1 := by omega
        simp [activeAgentPhiNat, hb, hexp]
  · simp [activeAgentPhiNat, if_neg hm, hcarrier hm]

/-- After initialization and with neutral non-Mains, the integer ledger is
exactly the potential appearing in SmallReadout. -/
theorem augmentedPhiNat_eq_shallowPotential {n : ℕ}
    (h : ℕ) (c : InputCfg n)
    (hphase : ∀ a ∈ c, 3 ≤ a.phase.val)
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.bias = .zero) :
    augmentedPhiNat h c = shallowPotential h c := by
  classical
  revert hphase hcarrier
  induction c using Multiset.induction_on with
  | empty =>
      intro _ _
      simp [augmentedPhiNat, shallowPotential]
  | cons a c ih =>
      intro hphase hcarrier
      have ha : a ∈ a ::ₘ c := Multiset.mem_cons_self _ _
      have hnot : ¬ a.phase.val < 3 := by
        have := hphase a ha
        omega
      have hhead :
          augmentedAgentPhiNat h a =
            if a.role = .main then
              match a.bias with
              | .zero => 0
              | .dyadic _ j => if j.val < h then 4 ^ (h - j.val - 1) else 0
            else 0 := by
        rw [augmentedAgentPhiNat, if_neg hnot]
        refine (activeAgentPhiNat_eq_role_filtered h a (hcarrier a ha)).trans ?_
        split_ifs <;> (cases hb : a.bias <;> simp)
      have htail := ih
        (fun b hb => hphase b (Multiset.mem_cons_of_mem hb))
        (fun b hb => hcarrier b (Multiset.mem_cons_of_mem hb))
      simpa only [augmentedPhiNat, shallowPotential, Multiset.map_cons,
        Multiset.sum_cons] using congrArg₂ (fun x y : ℕ => x + y) hhead htail

theorem readout_potential_of_augmented_bound {n : ℕ}
    (ell M : ℕ) (c : InputCfg n)
    (hphase : ∀ a ∈ c, 3 ≤ a.phase.val)
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.bias = .zero)
    (hbound : (1000 : ℚ) * augmentedPhi ell c ≤ (M : ℚ)) :
    1000 * shallowPotential ell c ≤ M := by
  have hcast : (1000 : ℚ) * (augmentedPhiNat ell c : ℚ) ≤ (M : ℚ) := by
    simpa only [augmentedPhiNat_cast] using hbound
  have hnat : 1000 * augmentedPhiNat ell c ≤ M := by exact_mod_cast hcast
  rwa [augmentedPhiNat_eq_shallowPotential ell c hphase hcarrier] at hnat

end Ripple.PopulationProtocol.ExactMajority.AveragingIntegerPotential

end

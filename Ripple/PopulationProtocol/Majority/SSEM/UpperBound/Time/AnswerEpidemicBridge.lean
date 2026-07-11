import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.DrainNoWakeTrace
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.EpidemicMechanics

namespace SSEM

open scoped BigOperators ENNReal

/-- The explicit binomial tail from the unconditional no-wake drain bound. -/
noncomputable abbrev drainNoWakeTail (n K d : ℕ) : ENNReal :=
  (n : ENNReal) * (Nat.choose K d : ENNReal) *
    (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ d)

private theorem probNotHitBy_ge_half_of_ProbHitWithin_le_half
    {Q X Y : Type*} {n : ℕ}
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (t : ℕ)
    (hHit :
      Probability.ProbHitWithin P hn C₀ Goal t ≤ (2 : ENNReal)⁻¹) :
    (2 : ENNReal)⁻¹ ≤ Probability.probNotHitBy P hn C₀ Goal t := by
  let hit := Probability.ProbHitWithin P hn C₀ Goal t
  let miss := Probability.probNotHitBy P hn C₀ Goal t
  have hsum : hit + miss = 1 := by
    simpa [hit, miss, Probability.ProbHitWithin] using
      Probability.probHitBy_add_probNotHitBy P hn C₀ Goal t
  have hle :
      (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ ≤
        (2 : ENNReal)⁻¹ + miss := by
    calc
      (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹
          = 1 := ENNReal.inv_two_add_inv_two
      _ = hit + miss := hsum.symm
      _ ≤ (2 : ENNReal)⁻¹ + miss := by
        simpa [hit, add_comm, add_left_comm, add_assoc] using
          add_le_add_right hHit miss
  have hhalf_ne_top : ((2 : ENNReal)⁻¹) ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]
    norm_num
  exact (ENNReal.add_le_add_iff_left hhalf_ne_top).mp hle

/-- Numeric complement of the unconditional drain bound: if the explicit
tail is at most `1/2`, then no wake occurs through the window with probability
at least `1/2`. -/
theorem no_wake_prob_ge_half
    {n Rmax Emax Dmax K d : ℕ}
    (hn : 0 < n) (hn2 : 2 ≤ n) (hd_pos : 0 < d) (hd : d ≤ Dmax)
    {C₀ : Config (AgentState n) Opinion n}
    (hAll : AllAgentsResetting C₀)
    (hDormantBudget :
      ∀ a : Fin n, (C₀ a).1.resetcount = 0 → d ≤ (C₀ a).1.delaytimer)
    (hTail : drainNoWakeTail n K d ≤ (2 : ENNReal)⁻¹) :
    (2 : ENNReal)⁻¹ ≤
      Probability.probNotHitBy
        (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C₀ SomeAgentAwake K := by
  let P : Protocol (AgentState n) Opinion Output :=
    PEMProtocol n 1 Rmax Emax Dmax hn
  have hDrain :
      Probability.ProbHitWithin P hn2 C₀ SomeAgentAwake K ≤
        drainNoWakeTail n K d := by
    simpa [P, drainNoWakeTail] using
      drain_probHitWithin_le_choose_unconditional
        (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (K := K) (d := d) (C₀ := C₀) hn hn2 hd_pos hd
        hAll hDormantBudget
  exact
    probNotHitBy_ge_half_of_ProbHitWithin_le_half P hn2 C₀
      SomeAgentAwake K (hDrain.trans hTail)

/-- Standard one-rumor epidemic-speed lower-bound hypothesis.

This is the external epidemic-speed building block, explicitly separate from
the Kanaya/[12] bound. -/
def StandardEpidemicFastHypothesisPEM
    (n Rmax Emax Dmax K : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n)
    (pE : ENNReal) : Prop :=
  ∀ {m : Answer} {C : Config (AgentState n) Opinion n},
    EpidemicRegion m C →
      pE ≤
        Probability.ProbHitWithin
          (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C
          (fun D => EpidemicPhiGoal m D ∨ SomeAgentAwake D) K

private theorem ProbHitWithin_left_ge_of_or_ge_add_and_right_le
    {Q X Y : Type*} {n : ℕ}
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n)
    (A B : Config Q X n → Prop) (t : ℕ)
    {p q : ENNReal} (hq_ne_top : q ≠ ⊤)
    (hor :
      p + q ≤
        Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t)
    (hB : Probability.ProbHitWithin P hn C₀ B t ≤ q) :
    p ≤ Probability.ProbHitWithin P hn C₀ A t := by
  let x := Probability.ProbHitWithin P hn C₀ A t
  let y := Probability.ProbHitWithin P hn C₀ B t
  have hOr :
      Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t ≤ x + y := by
    simpa [x, y] using Probability.ProbHitWithin_or_le_add P hn C₀ A B t
  have hpq : p + q ≤ x + q := by
    calc
      p + q
          ≤ Probability.ProbHitWithin P hn C₀ (fun C => A C ∨ B C) t := hor
      _ ≤ x + y := hOr
      _ ≤ x + q := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left (show y ≤ q from hB) x
  rw [add_comm p q, add_comm x q] at hpq
  exact (ENNReal.add_le_add_iff_left hq_ne_top).mp hpq

/-- Answer-epidemic bridge from a fresh all-Resetting start.

The final numeric tail hypothesis is matched to the bridge constant
`pE / 2`; this is the form needed to turn the epidemic lower bound and the
wake union bound into an intersection lower bound. -/
theorem answer_epidemic_bridge_from_fresh_resetting
    {n Rmax Emax Dmax K d : ℕ}
    (hn : 0 < n) (hn2 : 2 ≤ n) (hd_pos : 0 < d) (hd : d ≤ Dmax)
    {C₀ : Config (AgentState n) Opinion n} {m : Answer} {pE : ENNReal}
    (hAll : AllAgentsResetting C₀)
    (hDormantBudget :
      ∀ a : Fin n, (C₀ a).1.resetcount = 0 → d ≤ (C₀ a).1.delaytimer)
    (hRegion₀ : EpidemicRegion m C₀)
    (hTail : drainNoWakeTail n K d ≤ pE / 2)
    (epidemicFast :
      StandardEpidemicFastHypothesisPEM
        n Rmax Emax Dmax K hn hn2 pE) :
    pE / 2 ≤
      Probability.ProbHitWithin
        (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C₀
        (fun D => EpidemicPhiGoal m D ∧ AllAgentsResetting D) K := by
  let P : Protocol (AgentState n) Opinion Output :=
    PEMProtocol n 1 Rmax Emax Dmax hn
  let Target : Config (AgentState n) Opinion n → Prop :=
    fun D => EpidemicPhiGoal m D ∧ AllAgentsResetting D
  let Bad : Config (AgentState n) Opinion n → Prop := SomeAgentAwake
  have hDrain :
      Probability.ProbHitWithin P hn2 C₀ Bad K ≤
        drainNoWakeTail n K d := by
    simpa [P, Bad, drainNoWakeTail] using
      drain_probHitWithin_le_choose_unconditional
        (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (K := K) (d := d) (C₀ := C₀) hn hn2 hd_pos hd
        hAll hDormantBudget
  have hBad : Probability.ProbHitWithin P hn2 C₀ Bad K ≤ pE / 2 :=
    hDrain.trans hTail
  have hEpidemic :
      pE ≤
        Probability.ProbHitWithin P hn2 C₀
          (fun D => EpidemicPhiGoal m D ∨ Bad D) K := by
    simpa [P, Bad] using epidemicFast hRegion₀
  have hGoalOrBadToTargetOrBad :
      ∀ D : Config (AgentState n) Opinion n,
        EpidemicPhiGoal m D ∨ Bad D → Target D ∨ Bad D := by
    intro D hGoalOrBad
    rcases hGoalOrBad with hGoal | hAwake
    · by_cases hAwake : Bad D
      · exact Or.inr hAwake
      · exact Or.inl
          ⟨hGoal, (not_someAgentAwake_iff_allAgentsResetting D).mp hAwake⟩
    · exact Or.inr hAwake
  have hGoalLeOr :
      Probability.ProbHitWithin P hn2 C₀
          (fun D => EpidemicPhiGoal m D ∨ Bad D) K ≤
        Probability.ProbHitWithin P hn2 C₀ (fun D => Target D ∨ Bad D) K :=
    Probability.ProbHitWithin_mono_goal P hn2 C₀
      (fun D => EpidemicPhiGoal m D ∨ Bad D)
      (fun D => Target D ∨ Bad D)
      hGoalOrBadToTargetOrBad K
  have hsplit : pE / 2 + pE / 2 = pE := by
    simp
  have hor :
      pE / 2 + pE / 2 ≤
        Probability.ProbHitWithin P hn2 C₀ (fun D => Target D ∨ Bad D) K := by
    rw [hsplit]
    exact hEpidemic.trans hGoalLeOr
  have hpE_le_one : pE ≤ 1 :=
    hEpidemic.trans
      (Probability.ProbHitWithin_le_one P hn2 C₀
        (fun D => EpidemicPhiGoal m D ∨ Bad D) K)
  have hhalf_le_one : pE / 2 ≤ 1 := by
    have hhalf_le_pE : pE / 2 ≤ pE := by
      calc
        pE / 2 ≤ pE / 2 + pE / 2 :=
          (le_self_add : pE / 2 ≤ pE / 2 + pE / 2)
        _ = pE := hsplit
    exact hhalf_le_pE.trans hpE_le_one
  have hhalf_ne_top : pE / 2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hhalf_le_one
  exact
    ProbHitWithin_left_ge_of_or_ge_add_and_right_le P hn2 C₀
      Target Bad K hhalf_ne_top hor hBad

end SSEM

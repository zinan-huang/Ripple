/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase6PhiDropSum

The scheduler-level counting argument for Doty et al.'s base-4 Phase-6
potential.  Every sampled Reserve at an hour above the target band can split
every Main counted by `phiMass`.  Each ordered orientation loses at least half
of the Main's base-4 weight; summing the two disjoint orientations recovers one
full copy of that weight.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiDrift
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase678ReadySurvival

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6PhiDropSum

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The state finset supporting the base-4 Phase-6 potential at level `l`. -/
def highPhiStates (l : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter (Phase6Convergence.highSt (L := L) (K := K) l)

/-- The base-4 potential is the multiplicity-weighted sum over its support. -/
theorem sum_highPhiStates_eq_phiMass (l : ℕ) (c : Config (AgentState L K)) :
    ∑ a ∈ highPhiStates (L := L) (K := K) l,
        c.count a * Phase6PhiPotential.agentPhiW (L := L) (K := K) l a =
      Phase6PhiPotential.phiMass (L := L) (K := K) l c := by
  rw [Phase6PhiDrift.phiMass_eq_sum_count_agentPhiW]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  have hnot : ¬ Phase6Convergence.highSt (L := L) (K := K) l a := by
    simpa [highPhiStates] using ha
  rw [Phase6PhiPotential.agentPhiW_eq_zero_of_not_high (L := L) (K := K) l a hnot]
  simp

/-- Two-agent expansion of the base-4 potential. -/
theorem phiMass_pair_eq (l : ℕ) (x y : AgentState L K) :
    Phase6PhiPotential.phiMass (L := L) (K := K) l {x, y} =
      Phase6PhiPotential.agentPhiW (L := L) (K := K) l x +
        Phase6PhiPotential.agentPhiW (L := L) (K := K) l y := by
  exact Phase6PhiDrift.phiMass_pair (L := L) (K := K) l x y

/-- Sampled Reserves and positive-`phi` Mains are disjoint state classes. -/
theorem reserveAtHour6_disjoint_highPhiStates
    (l : ℕ) (i : Fin (L + 1)) :
    Disjoint
      (Phase6Convergence.reserveAtHour6 (L := L) (K := K) i)
      (highPhiStates (L := L) (K := K) l) := by
  rw [Finset.disjoint_left]
  intro a hra hha
  simp only [Phase6Convergence.reserveAtHour6, Finset.mem_filter] at hra
  simp only [highPhiStates, Finset.mem_filter] at hha
  exact absurd hha.2.1 (by simp [hra.2.1])

/-- The scheduler probability is symmetric under reversal of the two states. -/
theorem interactionProb_comm (c : Config (AgentState L K))
    (s t : AgentState L K) :
    c.interactionProb s t = c.interactionProb t s := by
  unfold Config.interactionProb Config.interactionCount
  by_cases h : s = t
  · subst h
    rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp [mul_comm]

/-! ## Pair-level half-drop and its lift to configurations -/

/-- With the Reserve first, the phase-6 dispatch cuts the pair's base-4
potential by at least one half. -/
theorem Phase6Transition_phi_pair_half
    (l : ℕ) (r m : AgentState L K) {σ : Sign} {j : Fin (L + 1)}
    (hrR : r.role = Role.reserve) (hmM : m.role = Role.main)
    (hb : m.bias = Bias.dyadic σ j) (hjlt : j.val < l)
    (hne : r.hour.val ≠ L) (hgt : r.hour.val > j.val) (hlt : j.val < L)
    (hr6 : 6 ≤ r.phase.val) (hm6 : 6 ≤ m.phase.val) :
    2 * (Phase6PhiPotential.agentPhiW (L := L) (K := K) l
            (Phase6Transition L K r m).1 +
          Phase6PhiPotential.agentPhiW (L := L) (K := K) l
            (Phase6Transition L K r m).2)
      ≤ Phase6PhiPotential.agentPhiW (L := L) (K := K) l r +
          Phase6PhiPotential.agentPhiW (L := L) (K := K) l m := by
  have hmbias : m.bias ≠ Bias.zero := by
    rw [hb]
    exact fun h => by cases h
  unfold Phase6Transition
  simp only
  set s1 :=
    (if r.role = Role.reserve ∧ m.role = Role.main ∧ m.bias ≠ Bias.zero then
      (doSplit L K r m).1
    else if m.role = Role.reserve ∧ r.role = Role.main ∧ r.bias ≠ Bias.zero then
      (doSplit L K m r).2
    else r) with hs1def
  set t1 :=
    (if r.role = Role.reserve ∧ m.role = Role.main ∧ m.bias ≠ Bias.zero then
      (doSplit L K r m).2
    else if m.role = Role.reserve ∧ r.role = Role.main ∧ r.bias ≠ Bias.zero then
      (doSplit L K m r).1
    else m) with ht1def
  have hs1eq : s1 = (doSplit L K r m).1 := by
    rw [hs1def, if_pos ⟨hrR, hmM, hmbias⟩]
  have ht1eq : t1 = (doSplit L K r m).2 := by
    rw [ht1def, if_pos ⟨hrR, hmM, hmbias⟩]
  have hs1p : 5 ≤ s1.phase.val := by
    rw [hs1eq, Phase6Convergence.doSplit_phase_fst_eq (L := L) (K := K) r m]
    omega
  have ht1p : 5 ≤ t1.phase.val := by
    rw [ht1eq, Phase6Convergence.doSplit_phase_snd_eq (L := L) (K := K) r m]
    omega
  rw [Phase6PhiDrift.clockBranch_agentPhiW_eq (L := L) (K := K) l s1 hs1p,
      Phase6PhiDrift.clockBranch_agentPhiW_eq (L := L) (K := K) l t1 ht1p,
      hs1eq, ht1eq]
  exact Phase6PhiPotential.doSplit_phi_pair_half (L := L) (K := K)
    l r m hrR hmM hb hjlt hne hgt hlt

/-- The same half-drop with the Main first and the Reserve second. -/
theorem Phase6Transition_phi_pair_half_rev
    (l : ℕ) (r m : AgentState L K) {σ : Sign} {j : Fin (L + 1)}
    (hrR : r.role = Role.reserve) (hmM : m.role = Role.main)
    (hb : m.bias = Bias.dyadic σ j) (hjlt : j.val < l)
    (hne : r.hour.val ≠ L) (hgt : r.hour.val > j.val) (hlt : j.val < L)
    (hr6 : 6 ≤ r.phase.val) (hm6 : 6 ≤ m.phase.val) :
    2 * (Phase6PhiPotential.agentPhiW (L := L) (K := K) l
            (Phase6Transition L K m r).1 +
          Phase6PhiPotential.agentPhiW (L := L) (K := K) l
            (Phase6Transition L K m r).2)
      ≤ Phase6PhiPotential.agentPhiW (L := L) (K := K) l m +
          Phase6PhiPotential.agentPhiW (L := L) (K := K) l r := by
  have hmbias : m.bias ≠ Bias.zero := by
    rw [hb]
    exact fun h => by cases h
  have hnotfirst : ¬ (m.role = Role.reserve ∧ r.role = Role.main ∧ r.bias ≠ Bias.zero) := by
    intro h
    rw [hmM] at h
    exact absurd h.1 (by decide)
  unfold Phase6Transition
  simp only
  set s1 :=
    (if m.role = Role.reserve ∧ r.role = Role.main ∧ r.bias ≠ Bias.zero then
      (doSplit L K m r).1
    else if r.role = Role.reserve ∧ m.role = Role.main ∧ m.bias ≠ Bias.zero then
      (doSplit L K r m).2
    else m) with hs1def
  set t1 :=
    (if m.role = Role.reserve ∧ r.role = Role.main ∧ r.bias ≠ Bias.zero then
      (doSplit L K m r).2
    else if r.role = Role.reserve ∧ m.role = Role.main ∧ m.bias ≠ Bias.zero then
      (doSplit L K r m).1
    else r) with ht1def
  have hs1eq : s1 = (doSplit L K r m).2 := by
    rw [hs1def, if_neg hnotfirst, if_pos ⟨hrR, hmM, hmbias⟩]
  have ht1eq : t1 = (doSplit L K r m).1 := by
    rw [ht1def, if_neg hnotfirst, if_pos ⟨hrR, hmM, hmbias⟩]
  have hs1p : 5 ≤ s1.phase.val := by
    rw [hs1eq, Phase6Convergence.doSplit_phase_snd_eq (L := L) (K := K) r m]
    omega
  have ht1p : 5 ≤ t1.phase.val := by
    rw [ht1eq, Phase6Convergence.doSplit_phase_fst_eq (L := L) (K := K) r m]
    omega
  rw [Phase6PhiDrift.clockBranch_agentPhiW_eq (L := L) (K := K) l s1 hs1p,
      Phase6PhiDrift.clockBranch_agentPhiW_eq (L := L) (K := K) l t1 ht1p,
      hs1eq, ht1eq]
  simpa [add_comm] using
    (Phase6PhiPotential.doSplit_phi_pair_half (L := L) (K := K)
      l r m hrR hmM hb hjlt hne hgt hlt)

/-- Lift a pair half-drop through removal and reinsertion of the scheduled pair. -/
theorem phiMass_stepOrSelf_pair_half_of_transition
    (l n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hpair :
      2 * (Phase6PhiPotential.agentPhiW (L := L) (K := K) l
              (Phase6Transition L K s t).1 +
            Phase6PhiPotential.agentPhiW (L := L) (K := K) l
              (Phase6Transition L K s t).2)
        ≤ Phase6PhiPotential.agentPhiW (L := L) (K := K) l s +
            Phase6PhiPotential.agentPhiW (L := L) (K := K) l t) :
    2 * Phase6PhiPotential.phiMass (L := L) (K := K) l
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) +
        (Phase6PhiPotential.agentPhiW (L := L) (K := K) l s +
          Phase6PhiPotential.agentPhiW (L := L) (K := K) l t)
      ≤ 2 * Phase6PhiPotential.phiMass (L := L) (K := K) l c := by
  obtain ⟨_, hph⟩ := hInv
  have hsmem : s ∈ c :=
    Multiset.mem_of_le (show ({s, t} : Multiset (AgentState L K)) ≤ c from happ) (by simp)
  have htmem : t ∈ c :=
    Multiset.mem_of_le (show ({s, t} : Multiset (AgentState L K)) ≤ c from happ) (by simp)
  have hs6 : s.phase.val = 6 := hph s hsmem
  have ht6 : t.phase.val = 6 := hph t htmem
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hcstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have htr : Transition L K s t = Phase6Transition L K s t :=
    Phase6Convergence.Transition_eq_Phase6Transition_of_phase6
      (L := L) (K := K) s t hs6 ht6
  have hcsplit : c = (c - {s, t}) + {s, t} :=
    (tsub_add_cancel_of_le hsub).symm
  rw [hcstep, Phase6PhiDrift.phiMass_add]
  have hcval :
      Phase6PhiPotential.phiMass (L := L) (K := K) l c =
        Phase6PhiPotential.phiMass (L := L) (K := K) l (c - {s, t}) +
          (Phase6PhiPotential.agentPhiW (L := L) (K := K) l s +
            Phase6PhiPotential.agentPhiW (L := L) (K := K) l t) := by
    conv_lhs => rw [hcsplit]
    rw [Phase6PhiDrift.phiMass_add, phiMass_pair_eq]
  rw [htr, phiMass_pair_eq, hcval]
  omega

/-! ## The two-orientation weighted rectangle -/

/-- Multiplicity-weighted interaction counts factor over a disjoint rectangle. -/
theorem sum_agentPhiW_interactionCount_cross
    (l : ℕ) (c : Config (AgentState L K))
    (A B : Finset (AgentState L K))
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) :
    (∑ p ∈ A ×ˢ B,
        Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 *
          c.interactionCount p.1 p.2) =
      (∑ a ∈ A, c.count a) *
        (∑ b ∈ B,
          c.count b * Phase6PhiPotential.agentPhiW (L := L) (K := K) l b) := by
  rw [Finset.sum_product]
  calc
    (∑ a ∈ A, ∑ b ∈ B,
        Phase6PhiPotential.agentPhiW (L := L) (K := K) l b *
          c.interactionCount a b) =
        ∑ a ∈ A, ∑ b ∈ B,
          c.count a *
            (c.count b * Phase6PhiPotential.agentPhiW (L := L) (K := K) l b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      unfold Config.interactionCount
      rw [if_neg (hdisj a ha b hb)]
      ring
    _ = (∑ a ∈ A, c.count a) *
        (∑ b ∈ B,
          c.count b * Phase6PhiPotential.agentPhiW (L := L) (K := K) l b) := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- The base-4 weighted scheduler mass of the Reserve/high-Main rectangle. -/
theorem sum_phi_interactionProb_reserve_high
    (l n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n) (i : Fin (L + 1)) :
    (∑ p ∈
        Phase6Convergence.reserveAtHour6 (L := L) (K := K) i ×ˢ
          highPhiStates (L := L) (K := K) l,
        (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) *
          c.interactionProb p.1 p.2) =
      (((Phase6Convergence.reserveAtHour6 (L := L) (K := K) i).sum c.count : ℕ) :
          ℝ≥0∞) *
        (Phase6PhiPotential.phiMass (L := L) (K := K) l c : ℝ≥0∞) /
          ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  let A := Phase6Convergence.reserveAtHour6 (L := L) (K := K) i
  let B := highPhiStates (L := L) (K := K) l
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a ≠ b := by
    intro a ha b hb hab
    subst b
    exact Finset.disjoint_left.mp
      (reserveAtHour6_disjoint_highPhiStates (L := L) (K := K) l i)
      (by simpa [A] using ha) (by simpa [B] using hb)
  have hcount := sum_agentPhiW_interactionCount_cross
    (L := L) (K := K) l c A B hAB
  have htp : c.totalPairs = n * (n - 1) := by
    rw [Config.totalPairs, hcard]
  change (∑ p ∈ A ×ˢ B,
      (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) *
        c.interactionProb p.1 p.2) = _
  simp only [Config.interactionProb, div_eq_mul_inv]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have hcast :
      (∑ p ∈ A ×ˢ B,
          (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) *
            (c.interactionCount p.1 p.2 : ℝ≥0∞)) =
        ((∑ p ∈ A ×ˢ B,
            Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 *
              c.interactionCount p.1 p.2 : ℕ) : ℝ≥0∞) := by
    norm_cast
  rw [hcast, hcount, Nat.cast_mul, htp, sum_highPhiStates_eq_phiMass]

/-- Real and `ENNReal` presentations of the Phase-6 scheduler rate agree. -/
theorem ofReal_phase6_rate_eq (n K₀ : ℕ) (hn : 2 ≤ n) :
    ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) =
      (K₀ : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  have hden_pos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n - 1)
  have hdenR : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← hdenR, ← ENNReal.ofReal_natCast K₀,
      ← ENNReal.ofReal_natCast (n * (n - 1)),
      ENNReal.ofReal_div_of_pos hden_pos]

/-- A live hour-`i` Reserve floor lower-bounds the scheduler-weighted base-4
drop by `K₀/(n(n-1))` times the current potential.  This is the persistent
consumer form used by the fuel ledger; no Phase-5 sampling predicate is kept
in the working invariant. -/
theorem phase6_phi_dropSum_floor_of_reserveFloor
    (l n : ℕ) (hn : 2 ≤ n)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (c : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hFloor : K₀ ≤
      (Phase6Convergence.reserveAtHour6 (L := L) (K := K) i).sum c.count) :
    ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) *
        (Phase6PhiPotential.phiMass (L := L) (K := K) l c : ℝ≥0∞) ≤
      WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
        (fun b => Phase6PhiPotential.phiMass (L := L) (K := K) l b) c := by
  classical
  let A := Phase6Convergence.reserveAtHour6 (L := L) (K := K) i
  let B := highPhiStates (L := L) (K := K) l
  let Φ : Config (AgentState L K) → ℕ :=
    fun b => Phase6PhiPotential.phiMass (L := L) (K := K) l b
  let drop : AgentState L K × AgentState L K → ℝ≥0∞ := fun p =>
    (Φ c : ℝ≥0∞) -
      (Φ (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞)
  let R₁ := A ×ˢ B
  let R₂ := B ×ˢ A
  have hAB : Disjoint A B := by
    exact reserveAtHour6_disjoint_highPhiStates (L := L) (K := K) l i
  have hRdisj : Disjoint R₁ R₂ := by
    exact Finset.disjoint_product.mpr (Or.inl hAB)
  have hterm : ∀ p ∈ R₁,
      (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) *
          c.interactionProb p.1 p.2 ≤
        drop p * c.interactionProb p.1 p.2 +
          drop (p.2, p.1) * c.interactionProb p.2 p.1 := by
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hrmem, hmmem⟩ := hp
    have hrmemA : p.1 ∈ A := hrmem
    have hmmemB : p.2 ∈ B := hmmem
    simp only [A, Phase6Convergence.reserveAtHour6, Finset.mem_filter] at hrmem
    simp only [B, highPhiStates, Finset.mem_filter] at hmmem
    obtain ⟨_, hrR, hrh⟩ := hrmem
    obtain ⟨_, hmM, σ, j, hb, hjlt⟩ := hmmem
    have hneState : p.1 ≠ p.2 := by
      intro heq
      have hp1B : p.1 ∈ B := by
        rw [heq]
        exact hmmemB
      exact Finset.disjoint_left.mp hAB hrmemA hp1B
    by_cases hcr : 1 ≤ c.count p.1
    · by_cases hcm : 1 ≤ c.count p.2
      · have hrin : p.1 ∈ c := Multiset.one_le_count_iff_mem.mp hcr
        have hmin : p.2 ∈ c := Multiset.one_le_count_iff_mem.mp hcm
        have happ₁ : Protocol.Applicable c p.1 p.2 :=
          Phase5Convergence.applicable_of_mem_distinct5 hrin hmin hneState
        have happ₂ : Protocol.Applicable c p.2 p.1 :=
          Phase5Convergence.applicable_of_mem_distinct5 hmin hrin hneState.symm
        have hrphase : p.1.phase.val = 6 := hInv.2 p.1 hrin
        have hmphase : p.2.phase.val = 6 := hInv.2 p.2 hmin
        have hgt : p.1.hour.val > j.val := by
          rw [hrh]
          omega
        have hne : p.1.hour.val ≠ L := by
          rw [hrh]
          exact hhne
        have hlt : j.val < L := by omega
        have hp1 := phiMass_stepOrSelf_pair_half_of_transition
          (L := L) (K := K) l n c hInv p.1 p.2 happ₁
          (Phase6Transition_phi_pair_half (L := L) (K := K)
            l p.1 p.2 hrR hmM hb hjlt hne hgt hlt (by omega) (by omega))
        have hp2 := phiMass_stepOrSelf_pair_half_of_transition
          (L := L) (K := K) l n c hInv p.2 p.1 happ₂
          (Phase6Transition_phi_pair_half_rev (L := L) (K := K)
            l p.1 p.2 hrR hmM hb hjlt hne hgt hlt (by omega) (by omega))
        have hrzero : Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.1 = 0 :=
          Phase6PhiPotential.agentPhiW_reserve (L := L) (K := K) l p.1 hrR
        rw [hrzero, zero_add] at hp1
        rw [hrzero, add_zero] at hp2
        have hdropNat :
            Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 ≤
              (Φ c - Φ (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2)) +
                (Φ c - Φ (Protocol.stepOrSelf (NonuniformMajority L K) c p.2 p.1)) := by
          dsimp [Φ] at hp1 hp2 ⊢
          omega
        have hdropE :
            (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) ≤
              drop p + drop (p.2, p.1) := by
          have hcast :
              (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) ≤
                ((Φ c - Φ (Protocol.stepOrSelf
                    (NonuniformMajority L K) c p.1 p.2) : ℕ) : ℝ≥0∞) +
                  ((Φ c - Φ (Protocol.stepOrSelf
                    (NonuniformMajority L K) c p.2 p.1) : ℕ) : ℝ≥0∞) := by
            exact_mod_cast hdropNat
          simpa only [drop, ENNReal.natCast_sub] using hcast
        calc
          (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) *
                c.interactionProb p.1 p.2
              ≤ (drop p + drop (p.2, p.1)) * c.interactionProb p.1 p.2 := by
                  gcongr
          _ = drop p * c.interactionProb p.1 p.2 +
                drop (p.2, p.1) * c.interactionProb p.2 p.1 := by
                  rw [add_mul, interactionProb_comm]
      · have hz : c.count p.2 = 0 := by omega
        have hprob : c.interactionProb p.1 p.2 = 0 := by
          simp [Config.interactionProb, Config.interactionCount, hneState, hz]
        rw [hprob, mul_zero]
        exact bot_le
    · have hz : c.count p.1 = 0 := by omega
      have hprob : c.interactionProb p.1 p.2 = 0 := by
        simp [Config.interactionProb, Config.interactionCount, hneState, hz]
      rw [hprob, mul_zero]
      exact bot_le
  have hrect :
      (∑ p ∈ R₁,
          (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) *
            c.interactionProb p.1 p.2) ≤
        (∑ p ∈ R₁, drop p * c.interactionProb p.1 p.2) +
          ∑ p ∈ R₂, drop p * c.interactionProb p.1 p.2 := by
    calc
      (∑ p ∈ R₁,
          (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) *
            c.interactionProb p.1 p.2)
          ≤ ∑ p ∈ R₁,
              (drop p * c.interactionProb p.1 p.2 +
                drop (p.2, p.1) * c.interactionProb p.2 p.1) := by
            exact Finset.sum_le_sum fun p hp => hterm p hp
      _ = (∑ p ∈ R₁, drop p * c.interactionProb p.1 p.2) +
          ∑ p ∈ R₁, drop (p.2, p.1) * c.interactionProb p.2 p.1 := by
            rw [Finset.sum_add_distrib]
      _ = (∑ p ∈ R₁, drop p * c.interactionProb p.1 p.2) +
          ∑ p ∈ R₂, drop p * c.interactionProb p.1 p.2 := by
            congr 1
            simp only [R₁, R₂, Finset.sum_product]
            rw [Finset.sum_comm]
  have hunion :
      (∑ p ∈ R₁, drop p * c.interactionProb p.1 p.2) +
          ∑ p ∈ R₂, drop p * c.interactionProb p.1 p.2 =
        ∑ p ∈ R₁ ∪ R₂, drop p * c.interactionProb p.1 p.2 := by
    exact (Finset.sum_union hRdisj).symm
  have huniv :
      (∑ p ∈ R₁ ∪ R₂, drop p * c.interactionProb p.1 p.2) ≤
        ∑ p : AgentState L K × AgentState L K,
          drop p * c.interactionProb p.1 p.2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro p _ _
    exact bot_le
  have hfloor : K₀ ≤ A.sum c.count := by
    exact hFloor
  have hrate :
      ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
        (((A.sum c.count : ℕ) : ℝ≥0∞)) /
          ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
    rw [ofReal_phase6_rate_eq n K₀ hn]
    gcongr
  have hweighted :
      ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) *
          (Φ c : ℝ≥0∞) ≤
        ∑ p ∈ R₁,
          (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) *
            c.interactionProb p.1 p.2 := by
    calc
      ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) *
            (Φ c : ℝ≥0∞)
          ≤ ((A.sum c.count : ℕ) : ℝ≥0∞) /
              ((n * (n - 1) : ℕ) : ℝ≥0∞) * (Φ c : ℝ≥0∞) := by
            gcongr
      _ = ∑ p ∈ R₁,
          (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) *
            c.interactionProb p.1 p.2 := by
        rw [show R₁ = A ×ˢ B from rfl]
        rw [sum_phi_interactionProb_reserve_high (L := L) (K := K)
          l n c hInv.1 i]
        simp only [A, Φ, div_eq_mul_inv]
        ac_rfl
  calc
    ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) *
          (Phase6PhiPotential.phiMass (L := L) (K := K) l c : ℝ≥0∞)
        = ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) *
            (Φ c : ℝ≥0∞) := rfl
    _ ≤ ∑ p ∈ R₁,
        (Phase6PhiPotential.agentPhiW (L := L) (K := K) l p.2 : ℝ≥0∞) *
          c.interactionProb p.1 p.2 := hweighted
    _ ≤ (∑ p ∈ R₁, drop p * c.interactionProb p.1 p.2) +
          ∑ p ∈ R₂, drop p * c.interactionProb p.1 p.2 := hrect
    _ = ∑ p ∈ R₁ ∪ R₂, drop p * c.interactionProb p.1 p.2 := hunion
    _ ≤ ∑ p : AgentState L K × AgentState L K,
        drop p * c.interactionProb p.1 p.2 := huniv
    _ = WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
        (fun b => Phase6PhiPotential.phiMass (L := L) (K := K) l b) c := rfl

/-- The Phase-5 sampled-floor wrapper for the direct Reserve-floor theorem. -/
theorem phase6_phi_dropSum_floor_of_reserveSampleGood
    (l n : ℕ) (hn : 2 ≤ n)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (c : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hPost : Phase5Convergence.ReserveSampleGood (L := L) (K := K) i K₀ c) :
    ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) *
        (Phase6PhiPotential.phiMass (L := L) (K := K) l c : ℝ≥0∞) ≤
      WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
        (fun b => Phase6PhiPotential.phiMass (L := L) (K := K) l b) c := by
  apply phase6_phi_dropSum_floor_of_reserveFloor
    (L := L) (K := K) l n hn i K₀ hhgt hhne c hInv
  exact PhaseFloors.phase6_reserve_floor_of_phase5Post i K₀ c hPost

/-- `Phase6DrainReady` wrapper for the full base-4 drop-sum floor. -/
theorem phase6_phi_dropSum_floor
    (n : ℕ) (σ : Sign) (l : ℕ) (hn : 2 ≤ n)
    (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (c : Config (AgentState L K))
    (hc : Phase678ReadySurvival.Phase6DrainReady
      (L := L) (K := K) n σ l hl1 hlL i K₀ c) :
    ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) *
        (Phase6PhiPotential.phiMass (L := L) (K := K) l c : ℝ≥0∞) ≤
      WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
        (fun b => Phase6PhiPotential.phiMass (L := L) (K := K) l b) c :=
  phase6_phi_dropSum_floor_of_reserveSampleGood
    (L := L) (K := K) l n hn i K₀ hhgt hhne c hc.win hc.sampled

/-- Assemble the drop-sum floor with the generic scheduler bridge. -/
theorem phase6_phi_weighted_drift
    (n : ℕ) (σ : Sign) (l : ℕ) (hn : 2 ≤ n)
    (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L) :
    DyadicMassDrainTight.WeightedDyadicMassDrift (L := L) (K := K)
      (fun c => Phase678ReadySurvival.Phase6DrainReady
        (L := L) (K := K) n σ l hl1 hlL i K₀ c)
      (fun c => Phase6PhiPotential.phiMass (L := L) (K := K) l c)
      (1 - ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) := by
  refine WeightedDriftDropSum.weighted_dyadic_mass_drift_on_of_dropSum
    (L := L) (K := K)
    (fun c => Phase678ReadySurvival.Phase6DrainReady
      (L := L) (K := K) n σ l hl1 hlL i K₀ c)
    (fun c => Phase6PhiPotential.phiMass (L := L) (K := K) l c)
    (ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))))
    (by simp) ?_ ?_ ?_
  · intro b hb
    rw [hb.win.1]
    exact hn
  · intro b hb pair
    exact Phase6PhiDrift.phiMass_stepOrSelf_le
      (L := L) (K := K) l n b hb.win pair.1 pair.2
  · intro b hb
    exact phase6_phi_dropSum_floor
      (L := L) (K := K) n σ l hn hl1 hlL i K₀ hhgt hhne b hb

/-! ## Axiom audit -/

#print axioms phase6_phi_dropSum_floor_of_reserveSampleGood
#print axioms phase6_phi_dropSum_floor_of_reserveFloor
#print axioms phase6_phi_dropSum_floor
#print axioms phase6_phi_weighted_drift

end Phase6PhiDropSum
end Ripple.PopulationProtocol.ExactMajority

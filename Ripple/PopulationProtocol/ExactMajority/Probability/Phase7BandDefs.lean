/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-7 exact-band interfaces

This file fixes the state predicates for the paper-faithful three-stage
Phase-7 drain.  Clearance is cumulative and strict: stage `j` assumes every
minority band below `j` is already empty.  The majority pool is the fixed block
at indices `l,l+1,l+2`; every member is within distance two of every naturally
truncated stage in that block.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOnlyWindows

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase7BandDefs

open scoped BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The number of `σ`-minority Mains at the exact exponent index `j`. -/
def bandCountN (σ : Sign) (j : Fin (L + 1))
    (c : Config (AgentState L K)) : ℕ :=
  (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count

/-- Cumulative strict clearance: every `σ`-minority band below `m` is empty. -/
def BandClear (σ : Sign) (m : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1), j.val < m → bandCountN (L := L) (K := K) σ j c = 0

/-- Phase 7 has finished the three stages beginning at `l`. -/
def Post7Bands (n : ℕ) (σ : Sign) (l : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c ∧
    BandClear (L := L) (K := K) σ (l + 3) c

/-- Opposite-sign Main eliminators whose exponent is within distance two of `j`. -/
def elimWithin2 (σ : Sign) (j : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧
    ∃ ss : Sign, ∃ k : Fin (L + 1), ss ≠ σ ∧ a.bias = Bias.dyadic ss k ∧
      k.val + 2 ≥ j.val ∧ j.val + 2 ≥ k.val)

/-- A uniform eliminator floor for every one of the truncated three stages. -/
def phase7BandPool (σ : Sign) (l E7 : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1), l ≤ j.val → j.val < l + 3 →
    1 ≤ bandCountN (L := L) (K := K) σ j c →
    E7 ≤ (elimWithin2 (L := L) (K := K) σ j).sum c.count

/-- The killed-kernel ready gate for one exact-band stage. -/
structure Phase7StageReady (n : ℕ) (σ : Sign) (l E7 : ℕ)
    (j : Fin (L + 1)) (c : Config (AgentState L K)) : Prop where
  honest : PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c
  cleared : BandClear (L := L) (K := K) σ j.val c
  pool : phase7BandPool (L := L) (K := K) σ l E7 c

/-- Opposite-sign Mains in the paper's fixed bands `l,l+1,l+2`. -/
def majorityBand3 (σ : Sign) (l : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧
    ∃ ss : Sign, ∃ k : Fin (L + 1), ss ≠ σ ∧ a.bias = Bias.dyadic ss k ∧
      l ≤ k.val ∧ k.val < l + 3)

/-- The deterministic Lemma-7.3/7.4 floor on the fixed majority block. -/
def MajorityBandFloor (σ : Sign) (l E7 : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  E7 ≤ (majorityBand3 (L := L) (K := K) σ l).sum c.count

private def bandSt (σ : Sign) (j : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.bias = Bias.dyadic σ j

private instance (σ : Sign) (j : Fin (L + 1)) (a : AgentState L K) :
    Decidable (bandSt (L := L) (K := K) σ j a) := by
  unfold bandSt
  infer_instance

private theorem bandCountN_eq_countP (σ : Sign) (j : Fin (L + 1))
    (c : Config (AgentState L K)) :
    bandCountN (L := L) (K := K) σ j c =
      Multiset.countP (bandSt (L := L) (K := K) σ j) c := by
  classical
  change (∑ a ∈ Finset.univ.filter (bandSt (L := L) (K := K) σ j), c.count a) = _
  calc
    (∑ a ∈ Finset.univ.filter (bandSt (L := L) (K := K) σ j), c.count a)
        = ∑ a : AgentState L K,
            if bandSt (L := L) (K := K) σ j a then c.count a else 0 :=
          Finset.sum_filter _ _
    _ = ∑ a : AgentState L K,
          (c.filter (bandSt (L := L) (K := K) σ j)).count a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Multiset.count_filter]
        rfl
    _ = (c.filter (bandSt (L := L) (K := K) σ j)).card :=
      Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
    _ = Multiset.countP (bandSt (L := L) (K := K) σ j) c :=
      (Multiset.countP_eq_card_filter _ _).symm

/-- An exact-band count is bounded by the population size. -/
theorem bandCountN_le_card (σ : Sign) (j : Fin (L + 1))
    (c : Config (AgentState L K)) :
    bandCountN (L := L) (K := K) σ j c ≤ c.card := by
  rw [bandCountN_eq_countP]
  exact Multiset.countP_le_card _ _

/-- Once stage `j` is empty, extend cumulative clearance through `j`. -/
theorem bandClear_succ_of_count_zero (σ : Sign) (j : Fin (L + 1))
    (c : Config (AgentState L K))
    (hclear : BandClear (L := L) (K := K) σ j.val c)
    (hzero : bandCountN (L := L) (K := K) σ j c = 0) :
    BandClear (L := L) (K := K) σ (j.val + 1) c := by
  intro k hk
  by_cases hkj : k.val < j.val
  · exact hclear k hkj
  · have hval : k.val = j.val := by omega
    have hfin : k = j := Fin.ext hval
    simpa [hfin] using hzero

/-- Every member of the fixed majority block lies in the distance-two
eliminator set of every stage in the same block. -/
theorem majorityBand3_subset_elimWithin2 (σ : Sign) (l : ℕ)
    (j : Fin (L + 1)) (hjl : l ≤ j.val) (hjtop : j.val < l + 3) :
    majorityBand3 (L := L) (K := K) σ l ⊆
      elimWithin2 (L := L) (K := K) σ j := by
  intro a ha
  rw [majorityBand3, Finset.mem_filter] at ha
  rw [elimWithin2, Finset.mem_filter]
  obtain ⟨_, hmain, ss, k, hss, hbias, hkl, hktop⟩ := ha
  exact ⟨Finset.mem_univ _, hmain, ss, k, hss, hbias, by omega, by omega⟩

/-- The paper-faithful majority-block floor supplies the uniform stage pool. -/
theorem phase7BandPool_of_majorityBandFloor (σ : Sign) (l E7 : ℕ)
    (c : Config (AgentState L K))
    (hfloor : MajorityBandFloor (L := L) (K := K) σ l E7 c) :
    phase7BandPool (L := L) (K := K) σ l E7 c := by
  intro j hjl hjtop _
  exact le_trans hfloor
    (Finset.sum_le_sum_of_subset
      (majorityBand3_subset_elimWithin2 (L := L) (K := K) σ l j hjl hjtop))

#print axioms bandCountN_le_card
#print axioms bandClear_succ_of_count_zero
#print axioms majorityBand3_subset_elimWithin2
#print axioms phase7BandPool_of_majorityBandFloor

end Phase7BandDefs
end Ripple.PopulationProtocol.ExactMajority

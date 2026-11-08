/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-7 exact-band scheduler mass

This file isolates the ordered-pair counting used by the paper-faithful
three-band Phase-7 drain.  The two orientations of
`elimWithin2 × minorityAt7` are disjoint and together contribute the factor
two in the multiplicative drift rate.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandTransition
import Ripple.PopulationProtocol.ExactMajority.Probability.WeightedDriftDropSum

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase7BandDropSum

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

open Phase7BandDefs

/-- An opposite-sign eliminator can never be the `σ`-minority Main in the
target band. -/
theorem elimWithin2_minorityAt7_disjoint (σ : Sign) (j : Fin (L + 1)) :
    Disjoint
      (elimWithin2 (L := L) (K := K) σ j)
      (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j) := by
  rw [Finset.disjoint_left]
  intro a hea hma
  simp only [elimWithin2, Finset.mem_filter] at hea
  simp only [Phase7Convergence.minorityAt7, Finset.mem_filter] at hma
  obtain ⟨_, _heMain, ss, k, hss, hebias, _⟩ := hea
  obtain ⟨_, _hmMain, hmbias⟩ := hma
  rw [hmbias] at hebias
  simp only [Bias.dyadic.injEq] at hebias
  exact hss hebias.1.symm

/-- Multiplicity-weighted ordered pairs factor over disjoint state classes. -/
theorem sum_interactionProb_cross_disjoint
    (n : ℕ) (c : Config (AgentState L K)) (hcard : c.card = n)
    (A B : Finset (AgentState L K))
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) :
    (∑ p ∈ A ×ˢ B, c.interactionProb p.1 p.2) =
      (((A.sum c.count) * (B.sum c.count) : ℕ) : ℝ≥0∞) /
        ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  have htp : c.totalPairs = n * (n - 1) := by
    rw [Config.totalPairs, hcard]
  simp only [Config.interactionProb, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum,
    Phase7Convergence.sum_interactionCount_cross_disjoint7 c A B hdisj,
    Nat.cast_mul, htp]

/-- The real and `ENNReal` presentations of the exact-band scheduler rate
agree. -/
theorem ofReal_phase7_rate_eq (n E7 : ℕ) (hn : 2 ≤ n) :
    ENNReal.ofReal (((2 * E7 : ℕ) : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1))) =
      ((2 * E7 : ℕ) : ℝ≥0∞) /
        ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
  have hden_pos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n - 1)
  have hdenR : ((n * (n - 1) : ℕ) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← hdenR, ← ENNReal.ofReal_natCast (2 * E7),
    ← ENNReal.ofReal_natCast (n * (n - 1)),
    ENNReal.ofReal_div_of_pos hden_pos]

/-- Two distinct states present in a configuration form an applicable ordered
pair. -/
theorem applicable_of_mem_distinct
    {c : Config (AgentState L K)} {x y : AgentState L K}
    (hx : x ∈ c) (hy : y ∈ c) (hxy : x ≠ y) :
    Protocol.Applicable c x y := by
  refine Multiset.le_iff_count.mpr ?_
  intro a
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl,
    Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
  have hxc : 1 ≤ Multiset.count x c := Multiset.one_le_count_iff_mem.mpr hx
  have hyc : 1 ≤ Multiset.count y c := Multiset.one_le_count_iff_mem.mpr hy
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := fun h => hxy (h ▸ rfl)
    rw [if_pos rfl, if_neg hay]
    omega
  · by_cases hay : a = y
    · subst hay
      rw [if_neg hax, if_pos rfl]
      omega
    · rw [if_neg hax, if_neg hay]
      omega

/-- The two ordered eliminator/minority rectangles lower-bound the
scheduler-weighted exact-band drop by the paper rate
`2 E7 / (n(n-1))`. -/
theorem phase7_band_dropSum_floor
    (n : ℕ) (σ : Sign) (l E7 : ℕ) (j : Fin (L + 1))
    (hn : 2 ≤ n) (hjl : l ≤ j.val) (hjtop : j.val < l + 3)
    (c : Config (AgentState L K))
    (hc : Phase7StageReady (L := L) (K := K) n σ l E7 j c) :
    ENNReal.ofReal (((2 * E7 : ℕ) : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1))) *
        (bandCountN (L := L) (K := K) σ j c : ℝ≥0∞) ≤
      WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
        (fun b => bandCountN (L := L) (K := K) σ j b) c := by
  classical
  let A := elimWithin2 (L := L) (K := K) σ j
  let B := Phase7Convergence.minorityAt7 (L := L) (K := K) σ j
  let Φ : Config (AgentState L K) → ℕ :=
    fun b => bandCountN (L := L) (K := K) σ j b
  let drop : AgentState L K × AgentState L K → ℝ≥0∞ := fun p =>
    (Φ c : ℝ≥0∞) -
      (Φ (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) : ℝ≥0∞)
  let R₁ := A ×ˢ B
  let R₂ := B ×ˢ A
  have hAB : Disjoint A B := by
    exact elimWithin2_minorityAt7_disjoint (L := L) (K := K) σ j
  have hRdisj : Disjoint R₁ R₂ :=
    Finset.disjoint_product.mpr (Or.inl hAB)
  have hterm₁ : ∀ p ∈ R₁,
      c.interactionProb p.1 p.2 ≤
        drop p * c.interactionProb p.1 p.2 := by
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨he, hm⟩ := hp
    have hne : p.1 ≠ p.2 := by
      intro h
      rw [← h] at hm
      exact Finset.disjoint_left.mp hAB he hm
    by_cases hce : 1 ≤ c.count p.1
    · by_cases hcm : 1 ≤ c.count p.2
      · have hec : p.1 ∈ c := Multiset.one_le_count_iff_mem.mp hce
        have hmc : p.2 ∈ c := Multiset.one_le_count_iff_mem.mp hcm
        have happ : Protocol.Applicable c p.1 p.2 :=
          applicable_of_mem_distinct hec hmc hne
        have hstrict :=
          Phase7BandTransition.bandCountN_stepOrSelf_drop_left
            (L := L) (K := K) n σ l E7 j c hc p
            (Finset.mem_product.mpr
              ⟨by simpa [A] using he, by simpa [B] using hm⟩) happ
        have hdropNat :
            1 ≤ Φ c - Φ (Protocol.stepOrSelf
              (NonuniformMajority L K) c p.1 p.2) := by
          dsimp [Φ] at hstrict ⊢
          omega
        have hdropE : (1 : ℝ≥0∞) ≤ drop p := by
          have hcast :
              (1 : ℝ≥0∞) ≤
                ((Φ c - Φ (Protocol.stepOrSelf
                  (NonuniformMajority L K) c p.1 p.2) : ℕ) : ℝ≥0∞) := by
            exact_mod_cast hdropNat
          simpa only [drop, ENNReal.natCast_sub] using hcast
        calc
          c.interactionProb p.1 p.2 = 1 * c.interactionProb p.1 p.2 := by
            rw [one_mul]
          _ ≤ drop p * c.interactionProb p.1 p.2 := by gcongr
      · have hz : c.count p.2 = 0 := by omega
        simp [Config.interactionProb, Config.interactionCount, hne, hz]
    · have hz : c.count p.1 = 0 := by omega
      simp [Config.interactionProb, Config.interactionCount, hne, hz]
  have hterm₂ : ∀ p ∈ R₂,
      c.interactionProb p.1 p.2 ≤
        drop p * c.interactionProb p.1 p.2 := by
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hm, he⟩ := hp
    have hne : p.1 ≠ p.2 := by
      intro h
      rw [← h] at he
      exact Finset.disjoint_left.mp hAB he hm
    by_cases hcm : 1 ≤ c.count p.1
    · by_cases hce : 1 ≤ c.count p.2
      · have hmc : p.1 ∈ c := Multiset.one_le_count_iff_mem.mp hcm
        have hec : p.2 ∈ c := Multiset.one_le_count_iff_mem.mp hce
        have happ : Protocol.Applicable c p.1 p.2 :=
          applicable_of_mem_distinct hmc hec hne
        have hstrict :=
          Phase7BandTransition.bandCountN_stepOrSelf_drop_right
            (L := L) (K := K) n σ l E7 j c hc p
            (Finset.mem_product.mpr
              ⟨by simpa [B] using hm, by simpa [A] using he⟩) happ
        have hdropNat :
            1 ≤ Φ c - Φ (Protocol.stepOrSelf
              (NonuniformMajority L K) c p.1 p.2) := by
          dsimp [Φ] at hstrict ⊢
          omega
        have hdropE : (1 : ℝ≥0∞) ≤ drop p := by
          have hcast :
              (1 : ℝ≥0∞) ≤
                ((Φ c - Φ (Protocol.stepOrSelf
                  (NonuniformMajority L K) c p.1 p.2) : ℕ) : ℝ≥0∞) := by
            exact_mod_cast hdropNat
          simpa only [drop, ENNReal.natCast_sub] using hcast
        calc
          c.interactionProb p.1 p.2 = 1 * c.interactionProb p.1 p.2 := by
            rw [one_mul]
          _ ≤ drop p * c.interactionProb p.1 p.2 := by gcongr
      · have hz : c.count p.2 = 0 := by omega
        simp [Config.interactionProb, Config.interactionCount, hne, hz]
    · have hz : c.count p.1 = 0 := by omega
      simp [Config.interactionProb, Config.interactionCount, hne, hz]
  have hrect :
      (∑ p ∈ R₁, c.interactionProb p.1 p.2) +
          (∑ p ∈ R₂, c.interactionProb p.1 p.2) ≤
        (∑ p ∈ R₁, drop p * c.interactionProb p.1 p.2) +
          ∑ p ∈ R₂, drop p * c.interactionProb p.1 p.2 :=
    add_le_add
      (Finset.sum_le_sum fun p hp => hterm₁ p hp)
      (Finset.sum_le_sum fun p hp => hterm₂ p hp)
  have hunion :
      (∑ p ∈ R₁, drop p * c.interactionProb p.1 p.2) +
          ∑ p ∈ R₂, drop p * c.interactionProb p.1 p.2 =
        ∑ p ∈ R₁ ∪ R₂, drop p * c.interactionProb p.1 p.2 :=
    (Finset.sum_union hRdisj).symm
  have huniv :
      (∑ p ∈ R₁ ∪ R₂, drop p * c.interactionProb p.1 p.2) ≤
        ∑ p : AgentState L K × AgentState L K,
          drop p * c.interactionProb p.1 p.2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro p _ _
    exact bot_le
  by_cases hΦ0 : Φ c = 0
  · simp [Φ, hΦ0]
  · have hΦpos : 1 ≤ Φ c := Nat.one_le_iff_ne_zero.mpr hΦ0
    have hA : E7 ≤ A.sum c.count := by
      exact hc.pool j hjl hjtop (by simpa [Φ] using hΦpos)
    have hsum₁ :
        (∑ p ∈ R₁, c.interactionProb p.1 p.2) =
          (((A.sum c.count) * (B.sum c.count) : ℕ) : ℝ≥0∞) /
            ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
      exact sum_interactionProb_cross_disjoint n c hc.honest.1 A B
        (fun a ha b hb hab => by
          rw [← hab] at hb
          exact Finset.disjoint_left.mp hAB ha hb)
    have hsum₂ :
        (∑ p ∈ R₂, c.interactionProb p.1 p.2) =
          (((B.sum c.count) * (A.sum c.count) : ℕ) : ℝ≥0∞) /
            ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
      exact sum_interactionProb_cross_disjoint n c hc.honest.1 B A
        (fun b hb a ha hab => by
          rw [hab] at hb
          exact Finset.disjoint_left.mp hAB ha hb)
    have hweighted :
        ENNReal.ofReal (((2 * E7 : ℕ) : ℝ) /
            ((n : ℝ) * ((n : ℝ) - 1))) * (Φ c : ℝ≥0∞) ≤
          (∑ p ∈ R₁, c.interactionProb p.1 p.2) +
            ∑ p ∈ R₂, c.interactionProb p.1 p.2 := by
      rw [ofReal_phase7_rate_eq n E7 hn, hsum₁, hsum₂]
      have hcoef : ((2 * E7 : ℕ) : ℝ≥0∞) ≤
          ((2 * A.sum c.count : ℕ) : ℝ≥0∞) := by
        exact_mod_cast Nat.mul_le_mul_left 2 hA
      have hB : (B.sum c.count : ℕ) = Φ c := by
        rfl
      rw [hB]
      calc
        ((2 * E7 : ℕ) : ℝ≥0∞) /
              ((n * (n - 1) : ℕ) : ℝ≥0∞) * (Φ c : ℝ≥0∞)
            ≤ ((2 * A.sum c.count : ℕ) : ℝ≥0∞) /
                ((n * (n - 1) : ℕ) : ℝ≥0∞) * (Φ c : ℝ≥0∞) := by
              gcongr
        _ = (((A.sum c.count) * Φ c : ℕ) : ℝ≥0∞) /
              ((n * (n - 1) : ℕ) : ℝ≥0∞) +
            (((Φ c) * (A.sum c.count) : ℕ) : ℝ≥0∞) /
              ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
              push_cast
              simp only [div_eq_mul_inv]
              ring
    calc
      ENNReal.ofReal (((2 * E7 : ℕ) : ℝ) /
            ((n : ℝ) * ((n : ℝ) - 1))) *
          (bandCountN (L := L) (K := K) σ j c : ℝ≥0∞)
          = ENNReal.ofReal (((2 * E7 : ℕ) : ℝ) /
              ((n : ℝ) * ((n : ℝ) - 1))) * (Φ c : ℝ≥0∞) := rfl
      _ ≤ (∑ p ∈ R₁, c.interactionProb p.1 p.2) +
            ∑ p ∈ R₂, c.interactionProb p.1 p.2 := hweighted
      _ ≤ (∑ p ∈ R₁, drop p * c.interactionProb p.1 p.2) +
            ∑ p ∈ R₂, drop p * c.interactionProb p.1 p.2 := hrect
      _ = ∑ p ∈ R₁ ∪ R₂, drop p * c.interactionProb p.1 p.2 := hunion
      _ ≤ ∑ p : AgentState L K × AgentState L K,
          drop p * c.interactionProb p.1 p.2 := huniv
      _ = WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
          (fun b => bandCountN (L := L) (K := K) σ j b) c := rfl

/-- Assemble the exact-band rectangle floor with the generic weighted-drift
bridge. -/
theorem phase7_band_weighted_drift
    (n : ℕ) (σ : Sign) (l E7 : ℕ) (j : Fin (L + 1))
    (hn : 2 ≤ n) (hjl : l ≤ j.val) (hjtop : j.val < l + 3) :
    DyadicMassDrainTight.WeightedDyadicMassDrift (L := L) (K := K)
      (fun c => Phase7StageReady (L := L) (K := K) n σ l E7 j c)
      (fun c => bandCountN (L := L) (K := K) σ j c)
      (1 - ENNReal.ofReal (((2 * E7 : ℕ) : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1)))) := by
  refine WeightedDriftDropSum.weighted_dyadic_mass_drift_on_of_dropSum
    (L := L) (K := K)
    (fun c => Phase7StageReady (L := L) (K := K) n σ l E7 j c)
    (fun c => bandCountN (L := L) (K := K) σ j c)
    (ENNReal.ofReal (((2 * E7 : ℕ) : ℝ) /
      ((n : ℝ) * ((n : ℝ) - 1)))) (by simp) ?_ ?_ ?_
  · intro c hc
    rw [hc.honest.1]
    exact hn
  · intro c hc pair
    exact Phase7BandTransition.bandCountN_stepOrSelf_le
      (L := L) (K := K) σ j n c hc.honest hc.cleared pair.1 pair.2
  · intro c hc
    exact phase7_band_dropSum_floor
      (L := L) (K := K) n σ l E7 j hn hjl hjtop c hc

#print axioms elimWithin2_minorityAt7_disjoint
#print axioms sum_interactionProb_cross_disjoint
#print axioms ofReal_phase7_rate_eq
#print axioms phase7_band_dropSum_floor
#print axioms phase7_band_weighted_drift

end Phase7BandDropSum
end Ripple.PopulationProtocol.ExactMajority

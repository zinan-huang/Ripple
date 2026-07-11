/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-3 same-exponent cancellation rectangle

This file discharges the scheduler-level H3 bridge used by the Lemma 6.17
same-exponent cancellation clock.  It counts the two ordered rectangles
`majority@h × minority@h` and `minority@h × majority@h`, then lifts that
interaction mass through the real `NonuniformMajority` transition kernel.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma617Minority
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FloorMasses
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealMixed

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ExactMajority
namespace Phase3SameExpRect

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Same-exponent phase-3 rectangles -/

/-- Majority-opinion Main agents at the single exponent index `h`, where `σ`
is the minority sign. -/
noncomputable def majorityAt (σ : Sign) (h : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter fun a =>
    a.role = Role.main ∧
      ∃ ss : Sign, ss ≠ σ ∧ a.bias = Bias.dyadic ss h

/-- Minority-opinion Main agents at the single exponent index `h`. -/
noncomputable def minorityAt (σ : Sign) (h : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter fun a =>
    a.role = Role.main ∧ a.bias = Bias.dyadic σ h

/-- The current same-exponent majority count `A_h`. -/
noncomputable def majorityCount (σ : Sign) (h : Fin (L + 1))
    (c : Config (AgentState L K)) : ℕ :=
  (majorityAt (L := L) (K := K) σ h).sum c.count

/-- The current same-exponent minority count `B_h`. -/
noncomputable def minorityCount (σ : Sign) (h : Fin (L + 1))
    (c : Config (AgentState L K)) : ℕ :=
  (minorityAt (L := L) (K := K) σ h).sum c.count

/-- The two ordered same-exponent cancellation rectangles. -/
noncomputable def sameExpCancelRect (σ : Sign) (h : Fin (L + 1)) :
    Finset (AgentState L K × AgentState L K) :=
  (majorityAt (L := L) (K := K) σ h ×ˢ minorityAt (L := L) (K := K) σ h) ∪
    (minorityAt (L := L) (K := K) σ h ×ˢ majorityAt (L := L) (K := K) σ h)

/-- The scheduler event of applicable same-exponent opposite-opinion Main/Main
pairs.  Zero-mass absent pairs are excluded so this event can be lifted directly
through `scheduledStep`. -/
def sameExpCancelPairs (c : Config (AgentState L K)) (σ : Sign)
    (h : Fin (L + 1)) : Set (AgentState L K × AgentState L K) :=
  {p | p ∈ sameExpCancelRect (L := L) (K := K) σ h ∧
    Protocol.Applicable c p.1 p.2}

/-- Positive `interactionCount` implies `Applicable`.  The same lemma exists
privately in several rectangle files; this local copy keeps the scheduler bridge
self-contained. -/
private lemma applicable_of_pos_iCount_sameExp (c : Config (AgentState L K))
    (s₁ s₂ : AgentState L K) (h : 0 < c.interactionCount s₁ s₂) :
    Protocol.Applicable c s₁ s₂ := by
  change {s₁, s₂} ≤ c
  rw [Multiset.le_iff_count]
  intro a
  simp only [Config.interactionCount, Config.count] at h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  by_cases heq : s₁ = s₂
  · subst heq
    simp only [ite_true] at h
    have htwo : 2 ≤ Multiset.count s₁ c := by
      by_contra hlt
      have hle : Multiset.count s₁ c ≤ 1 := by omega
      have hzero : Multiset.count s₁ c * (Multiset.count s₁ c - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (Multiset.count s₁ c) with h0 | hpos
        · simp [h0]
        · have hone : Multiset.count s₁ c = 1 := by omega
          simp [hone]
      omega
    by_cases ha : a = s₁ <;> simp_all
  · simp only [heq, ite_false] at h
    have hc1 : 0 < Multiset.count s₁ c := pos_of_mul_pos_left h (Nat.zero_le _)
    have hc2 : 0 < Multiset.count s₂ c := pos_of_mul_pos_right h (Nat.zero_le _)
    by_cases ha1 : a = s₁ <;> by_cases ha2 : a = s₂ <;> simp_all <;> omega

/-- Same-exponent majority and minority state sets are disjoint. -/
theorem majorityAt_minorityAt_disjoint
    (σ : Sign) (h : Fin (L + 1)) (a : AgentState L K)
    (haM : a ∈ majorityAt (L := L) (K := K) σ h)
    (ham : a ∈ minorityAt (L := L) (K := K) σ h) :
    False := by
  rw [majorityAt, Finset.mem_filter] at haM
  rw [minorityAt, Finset.mem_filter] at ham
  obtain ⟨_ha_univ, _harole, ss, hss, hbiasM⟩ := haM
  obtain ⟨_ha_univ', _harole', hbiasm⟩ := ham
  have hb : (Bias.dyadic ss h : Bias L) = Bias.dyadic σ h := hbiasM.symm.trans hbiasm
  rw [Bias.dyadic.injEq] at hb
  exact hss hb.1

/-- The two orientations of the same-exponent rectangle are disjoint. -/
private theorem sameExpCancelRect_orientations_disjoint
    (σ : Sign) (h : Fin (L + 1)) :
    Disjoint
      (majorityAt (L := L) (K := K) σ h ×ˢ minorityAt (L := L) (K := K) σ h)
      (minorityAt (L := L) (K := K) σ h ×ˢ majorityAt (L := L) (K := K) σ h) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpA hpB
  rw [Finset.mem_product] at hpA hpB
  exact majorityAt_minorityAt_disjoint (L := L) (K := K) σ h p.1 hpA.1 hpB.1

/-- The interaction-count mass of one same-exponent orientation is `A_h B_h`. -/
private theorem sameExp_orientation_interactionCount
    (σ : Sign) (h : Fin (L + 1)) (c : Config (AgentState L K)) :
    (∑ p ∈ majorityAt (L := L) (K := K) σ h ×ˢ minorityAt (L := L) (K := K) σ h,
        c.interactionCount p.1 p.2)
      = majorityCount (L := L) (K := K) σ h c *
          minorityCount (L := L) (K := K) σ h c := by
  classical
  unfold majorityCount minorityCount
  exact ClockRealMixed.sum_interactionCount_cross_disjoint
    (L := L) (K := K) c
    (majorityAt (L := L) (K := K) σ h)
    (minorityAt (L := L) (K := K) σ h)
    (fun a ha b hb hEq =>
      majorityAt_minorityAt_disjoint (L := L) (K := K) σ h b (by simpa [hEq] using ha) hb)

/-- The interaction-count mass of the symmetric same-exponent orientation is
again `A_h B_h`. -/
private theorem sameExp_orientation_interactionCount_symm
    (σ : Sign) (h : Fin (L + 1)) (c : Config (AgentState L K)) :
    (∑ p ∈ minorityAt (L := L) (K := K) σ h ×ˢ majorityAt (L := L) (K := K) σ h,
        c.interactionCount p.1 p.2)
      = minorityCount (L := L) (K := K) σ h c *
          majorityCount (L := L) (K := K) σ h c := by
  classical
  unfold majorityCount minorityCount
  exact ClockRealMixed.sum_interactionCount_cross_disjoint
    (L := L) (K := K) c
    (minorityAt (L := L) (K := K) σ h)
    (majorityAt (L := L) (K := K) σ h)
    (fun a ha b hb hEq =>
      majorityAt_minorityAt_disjoint (L := L) (K := K) σ h b hb (by simpa [hEq] using ha))

/-- The two ordered same-exponent rectangles have interaction-count mass
`2 A_h B_h`. -/
private theorem sameExpCancelRect_interactionCount
    (σ : Sign) (h : Fin (L + 1)) (c : Config (AgentState L K)) :
    (∑ p ∈ sameExpCancelRect (L := L) (K := K) σ h, c.interactionCount p.1 p.2)
      = 2 * majorityCount (L := L) (K := K) σ h c *
          minorityCount (L := L) (K := K) σ h c := by
  classical
  unfold sameExpCancelRect
  rw [Finset.sum_union (sameExpCancelRect_orientations_disjoint (L := L) (K := K) σ h)]
  rw [sameExp_orientation_interactionCount (L := L) (K := K) σ h c,
    sameExp_orientation_interactionCount_symm (L := L) (K := K) σ h c]
  ring

/-- The scheduler probability of selecting an applicable same-exponent
opposite-opinion Main/Main cancel pair is at least the ordered-pair rectangle
rate `2 A_h B_h / (n(n-1))`. -/
theorem phase3_sameExp_interactionProb_ge
    (σ : Sign) (h : Fin (L + 1)) (n : ℕ)
    (c : Config (AgentState L K)) (hcard : c.card = n) (hn : 2 ≤ n) :
    ENNReal.ofReal
        (((2 * majorityCount (L := L) (K := K) σ h c *
            minorityCount (L := L) (K := K) σ h c : ℕ) : ℝ) /
          ((n : ℝ) * (n - 1 : ℕ)))
      ≤ (c.interactionPMF (by rw [hcard]; exact hn)).toMeasure
          (sameExpCancelPairs (L := L) (K := K) c σ h) := by
  classical
  let R := sameExpCancelRect (L := L) (K := K) σ h
  have hc2 : 2 ≤ c.card := by rw [hcard]; exact hn
  have hsupport_subset :
      (↑R : Set (AgentState L K × AgentState L K)) ∩
          (c.interactionPMF hc2).support
        ⊆ sameExpCancelPairs (L := L) (K := K) c σ h := by
    intro p hp
    obtain ⟨hpR, hpsupp⟩ := hp
    rw [PMF.mem_support_iff] at hpsupp
    have happ : Protocol.Applicable c p.1 p.2 := by
      apply applicable_of_pos_iCount_sameExp (L := L) (K := K)
      by_contra hzero
      exact hpsupp (by
        change c.interactionProb p.1 p.2 = 0
        unfold Config.interactionProb
        rw [show c.interactionCount p.1 p.2 = 0 by omega]
        simp)
    exact ⟨by simpa [R] using hpR, happ⟩
  have hle_support := (c.interactionPMF hc2).toMeasure_mono
    (DiscreteMeasurableSpace.forall_measurableSet _) hsupport_subset
  have hRmeasure :
      (c.interactionPMF hc2).toMeasure (↑R : Set (AgentState L K × AgentState L K))
        = ENNReal.ofReal
          (((2 * majorityCount (L := L) (K := K) σ h c *
              minorityCount (L := L) (K := K) σ h c : ℕ) : ℝ) /
            ((n : ℝ) * (n - 1 : ℕ))) := by
    rw [PMF.toMeasure_apply_finset]
    simp_rw [show ∀ p : AgentState L K × AgentState L K,
        (c.interactionPMF hc2) p =
          (c.interactionCount p.1 p.2 : ENNReal) / c.totalPairs
      from fun _ => rfl, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum]
    rw [show (∑ p ∈ R, c.interactionCount p.1 p.2)
        = 2 * majorityCount (L := L) (K := K) σ h c *
          minorityCount (L := L) (K := K) σ h c by
        simpa [R] using sameExpCancelRect_interactionCount (L := L) (K := K) σ h c]
    rw [← div_eq_mul_inv]
    have hden_pos : (0 : ℝ) < ((n : ℝ) * (n - 1 : ℕ)) := by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
      have hn1 : (0 : ℝ) < (n - 1 : ℕ) := by
        exact_mod_cast (Nat.sub_pos_of_lt hn)
      positivity
    have hden_cast :
        (((n * (n - 1) : ℕ) : ℝ)) = (n : ℝ) * (n - 1 : ℕ) := by
      rw [Nat.cast_mul]
    rw [show c.totalPairs = n * (n - 1) by rw [Config.totalPairs, hcard]]
    rw [← ENNReal.ofReal_natCast (2 * majorityCount (L := L) (K := K) σ h c *
          minorityCount (L := L) (K := K) σ h c)]
    rw [← ENNReal.ofReal_natCast (n * (n - 1))]
    rw [← ENNReal.ofReal_div_of_pos (by rwa [hden_cast] : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ))]
    rw [hden_cast]
    rw [div_eq_mul_inv]
  calc
    ENNReal.ofReal
        (((2 * majorityCount (L := L) (K := K) σ h c *
            minorityCount (L := L) (K := K) σ h c : ℕ) : ℝ) /
          ((n : ℝ) * (n - 1 : ℕ)))
        = (c.interactionPMF hc2).toMeasure (↑R : Set (AgentState L K × AgentState L K)) :=
          hRmeasure.symm
    _ ≤ (c.interactionPMF hc2).toMeasure
          (sameExpCancelPairs (L := L) (K := K) c σ h) := hle_support

/-- Same-exponent rectangle bridge in the exact H3 shape expected by
`CancelClockConcentration`: if every applicable same-exponent cancel pair
increments the cancellation counter `C`, then the one-step success probability
is at least `2 A_h B_h / (n(n-1))`. -/
theorem phase3_sameExp_cancelCount_step_ge
    (σ : Sign) (h : Fin (L + 1)) (C : Config (AgentState L K) → ℕ)
    (n : ℕ) (c : Config (AgentState L K)) (hcard : c.card = n) (hn : 2 ≤ n)
    (hCinc : ∀ p ∈ sameExpCancelPairs (L := L) (K := K) c σ h,
      C ((NonuniformMajority L K).scheduledStep c p) = C c + 1) :
    (2 * (majorityCount (L := L) (K := K) σ h c : ℝ) *
        (minorityCount (L := L) (K := K) σ h c : ℝ)) /
        ((n : ℝ) * (n - 1 : ℕ))
      ≤ ((NonuniformMajority L K).transitionKernel c).real {y | C y = C c + 1} := by
  classical
  have hc2 : 2 ≤ c.card := by rw [hcard]; exact hn
  have hgood : ∀ p ∈ sameExpCancelPairs (L := L) (K := K) c σ h,
      (NonuniformMajority L K).scheduledStep c p ∈ {y | C y = C c + 1} := by
    intro p hp
    exact hCinc p hp
  have hstep :
      (c.interactionPMF hc2).toMeasure (sameExpCancelPairs (L := L) (K := K) c σ h)
        ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure {y | C y = C c + 1} := by
    exact stepDistOrSelf_toMeasure_ge c hc2 {y | C y = C c + 1}
      (sameExpCancelPairs (L := L) (K := K) c σ h) hgood
  have hrect :
      ENNReal.ofReal
          (((2 * majorityCount (L := L) (K := K) σ h c *
              minorityCount (L := L) (K := K) σ h c : ℕ) : ℝ) /
            ((n : ℝ) * (n - 1 : ℕ)))
        ≤ (c.interactionPMF hc2).toMeasure
            (sameExpCancelPairs (L := L) (K := K) c σ h) := by
    simpa using phase3_sameExp_interactionProb_ge
      (L := L) (K := K) σ h n c hcard hn
  have hENN :
      ENNReal.ofReal
          (((2 * majorityCount (L := L) (K := K) σ h c *
              minorityCount (L := L) (K := K) σ h c : ℕ) : ℝ) /
            ((n : ℝ) * (n - 1 : ℕ)))
        ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure {y | C y = C c + 1} :=
    hrect.trans hstep
  have hrate_nonneg :
      0 ≤ ((2 * majorityCount (L := L) (K := K) σ h c *
              minorityCount (L := L) (K := K) σ h c : ℕ) : ℝ) /
            ((n : ℝ) * (n - 1 : ℕ)) := by
    have hden_pos : (0 : ℝ) < ((n : ℝ) * (n - 1 : ℕ)) := by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
      have hn1 : (0 : ℝ) < (n - 1 : ℕ) := by
        exact_mod_cast (Nat.sub_pos_of_lt hn)
      positivity
    positivity
  have htarget_ne_top :
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure {y | C y = C c + 1} ≠ ⊤ := by
    have hle_one :
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure {y | C y = C c + 1}
          ≤ (1 : ℝ≥0∞) := by
      calc
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure {y | C y = C c + 1}
            ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Set.univ :=
              measure_mono (Set.subset_univ _)
        _ = 1 := by simp
    exact ne_of_lt (lt_of_le_of_lt hle_one ENNReal.one_lt_top)
  have hreal := ENNReal.toReal_mono htarget_ne_top hENN
  rw [ENNReal.toReal_ofReal hrate_nonneg] at hreal
  simpa [Measure.real] using hreal

/-- Lemma 6.17 per-row cancellation clock with H3 discharged by the phase-3
same-exponent rectangle.  The caller still supplies the counter support and the
structural floors; the ordered-pair success lower bound is no longer a premise. -/
theorem perRow_cancelClock_tail_sameExp
    (σ : Sign) (h : Fin (L + 1)) (C : Config (AgentState L K) → ℕ)
    (A0 B0 n D T : ℕ) (x0 : Config (AgentState L K))
    (hC0 : C x0 = 0)
    (hn : 2 ≤ n) (hD : D < B0) (hBA : B0 ≤ A0)
    (hqle :
      ∀ i : Fin D, CancelClockConcentration.twoSidedQ A0 B0 n D i ≤ 1)
    (hcard : ∀ x, C x < D → x.card = n)
    (hstep :
      ∀ x, C x < D →
        ∀ᵐ y ∂((NonuniformMajority L K).transitionKernel x),
          C y = C x ∨ C y = C x + 1)
    (hAfloor :
      ∀ x (_ : C x < D),
        ((A0 - C x : ℕ) : ℝ) ≤ majorityCount (L := L) (K := K) σ h x)
    (hBfloor :
      ∀ x (_ : C x < D),
        ((B0 - C x : ℕ) : ℝ) ≤ minorityCount (L := L) (K := K) σ h x)
    (hCinc :
      ∀ x (_ : C x < D), ∀ p ∈ sameExpCancelPairs (L := L) (K := K) x σ h,
        C ((NonuniformMajority L K).scheduledStep x p) = C x + 1)
    (hT :
      CancelClockConcentration.integratedInvRateClock D
        (CancelClockConcentration.twoSidedQ A0 B0 n D) D ≤ (T : ℝ)) :
    (CancelClockConcentration.stoppedKernel
        (NonuniformMajority L K).transitionKernel C D ^ T) x0 {x | C x < D}
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock D
                (CancelClockConcentration.twoSidedQ A0 B0 n D) D) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack D
                  (CancelClockConcentration.twoSidedQ A0 B0 n D)) ^ 2))) := by
  refine Lemma617Minority.perRow_cancelClock_tail
    (K := (NonuniformMajority L K).transitionKernel)
    (C := C)
    (A := majorityCount (L := L) (K := K) σ h)
    (B := minorityCount (L := L) (K := K) σ h)
    (A0 := A0) (B0 := B0) (n := n) (D := D) (T := T) (x0 := x0)
    hC0 hn hD hBA hqle hstep hAfloor hBfloor ?_ hT
  intro x hx
  exact phase3_sameExp_cancelCount_step_ge
    (L := L) (K := K) σ h C n x (hcard x hx) hn (hCinc x hx)

#print axioms phase3_sameExp_interactionProb_ge
#print axioms phase3_sameExp_cancelCount_step_ge
#print axioms perRow_cancelClock_tail_sameExp

end Phase3SameExpRect
end ExactMajority

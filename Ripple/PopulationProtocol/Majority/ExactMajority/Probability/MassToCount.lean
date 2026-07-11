/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Deterministic dyadic mass-to-count conversion

This file discharges the pointwise conversion needed by `Lemma613OFloor`:
a total dyadic-mass bound plus an active-band index ceiling gives the biased
Main count bound consumed as `hBiased`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma613OFloor
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DoublingEdges
import Mathlib.Tactic

namespace ExactMajority
namespace MassToCount

open scoped BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Stated first: the mass-to-count bridge -/

/-- The absolute dyadic mass of a bias, as a real number. -/
noncomputable def biasDyadicMass (b : Bias L) : ℝ :=
  match b with
  | .zero => 0
  | .dyadic _ i => (2 : ℝ) ^ (-(i.val : ℤ))

/-- The absolute dyadic mass of one agent.  This is sign- and role-agnostic,
matching the total-mass event: any non-Main mass only helps the upper bound. -/
noncomputable def agentDyadicMass (a : AgentState L K) : ℝ :=
  biasDyadicMass (L := L) a.bias

/-- Total absolute dyadic mass of a configuration. -/
noncomputable def totalDyadicMass (c : Config (AgentState L K)) : ℝ :=
  (c.map (fun a => agentDyadicMass (L := L) (K := K) a)).sum

theorem biasDyadicMass_nonneg (b : Bias L) : 0 ≤ biasDyadicMass (L := L) b := by
  cases b with
  | zero => simp [biasDyadicMass]
  | dyadic _ i =>
      simp [biasDyadicMass]

theorem agentDyadicMass_nonneg (a : AgentState L K) :
    0 ≤ agentDyadicMass (L := L) (K := K) a :=
  biasDyadicMass_nonneg (L := L) a.bias

theorem totalDyadicMass_nonneg (c : Config (AgentState L K)) :
    0 ≤ totalDyadicMass (L := L) (K := K) c := by
  unfold totalDyadicMass
  refine Multiset.sum_nonneg ?_
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨a, _, rfl⟩ := hx
  exact agentDyadicMass_nonneg (L := L) (K := K) a

/-- A biased Main under the active-band ceiling contributes at least one unit
after scaling total dyadic mass by `2^(h+1)`. -/
theorem one_le_scaled_agentDyadicMass_of_biasedMain_below
    (h : ℕ) (a : AgentState L K)
    (ha : a.role = Role.main ∧ a.bias ≠ Bias.zero)
    (hBandA :
      ∀ (s : Sign) (i : Fin (L + 1)), a.bias = Bias.dyadic s i → i.val ≤ h + 1) :
    (1 : ℝ) ≤ (2 : ℝ) ^ (((h + 1 : ℕ) : ℤ)) *
      agentDyadicMass (L := L) (K := K) a := by
  cases hb : a.bias with
  | zero =>
      exact False.elim (ha.2 hb)
  | dyadic s i =>
      unfold agentDyadicMass biasDyadicMass
      rw [hb]
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      have hnonneg :
          0 ≤ (((h + 1 : ℕ) : ℤ) + -((i.val : ℕ) : ℤ)) := by
        have hi : i.val ≤ h + 1 := hBandA s i hb
        omega
      exact one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 2) hnonneg

/-- Deterministic scaled form: if every biased Main has index at most `h+1`,
then `biasedMainCount ≤ 2^(h+1) * totalDyadicMass`.  This is the formal
`count * min-weight ≤ mass` step, after multiplying by `1 / min-weight`. -/
theorem biasedMainCount_le_scaled_totalDyadicMass
    (h : ℕ) (c : Config (AgentState L K))
    (hBand : DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c) :
    (Lemma613OFloor.phase3BiasedMainCount (L := L) (K := K) c : ℝ)
      ≤ (2 : ℝ) ^ (((h + 1 : ℕ) : ℤ)) *
        totalDyadicMass (L := L) (K := K) c := by
  classical
  induction c using Multiset.induction_on with
  | empty =>
      simp [Lemma613OFloor.phase3BiasedMainCount, totalDyadicMass]
  | cons a c ih =>
      let scale : ℝ := (2 : ℝ) ^ (((h + 1 : ℕ) : ℤ))
      have hscale_nonneg : 0 ≤ scale := by
        unfold scale
        positivity
      have hBandTail :
          DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c := by
        intro b hb hbmain s i hbi
        exact hBand b (by simp [hb]) hbmain s i hbi
      have ih' := ih hBandTail
      have hterm :
          (((if a.role = Role.main ∧ a.bias ≠ Bias.zero then 1 else 0) : ℕ) : ℝ)
            ≤ scale * agentDyadicMass (L := L) (K := K) a := by
        by_cases ha : a.role = Role.main ∧ a.bias ≠ Bias.zero
        · have hBandA :
            ∀ (s : Sign) (i : Fin (L + 1)), a.bias = Bias.dyadic s i → i.val ≤ h + 1 := by
              intro s i hbi
              exact hBand a (by simp) ha.1 s i hbi
          simpa [ha, scale] using
            one_le_scaled_agentDyadicMass_of_biasedMain_below
              (L := L) (K := K) h a ha hBandA
        · have hnonneg :
            0 ≤ scale * agentDyadicMass (L := L) (K := K) a :=
              mul_nonneg hscale_nonneg (agentDyadicMass_nonneg (L := L) (K := K) a)
          simpa [ha] using hnonneg
      unfold Lemma613OFloor.phase3BiasedMainCount totalDyadicMass at *
      simp only [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add]
      calc
        (Multiset.countP
              (fun a => a.role = Role.main ∧ a.bias ≠ Bias.zero) c : ℝ)
            + (((if a.role = Role.main ∧ a.bias ≠ Bias.zero then 1 else 0) : ℕ) : ℝ)
            ≤ scale *
                (Multiset.map
                  (fun a => agentDyadicMass (L := L) (K := K) a) c).sum
              + scale * agentDyadicMass (L := L) (K := K) a := by
                exact add_le_add ih' hterm
        _ = scale *
              (agentDyadicMass (L := L) (K := K) a
                + (Multiset.map
                    (fun a => agentDyadicMass (L := L) (K := K) a) c).sum) := by
                ring

/-- **Mass-to-count conversion for `Lemma613OFloor.hBiased`.**

On the good total-mass event
`totalDyadicMass c ≤ ρ |M| 2^{-h}`, and under the active-band ceiling that
every biased Main has dyadic index at most `h+1`, the biased Main count is at
most `2 ρ |M|`.  The proof is deterministic and independent of the §4.6
probability arguments. -/
theorem biasedMainCount_le_of_mass
    (h : ℕ) (rho M : ℝ) (c : Config (AgentState L K))
    (hBand : DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c)
    (hMass :
      totalDyadicMass (L := L) (K := K) c
        ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (Lemma613OFloor.phase3BiasedMainCount (L := L) (K := K) c : ℝ)
      ≤ 2 * rho * M := by
  let scale : ℝ := (2 : ℝ) ^ (((h + 1 : ℕ) : ℤ))
  have hscale_nonneg : 0 ≤ scale := by
    unfold scale
    positivity
  have hscaled :=
    biasedMainCount_le_scaled_totalDyadicMass (L := L) (K := K) h c hBand
  have hmass_scaled :
      scale * totalDyadicMass (L := L) (K := K) c
        ≤ scale * (rho * M * (2 : ℝ) ^ (-(h : ℤ))) :=
    mul_le_mul_of_nonneg_left hMass hscale_nonneg
  calc
    (Lemma613OFloor.phase3BiasedMainCount (L := L) (K := K) c : ℝ)
        ≤ scale * totalDyadicMass (L := L) (K := K) c := hscaled
    _ ≤ scale * (rho * M * (2 : ℝ) ^ (-(h : ℤ))) := hmass_scaled
    _ = 2 * rho * M := by
      unfold scale
      have hpow :
          (2 : ℝ) ^ (((h + 1 : ℕ) : ℤ)) * (2 : ℝ) ^ (-(h : ℤ)) = 2 := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        have hexp :
            (((h + 1 : ℕ) : ℤ) + -(h : ℤ)) = 1 := by
          omega
        rw [hexp]
        norm_num
      calc
        (2 : ℝ) ^ (((h + 1 : ℕ) : ℤ)) *
            (rho * M * (2 : ℝ) ^ (-(h : ℤ)))
            = ((2 : ℝ) ^ (((h + 1 : ℕ) : ℤ)) *
                (2 : ℝ) ^ (-(h : ℤ))) * (rho * M) := by
              ring
        _ = 2 * rho * M := by
          rw [hpow]
          ring

/-- Lemma-6.13 with the `hBiased` premise supplied by the deterministic
mass-to-count conversion. -/
theorem ofuel_floor_of_mass
    (l h : ℕ) (rho M : ℝ) (c : Config (AgentState L K))
    (hReach :
      (97 / 100 : ℝ) * M
        ≤ (Lemma613OFloor.phase3ReachedMainCount (L := L) (K := K) l c : ℝ))
    (hBand : DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c)
    (hMass :
      totalDyadicMass (L := L) (K := K) c
        ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (97 / 100 - 2 * rho) * M
      ≤ (Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c : ℝ) :=
  Lemma613OFloor.ofuel_floor (L := L) (K := K) l rho M c hReach
    (biasedMainCount_le_of_mass (L := L) (K := K) h rho M c hBand hMass)

/-- Final-hour specialization with the landed Lemma-6.16 constant
`rho_lm1`. -/
theorem ofuel_floor_final_hour_of_mass
    (l h : ℕ) (M : ℝ) (c : Config (AgentState L K))
    (hM : 0 ≤ M)
    (hReach :
      (97 / 100 : ℝ) * M
        ≤ (Lemma613OFloor.phase3ReachedMainCount (L := L) (K := K) l c : ℝ))
    (hBand : DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c)
    (hMass :
      totalDyadicMass (L := L) (K := K) c
        ≤ Lemma616TotalMass.Constants.rho_lm1 * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (15 / 100 : ℝ) * M
      ≤ (Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c : ℝ) :=
  Lemma613OFloor.ofuel_floor_final_hour (L := L) (K := K) l M c hM hReach
    (biasedMainCount_le_of_mass (L := L) (K := K) h
      Lemma616TotalMass.Constants.rho_lm1 M c hBand hMass)

#print axioms biasedMainCount_le_of_mass
#print axioms ofuel_floor_of_mass
#print axioms ofuel_floor_final_hour_of_mass

end MassToCount
end ExactMajority

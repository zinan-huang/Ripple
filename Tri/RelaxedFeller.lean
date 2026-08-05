/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Freeze
import Tri.RelaxedChain
import Tri.RelaxedDrift

/-!
# Feller safety bound for unequal reaction rates

This instantiates the repository's generic frozen-chain ruin theorem with the
rate-weighted geometric potential from `RelaxedDrift`.
-/

namespace Tri

open scoped ENNReal

/-- A uniform rate-weighted corner bias gives an unbounded-horizon lower-ruin
bound for the relaxed Tri chain. -/
theorem relaxed_feller
    (r : RelaxedRate) (β : NNReal)
    (n aLo bHi k : ℕ)
    (h3 : 3 ≤ n) (hpop : aLo + bHi + 2 = n)
    (hβ1 : 1 ≤ β) (hfireβ : r.fire ≤ β)
    (hcorner :
      β * (bHi + 1 : NNReal) ≤ r.fire * (aLo + 1 : NNReal)) :
    ⨆ T : ℕ,
        hitProb (fun z => z ≤ aLo) (relaxedTriChain r n) T (aLo + k) ≤
      (β : ℝ≥0∞)⁻¹ ^ k := by
  let u : ℝ≥0∞ := (β : ℝ≥0∞)⁻¹
  have hu1 : u ≤ 1 := by
    dsimp only [u]
    exact ENNReal.inv_le_one.mpr (by exact_mod_cast hβ1)
  have hβtop : (β : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hu0 : u ≠ 0 := by
    dsimp only [u]
    exact ENNReal.inv_ne_zero.mpr hβtop
  have hoff :
      ∀ s : ℕ, ¬s ≤ aLo →
        expect (relaxedTriChain r n s) (fun z => u ^ z) ≤ u ^ s := by
    intro s hs
    rw [Nat.not_le] at hs
    obtain ⟨a, rfl⟩ : ∃ a, s = a + 1 := ⟨s - 1, by omega⟩
    have haa : aLo ≤ a := by omega
    by_cases hle : a + 2 ≤ n
    · obtain ⟨b, hb⟩ : ∃ b, a + b + 2 = n :=
        ⟨n - a - 2, by omega⟩
      have hbb : b ≤ bHi := by omega
      rw [relaxedTriChain_apply r hb h3]
      dsimp only [u]
      exact relaxedTriStep_conserve_on_region
        r β a b aLo bHi (by omega) haa hbb hβ1 hfireβ hcorner
    · by_cases hcons : a + 1 = n
      · subst hcons
        rw [relaxedTriChain_consensus_X r h3, expect_pure]
      · unfold relaxedTriChain
        rw [dif_neg (by omega), expect_pure]
  refine feller_ruin_u
    (K := relaxedTriChain r n) id aLo k u hu1 hu0
    (fun z => u ^ z) (fun _ => rfl)
    (freeze_conserve hoff) (aLo + k) rfl

/-- Two-boundary Feller safety with a state-varying local odds certificate.

The analyzed kernel is stopped at the upper boundary.  The outer `hitProb`
adds the lower stopping boundary, so the left side is the lower-first event for
this explicitly stopped finite chain. -/
theorem relaxed_band_feller_varying_beta
    (r : RelaxedRate)
    (n lower upper gap : ℕ)
    (β₀ : NNReal) (β : ℕ → NNReal)
    (h3 : 3 ≤ n) (hβ₀ : 1 ≤ β₀)
    (hlive :
      ∀ a b : ℕ,
        a + b + 2 = n →
        lower ≤ a →
        a + 1 < upper →
        β₀ ≤ β (a + 1) ∧
          β (a + 1) * (b + 1 : NNReal) ≤
            r.fire * (a + 1 : NNReal)) :
    ⨆ T : ℕ,
        hitProb (fun x : ℕ => x ≤ lower)
          (freeze (fun x : ℕ => upper ≤ x) (relaxedTriChain r n))
          T (lower + gap) ≤
      (β₀ : ℝ≥0∞)⁻¹ ^ gap := by
  let u : ℝ≥0∞ := (β₀ : ℝ≥0∞)⁻¹
  let K : ℕ → PMF ℕ :=
    freeze (fun x : ℕ => upper ≤ x) (relaxedTriChain r n)
  have hu1 : u ≤ 1 := by
    dsimp only [u]
    exact ENNReal.inv_le_one.mpr (by exact_mod_cast hβ₀)
  have hu0 : u ≠ 0 := by
    dsimp only [u]
    exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  have hfireOne : r.fire ≤ 1 := by
    rw [← r.add_eq_one]
    exact le_add_right le_rfl
  have hfireβ₀ : r.fire ≤ β₀ := hfireOne.trans hβ₀
  have hoff :
      ∀ x : ℕ, ¬x ≤ lower →
        expect (K x) (fun z => u ^ z) ≤ u ^ x := by
    intro x hxLower
    by_cases hxUpper : upper ≤ x
    · rw [show K x = PMF.pure x by
        simp only [K, freeze_of_mem x hxUpper], expect_pure]
    · rw [show K x = relaxedTriChain r n x by
        simp only [K, freeze_of_not_mem x hxUpper]]
      by_cases hxPhys : x ≤ n
      · by_cases hxCons : x = n
        · subst x
          rw [relaxedTriChain_consensus_X r h3, expect_pure]
        · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 :=
            ⟨x - 1, by omega⟩
          obtain ⟨b, hpop⟩ : ∃ b, a + b + 2 = n :=
            ⟨n - a - 2, by omega⟩
          rw [relaxedTriChain_apply r hpop h3]
          obtain ⟨hfloor, hbias⟩ :=
            hlive a b hpop (by omega) (by omega)
          have hbias₀ :
              β₀ * (b + 1 : NNReal) ≤
                r.fire * (a + 1 : NNReal) := by
            calc
              β₀ * (b + 1 : NNReal) ≤
                  β (a + 1) * (b + 1 : NNReal) :=
                by
                  simpa only [mul_comm] using
                    mul_le_mul_right hfloor (b + 1 : NNReal)
              _ ≤ r.fire * (a + 1 : NNReal) := hbias
          dsimp only [u]
          exact relaxedTriStep_conserve_of_bias
            r β₀ a b (by omega) hβ₀ hfireβ₀ hbias₀
      · unfold relaxedTriChain
        rw [dif_neg (by omega), expect_pure]
  exact feller_ruin_u
    (K := K) id lower gap u hu1 hu0
    (fun z => u ^ z) (fun _ => rfl)
    (freeze_conserve hoff) (lower + gap) rfl

end Tri

#print axioms Tri.relaxed_feller
#print axioms Tri.relaxed_band_feller_varying_beta

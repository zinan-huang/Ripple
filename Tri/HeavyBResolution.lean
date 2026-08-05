/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBDirection
import Tri.DoubleBResolution

/-!
# Heavy-B level expectation and conservation

This file proves the 6-label expectation expansion of `heavyLevel` under
`heavyStateStep`, then uses `feller_reduced` to establish the one-step
geometric conservation that feeds the Feller ruin bound.

## Level ↔ co-level partition

Under `HeavyInv n`, `heavyLevel + coLevel = n` where `coLevel = y + b`.
This is half the Double-B scale (`2n → n`) and the level values are concrete.
-/

namespace Tri

open scoped ENNReal

/-! ### Per-label level values on `PairComp.nextHeavyState` -/

theorem nextHS_level_xb {n : ℕ} (s : HeavyState n) (a : ℕ)
    (ha : BiCfg.heavyLevel s.1 = a + 1) (hw : s.1.x * s.1.b ≠ 0) :
    BiCfg.heavyLevel (PairComp.nextHeavyState s PairComp.xb).1 = a + 2 := by
  have hb : 0 < s.1.b := Nat.pos_of_ne_zero (fun h => hw (by simp [h]))
  rw [PairComp.nextHeavyState, dif_neg (by simpa [PairComp.weight] using hw)]
  simp only [BiCfg.heavyLevel, PairComp.heavyNext] at ha ⊢; omega

theorem nextHS_level_yb {n : ℕ} (s : HeavyState n) (a : ℕ)
    (ha : BiCfg.heavyLevel s.1 = a + 1) (hw : s.1.y * s.1.b ≠ 0) :
    BiCfg.heavyLevel (PairComp.nextHeavyState s PairComp.yb).1 + 1 = a + 1 := by
  have hb : 0 < s.1.b := Nat.pos_of_ne_zero (fun h => hw (by simp [h]))
  rw [PairComp.nextHeavyState, dif_neg (by simpa [PairComp.weight] using hw)]
  simp only [BiCfg.heavyLevel, PairComp.heavyNext] at ha ⊢; omega

theorem nextHS_level_xy {n : ℕ} (s : HeavyState n) (a : ℕ)
    (ha : BiCfg.heavyLevel s.1 = a + 1) :
    BiCfg.heavyLevel (PairComp.nextHeavyState s PairComp.xy).1 = a + 1 := by
  rw [PairComp.nextHeavyState]
  by_cases hw : PairComp.weight s.1.x s.1.y s.1.b PairComp.xy = 0
  · rw [dif_pos hw]; exact ha
  · rw [dif_neg hw]
    have hx : 0 < s.1.x := Nat.pos_of_ne_zero (fun h => hw (by simp [PairComp.weight, h]))
    simp only [BiCfg.heavyLevel, PairComp.heavyNext] at ha ⊢; omega

theorem nextHS_level_inert {n : ℕ} (s : HeavyState n) (a : ℕ)
    (ha : BiCfg.heavyLevel s.1 = a + 1) (k : PairComp)
    (hk : k = .xx ∨ k = .yy ∨ k = .bb) :
    BiCfg.heavyLevel (PairComp.nextHeavyState s k).1 = a + 1 := by
  rw [PairComp.nextHeavyState]
  by_cases hw : PairComp.weight s.1.x s.1.y s.1.b k = 0
  · rw [dif_pos hw]; exact ha
  · rw [dif_neg hw]; rcases hk with h | h | h <;> subst h <;>
      simp only [PairComp.heavyNext, BiCfg.heavyLevel] at ha ⊢ <;> omega

/-! ### The 6-label expectation expansion -/

theorem heavyStateStep_expect_level {n : ℕ} (hn : 3 ≤ n) (s : HeavyState n) (a : ℕ)
    (ha : BiCfg.heavyLevel s.1 = a + 1) (F : ℕ → ℝ≥0∞) :
    expect (heavyStateStep n s) (fun z => F (BiCfg.heavyLevel z.1))
      = heavyResolveDown s * F a
        + heavyNeutralMass (heavy_two_entities hn s) * F (a + 1)
        + heavyResolveUp s * F (a + 2) := by
  have hh := heavy_two_entities hn s
  have hup : dbPairPMF s.1.x s.1.y s.1.b hh .xb = heavyResolveUp s :=
    (heavyResolveUp_eq s hh).symm
  have hdown : dbPairPMF s.1.x s.1.y s.1.b hh .yb = heavyResolveDown s :=
    (heavyResolveDown_eq s hh).symm
  have hxbT : dbPairPMF s.1.x s.1.y s.1.b hh .xb *
      F (BiCfg.heavyLevel (PairComp.nextHeavyState s .xb).1)
      = heavyResolveUp s * F (a + 2) := by
    by_cases hw : s.1.x * s.1.b = 0
    · rw [dbPairPMF_zero_of_weight_zero (by simpa [PairComp.weight] using hw)]
      have h0 : heavyResolveUp s = 0 := by unfold heavyResolveUp; rw [hw]; simp
      rw [h0]; simp
    · rw [nextHS_level_xb s a ha hw, hup]
  have hybT : dbPairPMF s.1.x s.1.y s.1.b hh .yb *
      F (BiCfg.heavyLevel (PairComp.nextHeavyState s .yb).1)
      = heavyResolveDown s * F a := by
    by_cases hw : s.1.y * s.1.b = 0
    · rw [dbPairPMF_zero_of_weight_zero (by simpa [PairComp.weight] using hw)]
      have h0 : heavyResolveDown s = 0 := by unfold heavyResolveDown; rw [hw]; simp
      rw [h0]; simp
    · have hlev : BiCfg.heavyLevel (PairComp.nextHeavyState s .yb).1 = a := by
        have := nextHS_level_yb s a ha hw; omega
      rw [hlev, hdown]
  have hunfold : heavyStateStep n s =
      (dbPairPMF s.1.x s.1.y s.1.b hh).map (PairComp.nextHeavyState s) := by
    unfold heavyStateStep; exact dif_pos hh
  rw [hunfold, expect_map]
  unfold expect; rw [tsum_fintype]; simp only [Function.comp_apply]
  rw [show (Finset.univ : Finset PairComp)
      = {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb, PairComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [nextHS_level_inert s a ha .xx (by tauto), nextHS_level_xy s a ha,
    nextHS_level_inert s a ha .yy (Or.inr (Or.inl rfl)), hxbT, hybT,
    nextHS_level_inert s a ha .bb (Or.inr (Or.inr rfl))]
  unfold heavyNeutralMass
  ring

/-! ### Resolution bias in the majority region -/

theorem heavyResolve_down_le {n : ℕ} (aLo bHi : ℕ) (hn : 3 ≤ n)
    (s : HeavyState n) (haLo : 0 < aLo)
    (halo : aLo ≤ BiCfg.heavyLevel s.1 - 1)
    (hbhi : s.1.y + s.1.b - 1 ≤ bHi)
    (hmaj : bHi ≤ aLo) :
    heavyResolveDown s ≤ heavyResolveUp s * ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) := by
  have hLv : BiCfg.heavyLevel s.1 = s.1.x + s.1.b := rfl
  have hloN : aLo ≤ s.1.x + s.1.b - 1 := by rw [hLv] at halo; exact halo
  have hlo2 : aLo + 1 ≤ s.1.x + s.1.b := by omega
  have hhi2 : s.1.y + s.1.b ≤ bHi + 1 := by omega
  have hkey : s.1.y * s.1.b * aLo ≤ s.1.x * s.1.b * bHi := by
    rcases Nat.eq_zero_or_pos s.1.b with hb | hb
    · simp [hb]
    · have hx : s.1.y ≤ s.1.x := by omega
      have h1 : s.1.y * aLo ≤ s.1.x * bHi := by nlinarith [hb, hx, hloN, hbhi]
      calc s.1.y * s.1.b * aLo = s.1.b * (s.1.y * aLo) := by ring
        _ ≤ s.1.b * (s.1.x * bHi) := Nat.mul_le_mul_left _ h1
        _ = s.1.x * s.1.b * bHi := by ring
  unfold heavyResolveDown heavyResolveUp
  have hEnt := heavy_two_entities hn s
  have hCpos : 0 < Nat.choose (heavyEntities s) 2 := Nat.choose_pos hEnt
  have hCR : (0 : ℝ) < (Nat.choose (heavyEntities s) 2 : ℝ) := by exact_mod_cast hCpos
  have haLoRpos : (0 : ℝ) < (aLo : ℝ) := by exact_mod_cast haLo
  have hdt : (s.1.y * s.1.b : ℕ) / (Nat.choose (heavyEntities s) 2 : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hCpos.ne')
  have hrt : (s.1.x * s.1.b : ℕ) / (Nat.choose (heavyEntities s) 2 : ℝ≥0∞) *
      ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hCpos.ne'))
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp only [ne_eq, Nat.cast_eq_zero]; omega))
  rw [← ENNReal.toReal_le_toReal hdt hrt]
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  rw [div_mul_div_comm, div_le_div_iff₀ hCR (by positivity)]
  push_cast
  have hkeyR : (s.1.y : ℝ) * s.1.b * aLo ≤ (s.1.x : ℝ) * s.1.b * bHi := by exact_mod_cast hkey
  nlinarith [mul_le_mul_of_nonneg_left hkeyR hCR.le, hCR]

/-! ### Feller conservation -/

theorem heavyState_conserve_on_region {n : ℕ} (aLo bHi : ℕ) (hn : 3 ≤ n)
    (haLo : 0 < aLo) (hmaj : bHi ≤ aLo) (s : HeavyState n)
    (halo : aLo < BiCfg.heavyLevel s.1) (hbhi : s.1.y + s.1.b ≤ bHi + 1) :
    expect (heavyStateStep n s) (fun z => ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ BiCfg.heavyLevel z.1)
      ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ BiCfg.heavyLevel s.1 := by
  set u : ℝ≥0∞ := (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) with hu
  have haLone : (aLo : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have haLotop : (aLo : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hu1 : u ≤ 1 := by
    rw [hu]; calc (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) ≤ (aLo : ℝ≥0∞) / (aLo : ℝ≥0∞) :=
        ENNReal.div_le_div_right (by exact_mod_cast hmaj) _
      _ = 1 := ENNReal.div_self haLone haLotop
  have hh := heavy_two_entities hn s
  have hCpos : 0 < Nat.choose (heavyEntities s) 2 := Nat.choose_pos hh
  have hCne : ((Nat.choose (heavyEntities s) 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hCpos.ne'
  have hdt : heavyResolveDown s ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hCne
  have hut : heavyResolveUp s ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hCne
  have hnt : heavyNeutralMass hh ≠ ⊤ := by
    have hsum := heavy_mass_sum s hh
    intro h; rw [h] at hsum; simp at hsum
  have hd : heavyResolveDown s ≤ heavyResolveUp s * u := by
    rw [hu]; exact heavyResolve_down_le aLo bHi hn s haLo (by omega) (by omega) hmaj
  have hred := feller_reduced (heavyResolveDown s) (heavyNeutralMass hh)
    (heavyResolveUp s) u (heavy_mass_sum s hh) hd hu1 hdt hnt hut
  obtain ⟨a, ha⟩ : ∃ a, BiCfg.heavyLevel s.1 = a + 1 := ⟨BiCfg.heavyLevel s.1 - 1, by omega⟩
  rw [heavyStateStep_expect_level hn s a ha (fun L => u ^ L), ha]
  have hfact : heavyResolveDown s * u ^ a
      + heavyNeutralMass hh * u ^ (a + 1) + heavyResolveUp s * u ^ (a + 2)
      = u ^ a * (heavyResolveDown s + heavyNeutralMass hh * u + heavyResolveUp s * u ^ 2) := by
    rw [pow_succ, pow_succ, pow_succ]; ring
  rw [hfact, pow_succ u a]
  exact mul_le_mul_left' hred _

end Tri

#print axioms Tri.nextHS_level_xb
#print axioms Tri.nextHS_level_yb
#print axioms Tri.nextHS_level_xy
#print axioms Tri.nextHS_level_inert
#print axioms Tri.heavyStateStep_expect_level
#print axioms Tri.heavyResolve_down_le
#print axioms Tri.heavyState_conserve_on_region

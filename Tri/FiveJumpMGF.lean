/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Drift

/-!
# Five-jump geometric drift

This is the scalar core needed by the multi-species fixed-pair argument. The
physical pair gap has jumps `-2,-1,0,+1,+2`; no projection of the full
configuration is assumed to be Markov.
-/

namespace Tri

open scoped ENNReal

/-- Real scalar MGF inequality for jumps `-2,-1,0,+1,+2`.

`down1 ≤ up1*u` pays for a one-unit adverse jump, while
`down2 ≤ up2*u^2` pays for a two-unit adverse jump. -/
theorem five_jump_mgf_core_real
    {down2 down1 stay up1 up2 u : ℝ}
    (hsum : down2 + down1 + stay + up1 + up2 = 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h1 : down1 ≤ up1 * u)
    (h2 : down2 ≤ up2 * u ^ 2) :
    down2 + down1 * u + stay * u ^ 2 +
        up1 * u ^ 3 + up2 * u ^ 4 ≤ u ^ 2 := by
  have huOne : 0 ≤ u * (1 - u) :=
    mul_nonneg hu0 (sub_nonneg.mpr hu1)
  have huSq : u ^ 2 ≤ 1 := by
    nlinarith
  have hpair1 :
      0 ≤ u * (1 - u) * (up1 * u - down1) :=
    mul_nonneg huOne (sub_nonneg.mpr h1)
  have hpair2 :
      0 ≤ (1 - u ^ 2) * (up2 * u ^ 2 - down2) :=
    mul_nonneg (sub_nonneg.mpr huSq) (sub_nonneg.mpr h2)
  nlinarith

/-- `ℝ≥0∞` form of the scalar five-jump MGF inequality.  Finiteness follows
from the five masses summing to one and from `u ≤ 1`. -/
theorem five_jump_mgf_core
    {down2 down1 stay up1 up2 u : ℝ≥0∞}
    (hsum : down2 + down1 + stay + up1 + up2 = 1)
    (hu1 : u ≤ 1)
    (h1 : down1 ≤ up1 * u)
    (h2 : down2 ≤ up2 * u ^ 2) :
    down2 + down1 * u + stay * u ^ 2 +
        up1 * u ^ 3 + up2 * u ^ 4 ≤ u ^ 2 := by
  have hd2le : down2 ≤ 1 := by
    rw [← hsum]
    exact le_add_right (le_add_right (le_add_right (le_add_right le_rfl)))
  have hd1le : down1 ≤ 1 := by
    rw [← hsum]
    calc
      down1 ≤ down2 + down1 := le_add_left le_rfl
      _ ≤ down2 + down1 + stay + up1 + up2 :=
        le_add_right (le_add_right (le_add_right le_rfl))
  have hstayle : stay ≤ 1 := by
    rw [← hsum]
    calc
      stay ≤ down2 + down1 + stay := le_add_left le_rfl
      _ ≤ down2 + down1 + stay + up1 + up2 :=
        le_add_right (le_add_right le_rfl)
  have hu1le : up1 ≤ 1 := by
    rw [← hsum]
    calc
      up1 ≤ down2 + down1 + stay + up1 := le_add_left le_rfl
      _ ≤ down2 + down1 + stay + up1 + up2 :=
        le_add_right le_rfl
  have hu2le : up2 ≤ 1 := by
    rw [← hsum]
    exact le_add_left le_rfl
  have fd2 : down2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hd2le
  have fd1 : down1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hd1le
  have fstay : stay ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hstayle
  have fu1 : up1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu1le
  have fu2 : up2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu2le
  have fu : u ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  have fdu : down1 * u ≠ ⊤ := ENNReal.mul_ne_top fd1 fu
  have fsu2 : stay * u ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top fstay (ENNReal.pow_ne_top fu)
  have fu13 : up1 * u ^ 3 ≠ ⊤ :=
    ENNReal.mul_ne_top fu1 (ENNReal.pow_ne_top fu)
  have fu24 : up2 * u ^ 4 ≠ ⊤ :=
    ENNReal.mul_ne_top fu2 (ENNReal.pow_ne_top fu)
  have fL :
      down2 + down1 * u + stay * u ^ 2 +
          up1 * u ^ 3 + up2 * u ^ 4 ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr
          ⟨ENNReal.add_ne_top.mpr ⟨fd2, fdu⟩, fsu2⟩, fu13⟩,
        fu24⟩
  rw [← ENNReal.toReal_le_toReal fL (ENNReal.pow_ne_top fu)]
  rw [ENNReal.toReal_add
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.add_ne_top.mpr
            ⟨ENNReal.add_ne_top.mpr ⟨fd2, fdu⟩, fsu2⟩, fu13⟩)
        fu24,
      ENNReal.toReal_add
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.add_ne_top.mpr ⟨fd2, fdu⟩, fsu2⟩)
        fu13,
      ENNReal.toReal_add
        (ENNReal.add_ne_top.mpr ⟨fd2, fdu⟩) fsu2,
      ENNReal.toReal_add fd2 fdu,
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow]
  simp only [ENNReal.toReal_pow]
  refine five_jump_mgf_core_real ?_
    ENNReal.toReal_nonneg ?_ ?_ ?_
  · have h := congrArg ENNReal.toReal hsum
    rwa [ENNReal.toReal_add
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.add_ne_top.mpr
              ⟨ENNReal.add_ne_top.mpr ⟨fd2, fd1⟩, fstay⟩, fu1⟩)
          fu2,
        ENNReal.toReal_add
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.add_ne_top.mpr ⟨fd2, fd1⟩, fstay⟩)
          fu1,
        ENNReal.toReal_add
          (ENNReal.add_ne_top.mpr ⟨fd2, fd1⟩) fstay,
        ENNReal.toReal_add fd2 fd1,
        ENNReal.toReal_one] at h
  · exact
      (ENNReal.toReal_le_toReal fu ENNReal.one_ne_top).mpr hu1
        |>.trans_eq ENNReal.toReal_one
  · have h :=
      (ENNReal.toReal_le_toReal fd1 (ENNReal.mul_ne_top fu1 fu)).mpr h1
    rwa [ENNReal.toReal_mul] at h
  · have h :=
      (ENNReal.toReal_le_toReal fd2
        (ENNReal.mul_ne_top fu2 (ENNReal.pow_ne_top fu))).mpr h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow] at h

/-- Once the scalar five-mass inequality is available in `ℝ≥0∞`, it lifts
exactly to a geometric potential at every gap `g ≥ 2`. -/
theorem five_jump_geometric_of_core
    {down2 down1 stay up1 up2 u : ℝ≥0∞} {g : ℕ}
    (hg : 2 ≤ g)
    (hcore :
      down2 + down1 * u + stay * u ^ 2 +
          up1 * u ^ 3 + up2 * u ^ 4 ≤ u ^ 2) :
    down2 * u ^ (g - 2) +
        down1 * u ^ (g - 1) +
        stay * u ^ g +
        up1 * u ^ (g + 1) +
        up2 * u ^ (g + 2) ≤
      u ^ g := by
  have hgm1 : g - 1 = (g - 2) + 1 := by omega
  have hg0 : g = (g - 2) + 2 := by omega
  have hgp1 : g + 1 = (g - 2) + 3 := by omega
  have hgp2 : g + 2 = (g - 2) + 4 := by omega
  have hpowm1 :
      u ^ (g - 1) = u ^ (g - 2) * u := by
    rw [hgm1, pow_add]
    simp
  have hpow0 :
      u ^ g = u ^ (g - 2) * u ^ 2 := by
    calc
      u ^ g = u ^ ((g - 2) + 2) := congrArg (fun k : ℕ => u ^ k) hg0
      _ = u ^ (g - 2) * u ^ 2 := pow_add _ _ _
  have hpowp1 :
      u ^ (g + 1) = u ^ (g - 2) * u ^ 3 := by
    rw [hgp1, pow_add]
  have hpowp2 :
      u ^ (g + 2) = u ^ (g - 2) * u ^ 4 := by
    rw [hgp2, pow_add]
  calc
    down2 * u ^ (g - 2) +
          down1 * u ^ (g - 1) +
          stay * u ^ g +
          up1 * u ^ (g + 1) +
          up2 * u ^ (g + 2) =
        u ^ (g - 2) *
          (down2 + down1 * u + stay * u ^ 2 +
            up1 * u ^ 3 + up2 * u ^ 4) := by
      rw [hpowm1, hpow0, hpowp1, hpowp2]
      ring
    _ ≤ u ^ (g - 2) * u ^ 2 :=
      mul_le_mul_right hcore _
    _ = u ^ g := hpow0.symm

/-- A pointwise one-step supermartingale estimate iterates for every finite
horizon. -/
theorem expect_iter_conserve
    {α : Type*} (K : α → PMF α) (V : α → ℝ≥0∞)
    (hstep : ∀ s, expect (K s) V ≤ V s)
    (T : ℕ) (s0 : α) :
    expect (iter K T s0) V ≤ V s0 := by
  have hstep' : ∀ s, expect (K s) V ≤ (1 : ℝ≥0∞) * V s := by
    intro s
    simpa using hstep s
  simpa using expect_iter_le K V 1 hstep' T s0

/-- Markov conversion for any terminal bad predicate. -/
theorem bad_mass_le_expect_div
    {α : Type*} (p : PMF α) (V : α → ℝ≥0∞)
    (Bad : α → Prop) [DecidablePred Bad]
    (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ⊤)
    (hbad : ∀ s, Bad s → θ ≤ V s) :
    (∑' s, if Bad s then p s else 0) ≤ expect p V / θ := by
  calc
    (∑' s, if Bad s then p s else 0) ≤
        ∑' s, if θ ≤ V s then p s else 0 := by
      refine ENNReal.tsum_le_tsum fun s => ?_
      by_cases hs : Bad s
      · have hθ := hbad s hs
        simp [hs, hθ]
      · simp [hs]
    _ ≤ expect p V / θ :=
      markov_div p V θ hθ0 hθtop

/-- Finite-horizon hitting wrapper once the physical stopped kernel has the
one-step potential estimate. -/
theorem stopped_bad_mass_le
    {α : Type*} (K : α → PMF α) (V : α → ℝ≥0∞)
    (Bad : α → Prop) [DecidablePred Bad]
    (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ⊤)
    (hstep : ∀ s, expect (K s) V ≤ V s)
    (hbad : ∀ s, Bad s → θ ≤ V s)
    (T : ℕ) (s0 : α) :
    (∑' s, if Bad s then iter K T s0 s else 0) ≤
      V s0 / θ := by
  exact (bad_mass_le_expect_div
    (iter K T s0) V Bad θ hθ0 hθtop hbad).trans
      (ENNReal.div_le_div_right
        (expect_iter_conserve K V hstep T s0) θ)

end Tri

#print axioms Tri.five_jump_mgf_core_real
#print axioms Tri.five_jump_mgf_core
#print axioms Tri.five_jump_geometric_of_core
#print axioms Tri.stopped_bad_mass_le

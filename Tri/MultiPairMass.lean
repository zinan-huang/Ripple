/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiPairJump

/-!
# Physical five-mass decomposition for a fixed species pair

For a fixed ordered pair `X,Y`, every physical unordered-triple sample changes
the signed gap `count X - count Y` by one of `-2,-1,0,+1,+2`.  This file
records the five physical masses directly on the sample space.  The extreme
fibers are exactly the two direct reactions `Y+Y+X -> Y+Y+Y` and
`X+X+Y -> X+X+X`.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Physical probability mass of samples producing one specified signed
increment of the fixed pair gap. -/
noncomputable def pairDeltaMass
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (k : ℤ) : ℝ≥0∞ :=
  ∑' t : TripleSample c,
    if samplePairDelta t X Y = k then triplePMF c h3 t else 0

/-- The five possible physical jump masses partition one raw interaction. -/
theorem pairDeltaMass_five_sum
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) :
    pairDeltaMass c h3 X Y (-2) +
        pairDeltaMass c h3 X Y (-1) +
        pairDeltaMass c h3 X Y 0 +
        pairDeltaMass c h3 X Y 1 +
        pairDeltaMass c h3 X Y 2 = 1 := by
  classical
  unfold pairDeltaMass
  simp only [tsum_fintype]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    ∑ t : TripleSample c,
        (((if samplePairDelta t X Y = -2 then triplePMF c h3 t else 0) +
          (if samplePairDelta t X Y = -1 then triplePMF c h3 t else 0) +
          (if samplePairDelta t X Y = 0 then triplePMF c h3 t else 0) +
          (if samplePairDelta t X Y = 1 then triplePMF c h3 t else 0)) +
          (if samplePairDelta t X Y = 2 then triplePMF c h3 t else 0)) =
        ∑ t : TripleSample c, triplePMF c h3 t := by
      apply Finset.sum_congr rfl
      intro t _ht
      have hlo := samplePairDelta_lower t X Y
      have hhi := samplePairDelta_upper t X Y
      have hcases :
          samplePairDelta t X Y = -2 ∨
          samplePairDelta t X Y = -1 ∨
          samplePairDelta t X Y = 0 ∨
          samplePairDelta t X Y = 1 ∨
          samplePairDelta t X Y = 2 := by
        omega
      rcases hcases with h | h | h | h | h <;> simp [h]
    _ = ∑' t : TripleSample c, triplePMF c h3 t := by
      rw [tsum_fintype]
    _ = 1 := PMF.tsum_coe _

/-- A physical sample has pair-gap increment `+2` exactly when it is the
direct `X`-wins-`Y` firing. -/
theorem samplePairDelta_eq_two_iff_fire
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) (hXY : X ≠ Y) :
    samplePairDelta t X Y = 2 ↔ IsFirePair t (X, Y) := by
  classical
  cases hclass : classify t with
  | none =>
      have hnofire : ¬ IsFirePair t (X, Y) :=
        (classify_eq_none_iff t).mp hclass (X, Y)
      simp [samplePairDelta, hclass, hnofire]
  | some p =>
      have hdelta :=
        directedPairDelta_eq_two_iff p.2.1 hXY
      constructor
      · intro h
        have hd : directedPairDelta p.1.1 p.1.2 X Y = 2 := by
          simpa [samplePairDelta, hclass] using h
        rcases hdelta.mp hd with ⟨hw, hl⟩
        have hp : p.1 = (X, Y) := Prod.ext hw hl
        rw [← hp]
        exact p.2
      · intro hfire
        have hp : p.1 = (X, Y) :=
          isFirePair_unique t p.2 hfire
        have hw : p.1.1 = X := congrArg Prod.fst hp
        have hl : p.1.2 = Y := congrArg Prod.snd hp
        simp only [samplePairDelta, hclass]
        exact hdelta.mpr ⟨hw, hl⟩

/-- A physical sample has pair-gap increment `-2` exactly when it is the
direct `Y`-wins-`X` firing. -/
theorem samplePairDelta_eq_neg_two_iff_fire
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) (hXY : X ≠ Y) :
    samplePairDelta t X Y = -2 ↔ IsFirePair t (Y, X) := by
  classical
  cases hclass : classify t with
  | none =>
      have hnofire : ¬ IsFirePair t (Y, X) :=
        (classify_eq_none_iff t).mp hclass (Y, X)
      simp [samplePairDelta, hclass, hnofire]
  | some p =>
      have hdelta :=
        directedPairDelta_eq_neg_two_iff p.2.1 hXY
      constructor
      · intro h
        have hd : directedPairDelta p.1.1 p.1.2 X Y = -2 := by
          simpa [samplePairDelta, hclass] using h
        rcases hdelta.mp hd with ⟨hw, hl⟩
        have hp : p.1 = (Y, X) := Prod.ext hw hl
        rw [← hp]
        exact p.2
      · intro hfire
        have hp : p.1 = (Y, X) :=
          isFirePair_unique t p.2 hfire
        have hw : p.1.1 = Y := congrArg Prod.fst hp
        have hl : p.1.2 = X := congrArg Prod.snd hp
        simp only [samplePairDelta, hclass]
        exact hdelta.mpr ⟨hw, hl⟩

/-- Membership in the fixed pair's third-species set, exposed in the order
used by the nested erasures. -/
theorem mem_thirdSpecies_iff
    (X Y Z : Species m) :
    Z ∈ thirdSpecies X Y ↔ Z ≠ Y ∧ Z ≠ X := by
  simp [thirdSpecies]

/-- The set of species outside a fixed pair is independent of the order of
that pair. -/
theorem thirdSpecies_comm
    (X Y : Species m) :
    thirdSpecies X Y = thirdSpecies Y X := by
  classical
  unfold thirdSpecies
  rw [Finset.erase_right_comm]

/-- A `+1` pair-gap jump is exactly one of the two favorable reactions
involving a unique third species. -/
theorem samplePairDelta_eq_one_iff_third
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) (hXY : X ≠ Y) :
    samplePairDelta t X Y = 1 ↔
      ∃ Z ∈ thirdSpecies X Y,
        IsFirePair t (X, Z) ∨ IsFirePair t (Z, Y) := by
  classical
  cases hclass : classify t with
  | none =>
      have hnofire :=
        (classify_eq_none_iff t).mp hclass
      constructor
      · intro h
        simp [samplePairDelta, hclass] at h
      · rintro ⟨Z, _hZ, hfire | hfire⟩
        · exact False.elim (hnofire (X, Z) hfire)
        · exact False.elim (hnofire (Z, Y) hfire)
  | some p =>
      have hdelta :=
        directedPairDelta_eq_one_iff p.2.1 hXY
      constructor
      · intro h
        have hd : directedPairDelta p.1.1 p.1.2 X Y = 1 := by
          simpa [samplePairDelta, hclass] using h
        rcases hdelta.mp hd with hleft | hright
        · let Z := p.1.2
          have hZX : Z ≠ X := by
            intro h
            exact p.2.1 (hleft.1.trans h.symm)
          have hZY : Z ≠ Y := hleft.2
          refine ⟨Z, (mem_thirdSpecies_iff X Y Z).2 ⟨hZY, hZX⟩,
            Or.inl ?_⟩
          have hp : p.1 = (X, Z) := Prod.ext hleft.1 rfl
          rw [← hp]
          exact p.2
        · let Z := p.1.1
          have hZX : Z ≠ X := hright.2
          have hZY : Z ≠ Y := by
            intro h
            exact p.2.1 (h.trans hright.1.symm)
          refine ⟨Z, (mem_thirdSpecies_iff X Y Z).2 ⟨hZY, hZX⟩,
            Or.inr ?_⟩
          have hp : p.1 = (Z, Y) := Prod.ext rfl hright.1
          rw [← hp]
          exact p.2
      · rintro ⟨Z, hZ, hfire | hfire⟩
        · have hp : p.1 = (X, Z) :=
            isFirePair_unique t p.2 hfire
          have hw : p.1.1 = X := congrArg Prod.fst hp
          have hl : p.1.2 = Z := congrArg Prod.snd hp
          have hZY : Z ≠ Y :=
            (mem_thirdSpecies_iff X Y Z).1 hZ |>.1
          have hloserY : p.1.2 ≠ Y := by
            rw [hl]
            exact hZY
          simp only [samplePairDelta, hclass]
          exact hdelta.mpr (Or.inl ⟨hw, hloserY⟩)
        · have hp : p.1 = (Z, Y) :=
            isFirePair_unique t p.2 hfire
          have hw : p.1.1 = Z := congrArg Prod.fst hp
          have hl : p.1.2 = Y := congrArg Prod.snd hp
          have hZX : Z ≠ X :=
            (mem_thirdSpecies_iff X Y Z).1 hZ |>.2
          have hwinnerX : p.1.1 ≠ X := by
            rw [hw]
            exact hZX
          simp only [samplePairDelta, hclass]
          exact hdelta.mpr (Or.inr ⟨hl, hwinnerX⟩)

/-- Swapping the tracked species negates every physical pair-gap jump. -/
theorem samplePairDelta_swap
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) :
    samplePairDelta t Y X = -samplePairDelta t X Y := by
  classical
  cases hclass : classify t with
  | none => simp [samplePairDelta, hclass]
  | some p =>
      simp only [samplePairDelta, hclass]
      unfold directedPairDelta
      ring

/-- Swapping the tracked pair and negating the requested jump preserves its
physical mass. -/
theorem pairDeltaMass_swap
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (k : ℤ) :
    pairDeltaMass c h3 X Y k =
      pairDeltaMass c h3 Y X (-k) := by
  classical
  unfold pairDeltaMass
  apply tsum_congr
  intro t
  by_cases h : samplePairDelta t X Y = k
  · have hs : samplePairDelta t Y X = -k := by
      rw [samplePairDelta_swap t X Y, h]
    simp [h, hs]
  · have hs : samplePairDelta t Y X ≠ -k := by
      intro hs
      rw [samplePairDelta_swap t X Y] at hs
      exact h (by omega)
    simp [h, hs]

/-- A `-1` pair-gap jump is exactly one of the two adverse reactions
involving a unique third species. -/
theorem samplePairDelta_eq_neg_one_iff_third
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) (hXY : X ≠ Y) :
    samplePairDelta t X Y = -1 ↔
      ∃ Z ∈ thirdSpecies X Y,
        IsFirePair t (Z, X) ∨ IsFirePair t (Y, Z) := by
  constructor
  · intro h
    have hswap : samplePairDelta t Y X = 1 := by
      rw [samplePairDelta_swap t X Y]
      omega
    rcases
        (samplePairDelta_eq_one_iff_third t Y X (Ne.symm hXY)).mp hswap with
      ⟨Z, hZ, hfire⟩
    have hmem : Z ∈ thirdSpecies X Y := by
      have hz := (mem_thirdSpecies_iff Y X Z).1 hZ
      exact (mem_thirdSpecies_iff X Y Z).2 ⟨hz.2, hz.1⟩
    exact ⟨Z, hmem, hfire.symm⟩
  · rintro ⟨Z, hZ, hfire⟩
    have hmem : Z ∈ thirdSpecies Y X := by
      have hz := (mem_thirdSpecies_iff X Y Z).1 hZ
      exact (mem_thirdSpecies_iff Y X Z).2 ⟨hz.2, hz.1⟩
    have hswap : samplePairDelta t Y X = 1 :=
      (samplePairDelta_eq_one_iff_third t Y X (Ne.symm hXY)).2
        ⟨Z, hmem, hfire.symm⟩
    rw [samplePairDelta_swap t X Y] at hswap
    omega

/-- Indicator mass for one directed firing predicate. -/
noncomputable def fireIndicator
    {c : Config m n} (t : TripleSample c)
    (p : Species m × Species m) (q : ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact if IsFirePair t p then q else 0

/-- Pointwise partition of a `+1` jump among the two favorable third-species
reaction families.  Uniqueness of `classify` ensures that exactly one summand
is nonzero. -/
theorem thirdPartyUp_indicator_sum_eq
    {c : Config m n} (t : TripleSample c)
    (X Y : Species m) (hXY : X ≠ Y) (q : ℝ≥0∞) :
    (∑ Z ∈ thirdSpecies X Y,
        (fireIndicator t (X, Z) q +
          fireIndicator t (Z, Y) q)) =
      if samplePairDelta t X Y = 1 then q else 0 := by
  classical
  by_cases hd : samplePairDelta t X Y = 1
  · rw [if_pos hd]
    rcases
        (samplePairDelta_eq_one_iff_third t X Y hXY).mp hd with
      ⟨Z, hZ, hfire | hfire⟩
    · have hz := (mem_thirdSpecies_iff X Y Z).1 hZ
      have hother : ¬ IsFirePair t (Z, Y) := by
        intro hother
        have hp := isFirePair_unique t hfire hother
        have hxz : X = Z := congrArg Prod.fst hp
        exact hz.2 hxz.symm
      calc
        (∑ W ∈ thirdSpecies X Y,
            (fireIndicator t (X, W) q +
              fireIndicator t (W, Y) q)) =
            (fireIndicator t (X, Z) q +
              fireIndicator t (Z, Y) q) := by
          apply Finset.sum_eq_single_of_mem Z hZ
          intro W hW hWZ
          ·
            have hw := (mem_thirdSpecies_iff X Y W).1 hW
            have hfirst : ¬ IsFirePair t (X, W) := by
              intro hfirst
              have hp := isFirePair_unique t hfire hfirst
              have hzw : Z = W := congrArg Prod.snd hp
              exact hWZ hzw.symm
            have hsecond : ¬ IsFirePair t (W, Y) := by
              intro hsecond
              have hp := isFirePair_unique t hfire hsecond
              have hxw : X = W := congrArg Prod.fst hp
              exact hw.2 hxw.symm
            simp [fireIndicator, hfirst, hsecond]
        _ = q := by simp [fireIndicator, hfire, hother]
    · have hz := (mem_thirdSpecies_iff X Y Z).1 hZ
      have hother : ¬ IsFirePair t (X, Z) := by
        intro hother
        have hp := isFirePair_unique t hfire hother
        have hzx : Z = X := congrArg Prod.fst hp
        exact hz.2 hzx
      calc
        (∑ W ∈ thirdSpecies X Y,
            (fireIndicator t (X, W) q +
              fireIndicator t (W, Y) q)) =
            (fireIndicator t (X, Z) q +
              fireIndicator t (Z, Y) q) := by
          apply Finset.sum_eq_single_of_mem Z hZ
          intro W hW hWZ
          ·
            have hfirst : ¬ IsFirePair t (X, W) := by
              intro hfirst
              have hp := isFirePair_unique t hfire hfirst
              have hzx : Z = X := congrArg Prod.fst hp
              exact hz.2 hzx
            have hsecond : ¬ IsFirePair t (W, Y) := by
              intro hsecond
              have hp := isFirePair_unique t hfire hsecond
              have hzw : Z = W := congrArg Prod.fst hp
              exact hWZ hzw.symm
            simp [fireIndicator, hfirst, hsecond]
        _ = q := by simp [fireIndicator, hfire, hother]
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro Z hZ
    have hfirst : ¬ IsFirePair t (X, Z) := by
      intro hfire
      exact hd ((samplePairDelta_eq_one_iff_third t X Y hXY).2
        ⟨Z, hZ, Or.inl hfire⟩)
    have hsecond : ¬ IsFirePair t (Z, Y) := by
      intro hfire
      exact hd ((samplePairDelta_eq_one_iff_third t X Y hXY).2
        ⟨Z, hZ, Or.inr hfire⟩)
    simp [fireIndicator, hfirst, hsecond]

/-- The physical `+1` jump mass is exactly the aggregate favorable mass over
all third species. -/
theorem pairDeltaMass_one_eq_thirdPartyUpMass_sum
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y) :
    pairDeltaMass c h3 X Y 1 =
      ∑ Z ∈ thirdSpecies X Y, thirdPartyUpMass c h3 X Y Z := by
  classical
  unfold pairDeltaMass thirdPartyUpMass directedFireMass
  simp only [tsum_fintype]
  symm
  calc
    ∑ Z ∈ thirdSpecies X Y,
        ((∑ t : TripleSample c,
            if IsFirePair t (X, Z) then triplePMF c h3 t else 0) +
          ∑ t : TripleSample c,
            if IsFirePair t (Z, Y) then triplePMF c h3 t else 0) =
        ∑ Z ∈ thirdSpecies X Y,
          ∑ t : TripleSample c,
            ((if IsFirePair t (X, Z) then triplePMF c h3 t else 0) +
              (if IsFirePair t (Z, Y) then triplePMF c h3 t else 0)) := by
      apply Finset.sum_congr rfl
      intro Z _hZ
      rw [Finset.sum_add_distrib]
    _ = ∑ t : TripleSample c,
          ∑ Z ∈ thirdSpecies X Y,
            ((if IsFirePair t (X, Z) then triplePMF c h3 t else 0) +
              (if IsFirePair t (Z, Y) then triplePMF c h3 t else 0)) := by
      rw [Finset.sum_comm]
    _ = ∑ t : TripleSample c,
          if samplePairDelta t X Y = 1 then triplePMF c h3 t else 0 := by
      apply Finset.sum_congr rfl
      intro t _ht
      simpa [fireIndicator] using
        thirdPartyUp_indicator_sum_eq t X Y hXY (triplePMF c h3 t)

/-- The physical `-1` jump mass is exactly the aggregate adverse mass over
all third species. -/
theorem pairDeltaMass_neg_one_eq_thirdPartyDownMass_sum
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y) :
    pairDeltaMass c h3 X Y (-1) =
      ∑ Z ∈ thirdSpecies X Y, thirdPartyDownMass c h3 X Y Z := by
  calc
    pairDeltaMass c h3 X Y (-1) =
        pairDeltaMass c h3 Y X 1 := by
      simpa using pairDeltaMass_swap c h3 X Y (-1)
    _ = ∑ Z ∈ thirdSpecies Y X,
          thirdPartyUpMass c h3 Y X Z :=
      pairDeltaMass_one_eq_thirdPartyUpMass_sum
        c h3 Y X (Ne.symm hXY)
    _ = ∑ Z ∈ thirdSpecies X Y,
          thirdPartyDownMass c h3 X Y Z := by
      rw [← thirdSpecies_comm X Y]
      apply Finset.sum_congr rfl
      intro Z _hZ
      simp only [thirdPartyUpMass, thirdPartyDownMass]
      exact add_comm _ _

/-- The physical `+2` jump mass is exactly the direct favorable firing mass. -/
theorem pairDeltaMass_two_eq_directedFireMass
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y) :
    pairDeltaMass c h3 X Y 2 =
      directedFireMass c h3 X Y := by
  classical
  unfold pairDeltaMass directedFireMass
  apply tsum_congr
  intro t
  by_cases hd : samplePairDelta t X Y = 2
  · have hf :=
      (samplePairDelta_eq_two_iff_fire t X Y hXY).mp hd
    simp [hd, hf]
  · have hf : ¬ IsFirePair t (X, Y) := by
      intro hfire
      exact hd ((samplePairDelta_eq_two_iff_fire t X Y hXY).mpr hfire)
    simp [hd, hf]

/-- The physical `-2` jump mass is exactly the reverse direct firing mass. -/
theorem pairDeltaMass_neg_two_eq_directedFireMass
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y) :
    pairDeltaMass c h3 X Y (-2) =
      directedFireMass c h3 Y X := by
  classical
  unfold pairDeltaMass directedFireMass
  apply tsum_congr
  intro t
  by_cases hd : samplePairDelta t X Y = -2
  · have hf :=
      (samplePairDelta_eq_neg_two_iff_fire t X Y hXY).mp hd
    simp [hd, hf]
  · have hf : ¬ IsFirePair t (Y, X) := by
      intro hfire
      exact hd ((samplePairDelta_eq_neg_two_iff_fire t X Y hXY).mpr hfire)
    simp [hd, hf]

/-- The five physical jump masses satisfy the geometric-MGF inequality at the
common pair-gap base whenever `X` leads every species by `d`. -/
theorem pairDeltaMass_five_mgf
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hgap : HasPairwiseGap c X d) :
    pairDeltaMass c h3 X Y (-2) +
        pairDeltaMass c h3 X Y (-1) * pairGapBase n d +
        pairDeltaMass c h3 X Y 0 * pairGapBase n d ^ 2 +
        pairDeltaMass c h3 X Y 1 * pairGapBase n d ^ 3 +
        pairDeltaMass c h3 X Y 2 * pairGapBase n d ^ 4 ≤
      pairGapBase n d ^ 2 := by
  apply five_jump_mgf_core
  · exact pairDeltaMass_five_sum c h3 X Y
  · exact pairGapBase_le_one n d (by omega)
  · rw [pairDeltaMass_neg_one_eq_thirdPartyDownMass_sum
        c h3 X Y hXY,
      pairDeltaMass_one_eq_thirdPartyUpMass_sum
        c h3 X Y hXY]
    exact thirdPartyDownMass_sum_le_up_mul_base
      c h3 X Y hXY d hgap
  · rw [pairDeltaMass_neg_two_eq_directedFireMass
        c h3 X Y hXY,
      pairDeltaMass_two_eq_directedFireMass
        c h3 X Y hXY]
    exact reverse_directedFireMass_le_base_sq
      c h3 X Y hXY d (hgap Y (Ne.symm hXY))

end Tri.Multi

#print axioms Tri.Multi.pairDeltaMass_five_sum
#print axioms Tri.Multi.pairDeltaMass_two_eq_directedFireMass
#print axioms Tri.Multi.pairDeltaMass_neg_two_eq_directedFireMass
#print axioms Tri.Multi.pairDeltaMass_one_eq_thirdPartyUpMass_sum
#print axioms Tri.Multi.pairDeltaMass_neg_one_eq_thirdPartyDownMass_sum
#print axioms Tri.Multi.pairDeltaMass_five_mgf

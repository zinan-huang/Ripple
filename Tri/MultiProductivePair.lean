/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveEmbedded

/-!
# Pair-gap control in productive-event time

The proper-stage proof is indexed by productive reactions.  This file
transfers the physical fixed-pair geometric supermartingale to the exact
conditioned productive-event kernel, while keeping the full configuration as
the Markov state.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- A physical expectation is the nonproductive self-loop contribution plus
the positive-mass conditioned productive expectation. -/
theorem expect_multiStep_eq_nonproductive_add_productive
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (F : Config m n → ℝ≥0∞) :
    expect (multiStep c h3) F =
      nonproductiveMass c h3 * F c +
        productiveMass c h3 * expect (productiveStep h3 c) F := by
  classical
  have hPtop : productiveMass c h3 ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (productiveMass_le_one c h3)
  rw [productiveStep_of_mass_ne_zero h3 c hprod, expect_map,
    expect_productiveSamplePMF]
  unfold multiStep
  rw [expect_map]
  unfold expect nonproductiveMass
  simp only [tsum_fintype]
  rw [ENNReal.mul_div_cancel hprod hPtop]
  calc
    ∑ t : TripleSample c, triplePMF c h3 t * F (sampleNext c t) =
        ∑ t : TripleSample c,
          ((if IsProductiveSample t then 0 else triplePMF c h3 t) * F c +
            if IsProductiveSample t then
              triplePMF c h3 t * F (sampleNext c t) else 0) := by
      apply Finset.sum_congr rfl
      intro t _ht
      by_cases ht : IsProductiveSample t
      · simp [ht]
      · have hclass : classify t = none := by
          simpa [IsProductiveSample] using ht
        have hnext : sampleNext c t = c := by
          unfold sampleNext
          rw [hclass]
        simp [ht, hnext]
    _ =
        (∑ t : TripleSample c,
          if IsProductiveSample t then 0 else triplePMF c h3 t) * F c +
        ∑ t : TripleSample c,
          if IsProductiveSample t then
            triplePMF c h3 t * F (sampleNext c t) else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]

/-- Conditioning away inert self-loops preserves any physical
supermartingale inequality. -/
theorem productiveStep_conserve_of_multiStep_conserve
    (c : Config m n) (h3 : 3 ≤ n)
    (F : Config m n → ℝ≥0∞)
    (hFtop : F c ≠ ∞)
    (hraw : expect (multiStep c h3) F ≤ F c) :
    expect (productiveStep h3 c) F ≤ F c := by
  classical
  by_cases hprod : productiveMass c h3 = 0
  · unfold productiveStep
    simp [hprod]
  · have hPtop : productiveMass c h3 ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top
        (productiveMass_le_one c h3)
    have hdecomp :=
      expect_multiStep_eq_nonproductive_add_productive
        c h3 hprod F
    have hsum := productiveMass_add_nonproductiveMass c h3
    have hmul :
        productiveMass c h3 * expect (productiveStep h3 c) F ≤
          productiveMass c h3 * F c := by
      rw [hdecomp] at hraw
      have hraw' :
          nonproductiveMass c h3 * F c +
              productiveMass c h3 *
                expect (productiveStep h3 c) F ≤
            nonproductiveMass c h3 * F c +
              productiveMass c h3 * F c := by
        calc
          nonproductiveMass c h3 * F c +
                productiveMass c h3 *
                  expect (productiveStep h3 c) F ≤
              F c := hraw
          _ = (nonproductiveMass c h3 +
                productiveMass c h3) * F c := by
            rw [add_comm, hsum, one_mul]
          _ = nonproductiveMass c h3 * F c +
                productiveMass c h3 * F c := by
            rw [add_mul]
      have hQle : nonproductiveMass c h3 ≤ 1 := by
        rw [← hsum]
        exact le_add_left le_rfl
      have hQtop : nonproductiveMass c h3 ≠ ∞ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top hQle
      exact ENNReal.le_of_add_le_add_left
        (ENNReal.mul_ne_top hQtop hFtop) hraw'
    have hdiv :=
      ENNReal.div_le_div_right hmul (productiveMass c h3)
    have hcancel (a : ℝ≥0∞) :
        productiveMass c h3 * a / productiveMass c h3 = a := by
      rw [div_eq_mul_inv]
      calc
        productiveMass c h3 * a * (productiveMass c h3)⁻¹ =
            (productiveMass c h3 * (productiveMass c h3)⁻¹) * a := by
          ring
        _ = a := by
          rw [ENNReal.mul_inv_cancel hprod hPtop, one_mul]
    rw [hcancel, hcancel] at hdiv
    exact hdiv

/-- The fixed-pair geometric potential remains a supermartingale in exact
productive-event time. -/
theorem productiveStep_pairGapPotential_conserve
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hd2 : 2 ≤ d)
    (hgap : HasPairwiseGap c X d) :
    expect (productiveStep h3 c)
        (pairGapPotential (pairGapBase n d) X Y) ≤
      pairGapPotential (pairGapBase n d) X Y c :=
  productiveStep_conserve_of_multiStep_conserve c h3 _
    (ENNReal.pow_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        (pairGapBase_le_one n d (by omega)))) <|
      multiStep_pairGapPotential_conserve
        c h3 X Y hXY d hd2 hgap

/-- The productive-event chain frozen on first failure of the global
pairwise gap. -/
noncomputable def productivePairGapStop
    (h3 : 3 ≤ n) (X : Species m) (d : ℕ)
    (c : Config m n) : PMF (Config m n) := by
  classical
  exact if HasPairwiseGap c X d then productiveStep h3 c else PMF.pure c

/-- Every fixed-competitor potential is a supermartingale for the globally
stopped productive-event chain. -/
theorem productivePairGapStop_pair_conserve
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hd2 : 2 ≤ d)
    (c : Config m n) :
    expect (productivePairGapStop h3 X d c)
        (pairGapPotential (pairGapBase n d) X Y) ≤
      pairGapPotential (pairGapBase n d) X Y c := by
  classical
  unfold productivePairGapStop
  split_ifs with hgap
  · exact productiveStep_pairGapPotential_conserve
      c h3 X Y hXY d hd2 hgap
  · simp only [expect_pure]
    exact le_rfl

/-- One fixed competitor's finite productive-time backsliding mass. -/
theorem productivePairGapStop_pair_failure_le
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n) :
    (∑' c : Config m n,
      if pairGapNat c X Y < d then
        iter (productivePairGapStop h3 X d) T c0 c
      else 0) ≤
      pairGapBase n d ^ pairGapNat c0 X Y /
        pairGapBase n d ^ (d - 1) := by
  let u := pairGapBase n d
  let V : Config m n → ℝ≥0∞ := pairGapPotential u X Y
  let Bad : Config m n → Prop := fun c => pairGapNat c X Y < d
  have hu1 : u ≤ 1 :=
    pairGapBase_le_one n d (by omega)
  have hu0 : u ≠ 0 :=
    pairGapBase_ne_zero n d (by omega)
  have hutop : u ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  have htheta0 : u ^ (d - 1) ≠ 0 :=
    pow_ne_zero _ hu0
  have hthetaTop : u ^ (d - 1) ≠ ⊤ :=
    ENNReal.pow_ne_top hutop
  have hstep :
      ∀ c, expect (productivePairGapStop h3 X d c) V ≤ V c := by
    intro c
    exact productivePairGapStop_pair_conserve
      h3 X Y hXY d hd2 c
  have hbad :
      ∀ c, Bad c → u ^ (d - 1) ≤ V c := by
    intro c hc
    unfold Bad at hc
    unfold V pairGapPotential
    apply pow_le_pow_right_of_le_one' hu1
    omega
  simpa only [Bad, V, u, pairGapPotential] using
    stopped_bad_mass_le
      (productivePairGapStop h3 X d) V Bad
      (u ^ (d - 1)) htheta0 hthetaTop
      hstep hbad T c0

/-- Global finite-horizon no-backsliding in productive-event time. -/
theorem productivePairGapStop_global_failure_le
    (h3 : 3 ≤ n) (X : Species m)
    (d : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n) :
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        pairGapBase n d ^ pairGapNat c0 X Y /
          pairGapBase n d ^ (d - 1) := by
  calc
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        ∑' c : Config m n,
          if pairGapNat c X Y < d then
            iter (productivePairGapStop h3 X d) T c0 c
          else 0 :=
      globalPairGapFailureMass_le_pair_sum
        (iter (productivePairGapStop h3 X d) T c0) X d (by omega)
    _ ≤ ∑ Y ∈ Finset.univ.erase X,
        pairGapBase n d ^ pairGapNat c0 X Y /
          pairGapBase n d ^ (d - 1) := by
      apply Finset.sum_le_sum
      intro Y hY
      have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
      exact productivePairGapStop_pair_failure_le
        h3 X Y (Ne.symm hYX) d hd2 T c0

/-- A buffered initial gap gives one common productive-time failure power. -/
theorem productivePairGapStop_global_failure_le_of_buffer
    (h3 : 3 ≤ n) (X : Species m)
    (d b : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X (d + b)) :
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      (m : ℝ≥0∞) * pairGapBase n d ^ (b + 1) := by
  let u := pairGapBase n d
  have hu1 : u ≤ 1 :=
    pairGapBase_le_one n d (by omega)
  have hu0 : u ≠ 0 :=
    pairGapBase_ne_zero n d (by omega)
  have hutop : u ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  have htheta0 : u ^ (d - 1) ≠ 0 :=
    pow_ne_zero _ hu0
  have hthetaTop : u ^ (d - 1) ≠ ⊤ :=
    ENNReal.pow_ne_top hutop
  calc
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        u ^ pairGapNat c0 X Y / u ^ (d - 1) := by
      simpa only [u] using
        productivePairGapStop_global_failure_le h3 X d hd2 T c0
    _ ≤ ∑ Y ∈ Finset.univ.erase X, u ^ (b + 1) := by
      apply Finset.sum_le_sum
      intro Y hY
      have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
      have hgap := hinit Y hYX
      have hnat : d + b ≤ pairGapNat c0 X Y := by
        unfold pairGapNat
        omega
      have hpow :
          u ^ pairGapNat c0 X Y ≤ u ^ (d + b) :=
        pow_le_pow_right_of_le_one' hu1 hnat
      calc
        u ^ pairGapNat c0 X Y / u ^ (d - 1) ≤
            u ^ (d + b) / u ^ (d - 1) :=
          ENNReal.div_le_div_right hpow _
        _ = u ^ (b + 1) := by
          rw [show d + b = (d - 1) + (b + 1) by omega,
            pow_add, mul_comm, mul_div_assoc,
            ENNReal.div_self htheta0 hthetaTop, mul_one]
    _ = ((Finset.univ.erase X).card : ℝ≥0∞) * u ^ (b + 1) := by
      simp
    _ ≤ (m : ℝ≥0∞) * u ^ (b + 1) := by
      gcongr
      simp

/-- Gaussian-envelope form of productive-time global no-backsliding. -/
theorem productivePairGapStop_global_failure_exp
    (h3 : 3 ≤ n) (X : Species m)
    (d b : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X (d + b)) :
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(((b + 1 : ℕ) : ℝ) * (d : ℝ) ^ 2 /
            (4 * (n : ℝ) ^ 2 + (d : ℝ) ^ 2)))) := by
  calc
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      (m : ℝ≥0∞) * pairGapBase n d ^ (b + 1) :=
        productivePairGapStop_global_failure_le_of_buffer
          h3 X d b hd2 T c0 hinit
    _ ≤ (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(((b + 1 : ℕ) : ℝ) * (d : ℝ) ^ 2 /
            (4 * (n : ℝ) ^ 2 + (d : ℝ) ^ 2)))) :=
      mul_le_mul_right
        (pairGapBase_pow_le_exp n d (b + 1) (by omega)) _

end Tri.Multi

#print axioms Tri.Multi.expect_multiStep_eq_nonproductive_add_productive
#print axioms Tri.Multi.productiveStep_conserve_of_multiStep_conserve
#print axioms Tri.Multi.productiveStep_pairGapPotential_conserve
#print axioms Tri.Multi.productivePairGapStop_pair_conserve
#print axioms Tri.Multi.productivePairGapStop_pair_failure_le
#print axioms Tri.Multi.productivePairGapStop_global_failure_le
#print axioms Tri.Multi.productivePairGapStop_global_failure_le_of_buffer
#print axioms Tri.Multi.productivePairGapStop_global_failure_exp

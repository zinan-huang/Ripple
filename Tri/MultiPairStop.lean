/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiPairSuper
import Tri.RatioExp

/-!
# Globally stopped fixed-pair no-backsliding

The kernel is frozen as soon as the designated species no longer leads every
competitor by `d`.  Before that exit, each fixed-pair geometric potential is
conserved by the physical multi-species kernel.  This gives a finite-horizon
bound for every possible offending competitor without projecting the full
configuration to a Markov gap chain.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Physical multi-species step frozen after the global pairwise gap `d`
fails. -/
noncomputable def multiPairGapStop
    (h3 : 3 ≤ n) (X : Species m) (d : ℕ)
    (c : Config m n) : PMF (Config m n) := by
  classical
  exact if HasPairwiseGap c X d then multiStep c h3 else PMF.pure c

/-- Every fixed-competitor potential is a supermartingale for the globally
stopped physical kernel. -/
theorem multiPairGapStop_pair_conserve
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hd2 : 2 ≤ d)
    (c : Config m n) :
    expect (multiPairGapStop h3 X d c)
        (pairGapPotential (pairGapBase n d) X Y) ≤
      pairGapPotential (pairGapBase n d) X Y c := by
  classical
  unfold multiPairGapStop
  split_ifs with hgap
  · exact multiStep_pairGapPotential_conserve
      c h3 X Y hXY d hd2 hgap
  · simp only [expect_pure]
    exact le_rfl

/-- Finite-horizon probability that one fixed competitor is within distance
`d` in the globally stopped chain. -/
theorem multiPairGapStop_pair_failure_le
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n) :
    (∑' c : Config m n,
      if pairGapNat c X Y < d then
        iter (multiPairGapStop h3 X d) T c0 c
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
  have hutop : u ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  have htheta0 : u ^ (d - 1) ≠ 0 :=
    pow_ne_zero _ hu0
  have hthetaTop : u ^ (d - 1) ≠ ⊤ :=
    ENNReal.pow_ne_top hutop
  have hstep :
      ∀ c, expect (multiPairGapStop h3 X d c) V ≤ V c := by
    intro c
    exact multiPairGapStop_pair_conserve
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
      (multiPairGapStop h3 X d) V Bad
      (u ^ (d - 1)) htheta0 hthetaTop
      hstep hbad T c0

/-- Terminal mass outside the global pairwise-gap region. -/
noncomputable def globalPairGapFailureMass
    (p : PMF (Config m n)) (X : Species m) (d : ℕ) : ℝ≥0∞ := by
  classical
  exact ∑' c : Config m n,
    if ¬ HasPairwiseGap c X d then p c else 0

/-- A global pairwise-gap violation is witnessed by one competitor, so its
mass is bounded by the finite sum of the fixed-competitor bad masses. -/
theorem globalPairGapFailureMass_le_pair_sum
    (p : PMF (Config m n)) (X : Species m) (d : ℕ)
    (hd : 0 < d) :
    globalPairGapFailureMass p X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        ∑' c : Config m n,
          if pairGapNat c X Y < d then p c else 0 := by
  classical
  unfold globalPairGapFailureMass
  simp only [tsum_fintype]
  calc
    ∑ c : Config m n,
        (if ¬ HasPairwiseGap c X d then p c else 0) ≤
      ∑ c : Config m n,
        ∑ Y ∈ Finset.univ.erase X,
          (if pairGapNat c X Y < d then p c else 0) := by
      apply Finset.sum_le_sum
      intro c _hc
      by_cases hgap : HasPairwiseGap c X d
      · simp [hgap]
      · have hwitness :
            ∃ Y, Y ≠ X ∧ count c X < count c Y + d := by
          unfold HasPairwiseGap at hgap
          push Not at hgap
          exact hgap
        obtain ⟨Y, hYX, hbad⟩ := hwitness
        have hmem : Y ∈ (Finset.univ.erase X : Finset (Species m)) := by
          simp [hYX]
        have hnatBad : pairGapNat c X Y < d := by
          unfold pairGapNat
          omega
        rw [if_pos hgap]
        have hsingle :
            (if pairGapNat c X Y < d then p c else 0) ≤
              ∑ Z ∈ Finset.univ.erase X,
                (if pairGapNat c X Z < d then p c else 0) :=
          Finset.single_le_sum
            (f := fun Z =>
              if pairGapNat c X Z < d then p c else 0)
            (fun Z _hZ => by exact bot_le) hmem
        simpa [hnatBad] using hsingle
    _ = ∑ Y ∈ Finset.univ.erase X,
          ∑ c : Config m n,
            (if pairGapNat c X Y < d then p c else 0) := by
      rw [Finset.sum_comm]

/-- Finite-horizon global no-backsliding bound for the physical
multi-species chain frozen on first pairwise-gap failure. -/
theorem multiPairGapStop_global_failure_le
    (h3 : 3 ≤ n) (X : Species m)
    (d : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n) :
    globalPairGapFailureMass
        (iter (multiPairGapStop h3 X d) T c0) X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        pairGapBase n d ^ pairGapNat c0 X Y /
          pairGapBase n d ^ (d - 1) := by
  calc
    globalPairGapFailureMass
        (iter (multiPairGapStop h3 X d) T c0) X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        ∑' c : Config m n,
          if pairGapNat c X Y < d then
            iter (multiPairGapStop h3 X d) T c0 c
          else 0 :=
      globalPairGapFailureMass_le_pair_sum
        (iter (multiPairGapStop h3 X d) T c0) X d (by omega)
    _ ≤ ∑ Y ∈ Finset.univ.erase X,
        pairGapBase n d ^ pairGapNat c0 X Y /
          pairGapBase n d ^ (d - 1) := by
      apply Finset.sum_le_sum
      intro Y hY
      have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
      exact multiPairGapStop_pair_failure_le
        h3 X Y (Ne.symm hYX) d hd2 T c0

/-- If the initial global gap has an additional buffer `b`, every competitor's
ratio bound simplifies to one common power, and the finite union costs at most
the number of species. -/
theorem multiPairGapStop_global_failure_le_of_buffer
    (h3 : 3 ≤ n) (X : Species m)
    (d b : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X (d + b)) :
    globalPairGapFailureMass
        (iter (multiPairGapStop h3 X d) T c0) X d ≤
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
        (iter (multiPairGapStop h3 X d) T c0) X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        u ^ pairGapNat c0 X Y / u ^ (d - 1) := by
      simpa only [u] using
        multiPairGapStop_global_failure_le h3 X d hd2 T c0
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

/-- The common pair-gap base has the exact Gaussian exponential envelope
coming from its denominator slack `d²`. -/
theorem pairGapBase_pow_le_exp
    (n d k : ℕ) (hn : 0 < n) :
    pairGapBase n d ^ k ≤
      ENNReal.ofReal
        (Real.exp (-((k : ℝ) * (d : ℝ) ^ 2 /
          (4 * (n : ℝ) ^ 2 + (d : ℝ) ^ 2)))) := by
  unfold pairGapBase
  apply ratio_pow_le_ofReal_exp
  · positivity
  · omega
  · push_cast
    ring_nf
    exact le_rfl

/-- Exponential form of the buffered global no-backsliding estimate. -/
theorem multiPairGapStop_global_failure_exp
    (h3 : 3 ≤ n) (X : Species m)
    (d b : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X (d + b)) :
    globalPairGapFailureMass
        (iter (multiPairGapStop h3 X d) T c0) X d ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(((b + 1 : ℕ) : ℝ) * (d : ℝ) ^ 2 /
            (4 * (n : ℝ) ^ 2 + (d : ℝ) ^ 2)))) := by
  calc
    globalPairGapFailureMass
        (iter (multiPairGapStop h3 X d) T c0) X d ≤
      (m : ℝ≥0∞) * pairGapBase n d ^ (b + 1) :=
        multiPairGapStop_global_failure_le_of_buffer
          h3 X d b hd2 T c0 hinit
    _ ≤ (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(((b + 1 : ℕ) : ℝ) * (d : ℝ) ^ 2 /
            (4 * (n : ℝ) ^ 2 + (d : ℝ) ^ 2)))) :=
      mul_le_mul_right
        (pairGapBase_pow_le_exp n d (b + 1) (by omega)) _

end Tri.Multi

#print axioms Tri.Multi.multiPairGapStop_pair_conserve
#print axioms Tri.Multi.multiPairGapStop_pair_failure_le
#print axioms Tri.Multi.globalPairGapFailureMass_le_pair_sum
#print axioms Tri.Multi.multiPairGapStop_global_failure_le
#print axioms Tri.Multi.multiPairGapStop_global_failure_le_of_buffer
#print axioms Tri.Multi.pairGapBase_pow_le_exp
#print axioms Tri.Multi.multiPairGapStop_global_failure_exp

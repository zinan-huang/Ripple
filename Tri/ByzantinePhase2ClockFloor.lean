/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase1Productive
import Tri.ByzantinePhase2Ladder

/-!
# Byzantine Phase-II dyadic productive-clock floor

This file contains only the stop predicate, the dyadic Bernoulli floor and its
complement identity, and the statewise productive-mass lower bound.  The raw
rung and ladder horizons belong in a later file.
-/

namespace Tri.Byzantine

open scoped ENNReal NNReal

noncomputable section

variable {n B z : ℕ}

/-- The raw/productive clock is live until either the lower Phase-II boundary
or the current rung target is reached. -/
def Phase2DyadicClockStop
    (j : ℕ) (q : Phase2Level n B z) : Prop :=
  Phase2EntryFailure q ∨
    Phase2RungTarget (phase2DyadicK j) q

instance phase2DyadicClockStopDecidable (j : ℕ) :
    DecidablePred
      (Phase2DyadicClockStop (n := n) (B := B) (z := z) j) := by
  intro q
  unfold Phase2DyadicClockStop
  infer_instance

/-- At dyadic denominator `K_j`, the live productive probability is at least
`1 / (2 K_j)`.  Keeping the product inside one denominator avoids all
inverse-of-product rewriting in `ENNReal`. -/
noncomputable def phase2DyadicClockFloor (j : ℕ) : NNReal :=
  (1 : NNReal) /
    ((2 * phase2DyadicK j : ℕ) : NNReal)

/-- The `ENNReal` form consumed by the productive-clock comparison. -/
theorem phase2DyadicClockFloor_eq (j : ℕ) :
    (phase2DyadicClockFloor j : ℝ≥0∞) =
      (1 : ℝ≥0∞) /
        ((2 * phase2DyadicK j : ℕ) : ℝ≥0∞) := by
  have hK : phase2DyadicK j ≠ 0 := by
    simp [phase2DyadicK]
  have hdenNat : 2 * phase2DyadicK j ≠ 0 :=
    Nat.mul_ne_zero (by norm_num) hK
  have hdenNN :
      (((2 * phase2DyadicK j : ℕ) : NNReal)) ≠ 0 := by
    exact_mod_cast hdenNat
  rw [phase2DyadicClockFloor, ENNReal.coe_div hdenNN]
  norm_num

/-- The floor and its `ENNReal` complement sum exactly to one. -/
theorem phase2DyadicClockComplement (j : ℕ) :
    (phase2DyadicClockFloor j : ℝ≥0∞) +
        (1 - (phase2DyadicClockFloor j : ℝ≥0∞)) = 1 := by
  have hKpos : 0 < phase2DyadicK j := by
    simp [phase2DyadicK]
  have hdenNat : 1 ≤ 2 * phase2DyadicK j := by
    omega
  have hdenE :
      (1 : ℝ≥0∞) ≤
        ((2 * phase2DyadicK j : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hdenNat
  have hpLe :
      (phase2DyadicClockFloor j : ℝ≥0∞) ≤ 1 := by
    rw [phase2DyadicClockFloor_eq]
    exact ENNReal.div_le_of_le_mul (by simpa using hdenE)
  rw [add_comm]
  exact tsub_add_cancel_of_le hpLe

/-- Canonical relaxed rate induced by the current physical `Y/Z` split.
The zero-minority branch is assigned the harmless rate `(1,0)`. -/
noncomputable def phase2PaperEffectiveRate
    (q : Phase2Level n B z) : RelaxedRate := by
  by_cases hm : State.y q.1 + State.z q.1 = 0
  · exact
      { fire := 1
        idle := 0
        add_eq_one := by norm_num }
  · let m : NNReal :=
      ((State.y q.1 + State.z q.1 : ℕ) : NNReal)
    have hmNN : m ≠ 0 := by
      dsimp only [m]
      exact_mod_cast hm
    exact
      { fire := (State.y q.1 : NNReal) / m
        idle := (State.z q.1 : NNReal) / m
        add_eq_one := by
          rw [← add_div]
          have hsum :
              (State.y q.1 : NNReal) +
                  (State.z q.1 : NNReal) = m := by
            dsimp only [m]
            exact_mod_cast
              (show
                State.y q.1 + State.z q.1 =
                  State.y q.1 + State.z q.1 by rfl)
          rw [hsum, div_self hmNN] }

/-- The canonical rate satisfies the division-free physical specification. -/
theorem phase2PaperEffectiveRate_spec
    (q : Phase2Level n B z) :
    IsPaperEffectiveRate (phase2PaperEffectiveRate q) q.1 := by
  by_cases hm : State.y q.1 + State.z q.1 = 0
  · apply isPaperEffectiveRate_of_yz_eq_zero
    exact hm
  · have hmNat :
        (State.y q.1 + State.z q.1 : ℕ) ≠ 0 :=
      hm
    have hmE :
        ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hmNat
    have hmTop :
        ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    have hmE' :
        (State.y q.1 : ℝ≥0∞) +
            (State.z q.1 : ℝ≥0∞) ≠ 0 := by
      simpa using hmE
    have hmTop' :
        (State.y q.1 : ℝ≥0∞) +
            (State.z q.1 : ℝ≥0∞) ≠ ⊤ := by
      simpa using hmTop
    simp only [phase2PaperEffectiveRate, hm, ↓reduceDIte]
    constructor
    · change
        (((State.y q.1 : NNReal) /
            ((State.y q.1 + State.z q.1 : ℕ) : NNReal) :
              NNReal) : ℝ≥0∞) *
            ((State.y q.1 : ℝ≥0∞) +
              (State.z q.1 : ℝ≥0∞)) =
          (State.y q.1 : ℝ≥0∞)
      rw [ENNReal.coe_div]
      · push_cast
        exact ENNReal.div_mul_cancel hmE' hmTop'
      · exact_mod_cast hmNat
    · change
        (((State.z q.1 : NNReal) /
            ((State.y q.1 + State.z q.1 : ℕ) : NNReal) :
              NNReal) : ℝ≥0∞) *
            ((State.y q.1 : ℝ≥0∞) +
              (State.z q.1 : ℝ≥0∞)) =
          (State.z q.1 : ℝ≥0∞)
      rw [ENNReal.coe_div]
      · push_cast
        exact ENNReal.div_mul_cancel hmE' hmTop'
      · exact_mod_cast hmNat

/-- The dyadic clock stop is the next cumulative ladder target together with
the common lower exit. -/
theorem phase2DyadicClockStop_iff
    (j : ℕ) (q : Phase2Level n B z) :
    Phase2DyadicClockStop
        (n := n) (B := B) (z := z) j q ↔
      Phase2EntryFailure q ∨
        Phase2LadderTarget
          (n := n) (B := B) (z := z) (j + 1) q := by
  unfold Phase2DyadicClockStop Phase2RungTarget
    Phase2LadderTarget
  rw [phase2DyadicCheckpoint_succ_eq]

/-- On every live state of dyadic rung `j`, the paper-worst fixed-fibre chain
has productive mass at least `1 / (2 K_j)`.

The proof uses only:

* the live lower boundary `3n ≤ 4x`;
* failure of strong entry, hence `z < y` and `fire ≥ 1/2`;
* failure of the next cap, hence `n < 2K_j (y+z)`;
* the exact relaxed productive bridge already proved for Phase I.
-/
theorem phase2DyadicProductiveMass_ge
    (h3 : 3 ≤ n) (j : ℕ) (q : Phase2Level n B z)
    (rEff : RelaxedRate)
    (hrate : IsPaperEffectiveRate rEff q.1)
    (hlive :
      ¬ Phase2DyadicClockStop
        (n := n) (B := B) (z := z) j q) :
    (phase2DyadicClockFloor j : ℝ≥0∞) ≤
      phase1ProductiveMass h3 q := by
  have hentry : ¬ Phase2EntryFailure q := by
    intro h
    exact hlive (Or.inl h)
  have hrung :
      ¬ Phase2RungTarget (phase2DyadicK j) q := by
    intro h
    exact hlive (Or.inr h)
  have hstrong : ¬ Phase2StrongTarget q := by
    intro h
    exact hrung (Or.inl h)
  have hcap :
      ¬ Phase2AggregateCap
        (n := n) (B := B) (z := z)
        (2 * phase2DyadicK j) q := by
    intro h
    exact hrung (Or.inr h)

  unfold Phase2EntryFailure at hentry
  have hxBand :
      3 * n ≤ 4 * State.x q.1 :=
    Nat.le_of_not_gt hentry

  have hnotYZ :
      ¬ State.y q.1 ≤ State.z q.1 := by
    intro h
    exact hstrong ((phase2StrongTarget_iff_y_le_z q).2 h)
  have hyz : State.z q.1 < State.y q.1 :=
    Nat.lt_of_not_ge hnotYZ
  have hmPos :
      0 < State.y q.1 + State.z q.1 := by
    omega
  have hxPos : 0 < State.x q.1 := by
    omega

  unfold Phase2AggregateCap at hcap
  have hnext :
      n <
        (2 * phase2DyadicK j) *
          (State.y q.1 + State.z q.1) :=
    Nat.lt_of_not_ge hcap

  /- The exact effective-rate identity and `z < y` give `fire ≥ 1/2`. -/
  have hminorPair :
      State.y q.1 + State.z q.1 ≤
        2 * State.y q.1 := by
    omega
  have hhalfShare :
      ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) / 2 ≤
        (State.y q.1 : ℝ≥0∞) := by
    -- the repo's idiom is `div_le_iff_le_mul` with `Or.inl` side conditions
    -- (see Tri/Phase3Productive.lean); `div_le_iff` has a different shape here.
    apply
      (ENNReal.div_le_iff_le_mul
        (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
        (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).2
    exact_mod_cast (by
      simpa [mul_comm] using hminorPair)
  have hhalfMul :
      ((1 : ℝ≥0∞) / 2) *
          ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) ≤
        (State.y q.1 : ℝ≥0∞) := by
    calc
      ((1 : ℝ≥0∞) / 2) *
            ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) =
          ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) / 2 := by
            simp only [div_eq_mul_inv]
            ac_rfl
      _ ≤ (State.y q.1 : ℝ≥0∞) := hhalfShare
  have hmNe :
      ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hmPos.ne'
  have hmTop :
      ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hfireHalf :
      ((1 : ℝ≥0∞) / 2) ≤ (rEff.fire : ℝ≥0∞) := by
    apply (ENNReal.mul_le_mul_iff_right hmNe hmTop).mp
    -- goal is `m * (1/2) ≤ m * fire`; only the right factors differ.
    gcongr
    -- reduces to `1/2 ≤ fire`; cancel `m` from `hhalfMul` on the right.
    refine (ENNReal.mul_le_mul_iff_right hmNe hmTop).mp ?_
    calc ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2)
        ≤ (State.y q.1 : ℝ≥0∞) := by
            rw [mul_comm]; exact hhalfMul
      _ = ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) *
            (rEff.fire : ℝ≥0∞) := by
            rw [mul_comm]
            -- fire_cross is stated with the cast distributed over the sum
            have h := hrate.fire_cross.symm
            push_cast
            push_cast at h
            exact h

  have hnPos : 0 < n := by
    omega
  have hKpos : 0 < phase2DyadicK j := by
    simp [phase2DyadicK]
  have hDpos : 0 < 2 * phase2DyadicK j :=
    Nat.mul_pos (by norm_num) hKpos
  have hnNe : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hnPos.ne'
  have hnTop : (n : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hDNe :
      ((2 * phase2DyadicK j : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hDpos.ne'
  have hDTop :
      ((2 * phase2DyadicK j : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hfloorShare :
      (phase2DyadicClockFloor j : ℝ≥0∞) ≤
        ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) /
          (n : ℝ≥0∞) := by
    rw [phase2DyadicClockFloor_eq]
    apply
      (ENNReal.le_div_iff_mul_le
        (Or.inl hnNe) (Or.inl hnTop)).2
    calc
      (1 : ℝ≥0∞) /
            ((2 * phase2DyadicK j : ℕ) : ℝ≥0∞) *
          (n : ℝ≥0∞) =
          (n : ℝ≥0∞) /
            ((2 * phase2DyadicK j : ℕ) : ℝ≥0∞) := by
            simp only [div_eq_mul_inv, one_mul]
            ac_rfl
      _ ≤ ((State.y q.1 + State.z q.1 : ℕ) : ℝ≥0∞) := by
        apply
          (ENNReal.div_le_iff hDNe hDTop).2
        exact_mod_cast (by
          simpa [mul_comm] using hnext.le)

  /- Move to the successor-indexed ordinary/relaxed productive formulas. -/
  obtain ⟨xPred, hxPred⟩ :=
    Nat.exists_eq_succ_of_ne_zero hxPos.ne'
  obtain ⟨mPred, hmPred⟩ :=
    Nat.exists_eq_succ_of_ne_zero hmPos.ne'
  simp only [Nat.succ_eq_add_one] at hxPred hmPred

  have hpop : xPred + mPred + 2 = n := by
    have htotal := State.total q.1
    omega
  have hxBand' :
      3 * n ≤ 4 * (xPred + 1) := by
    simpa only [hxPred] using hxBand
  have hcoef :
      2 * (xPred + mPred + 1) ≤
        3 * (xPred + 1) := by
    omega
  have hcross :
      (2 * (mPred + 1)) *
          (n * (xPred + mPred + 1)) ≤
        (3 * ((xPred + 1) * (mPred + 1))) * n := by
    have hmul :=
      Nat.mul_le_mul_left (n * (mPred + 1)) hcoef
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

  have hdenPos :
      0 < n * (xPred + mPred + 1) := by
    apply Nat.mul_pos hnPos
    omega
  have hdenNe :
      ((n * (xPred + mPred + 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hdenPos.ne'
  have hdenTop :
      ((n * (xPred + mPred + 1) : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _

  have hleft :
      (2 : ℝ≥0∞) *
          (((mPred + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) =
        ((2 * (mPred + 1) : ℕ) : ℝ≥0∞) /
          (n : ℝ≥0∞) := by
    simp only [div_eq_mul_inv]
    push_cast
    ring

  have hordinary :
      (2 : ℝ≥0∞) *
          (((mPred + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) ≤
        triStep (xPred + 1) (mPred + 1) (by omega) xPred +
          triStep (xPred + 1) (mPred + 1) (by omega)
            (xPred + 2) := by
    rw [hleft, productive_mass_closed xPred mPred n h3 hpop]
    apply
      (ENNReal.div_le_iff hnNe hnTop).2
    have hrhs :
        (((3 * ((xPred + 1) * (mPred + 1)) : ℕ) : ℝ≥0∞) /
              ((n * (xPred + mPred + 1) : ℕ) : ℝ≥0∞)) *
            (n : ℝ≥0∞) =
          ((((3 * ((xPred + 1) * (mPred + 1)) : ℕ) : ℝ≥0∞) *
              (n : ℝ≥0∞)) /
            ((n * (xPred + mPred + 1) : ℕ) : ℝ≥0∞)) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    rw [hrhs]
    apply
      (ENNReal.le_div_iff_mul_le
        (Or.inl hdenNe) (Or.inl hdenTop)).2
    exact_mod_cast hcross

  have hrelaxed :=
    relaxed_productive_mass_ge_fire_mul
      rEff xPred mPred (by omega)
  have hfloorShare' :
      (phase2DyadicClockFloor j : ℝ≥0∞) ≤
        ((mPred + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞) := by
    simpa only [hmPred] using hfloorShare
  have hhalfTwo :
      ((1 : ℝ≥0∞) / 2) * 2 = 1 := by
    calc
      ((1 : ℝ≥0∞) / 2) * 2 =
          2 * ((1 : ℝ≥0∞) / 2) := by ring
      _ = 1 := by
        rw [one_div,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

  calc
    (phase2DyadicClockFloor j : ℝ≥0∞) ≤
        ((mPred + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞) :=
      hfloorShare'
    _ = ((1 : ℝ≥0∞) / 2) *
          ((2 : ℝ≥0∞) *
            (((mPred + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞))) := by
      symm
      calc
        ((1 : ℝ≥0∞) / 2) *
              ((2 : ℝ≥0∞) *
                (((mPred + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞))) =
            (((1 : ℝ≥0∞) / 2) * 2) *
              (((mPred + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) := by
                ring
        _ = ((mPred + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞) := by
          rw [hhalfTwo, one_mul]
    _ ≤ (rEff.fire : ℝ≥0∞) *
          (triStep (xPred + 1) (mPred + 1) (by omega) xPred +
            triStep (xPred + 1) (mPred + 1) (by omega)
              (xPred + 2)) :=
      mul_le_mul hfireHalf hordinary bot_le bot_le
    _ ≤ relaxedTriStep rEff
          (xPred + 1) (mPred + 1) (by omega) xPred +
        relaxedTriStep rEff
          (xPred + 1) (mPred + 1) (by omega) (xPred + 2) :=
      hrelaxed
    _ = phase1ProductiveMass h3 q :=
      (phase1ProductiveMass_eq_relaxed
        h3 q rEff hxPred hmPred hrate).symm

/-- Parameter-free form using the canonical physical effective rate. -/
theorem phase2DyadicProductiveMass_ge_canonical
    (h3 : 3 ≤ n) (j : ℕ) (q : Phase2Level n B z)
    (hlive :
      ¬ Phase2DyadicClockStop
        (n := n) (B := B) (z := z) j q) :
    (phase2DyadicClockFloor j : ℝ≥0∞) ≤
      phase1ProductiveMass h3 q :=
  phase2DyadicProductiveMass_ge
    h3 j q (phase2PaperEffectiveRate q)
      (phase2PaperEffectiveRate_spec q) hlive

end

end Tri.Byzantine

#print axioms Tri.Byzantine.phase2PaperEffectiveRate_spec
#print axioms Tri.Byzantine.phase2DyadicClockStop_iff
#print axioms Tri.Byzantine.phase2DyadicProductiveMass_ge
#print axioms Tri.Byzantine.phase2DyadicProductiveMass_ge_canonical

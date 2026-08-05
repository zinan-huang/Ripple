/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBHighCapBridge
import Tri.SingleBCoReturn
import Tri.RatioExp

/-!
# Single-B final consensus interface

The late ladder reaches the additive co-level checkpoint
`SingleLateCheckpoint n (singleLateTargetCap n gamma)`.  The remaining live
route must work on the co-level `2y+b`: co-level zero is exactly all-`X`
consensus, and all-`X` is absorbing for the Single-B kernel.

The corrected-level export through a target above `2n` stays intentionally
dead.  The last lemma records the arithmetic obstruction to reusing the
level-form structural rung with `Lexit = 2*n`: its high-boundary and co-clock
side conditions force every positive budget to be zero.
-/

namespace Tri

open scoped ENNReal

/-- Logarithmic co-level scale of the final Single-B block. -/
def singleFinalScale (n gamma : Nat) : Nat :=
  gamma * Nat.log 2 n + 1

/-- Resolution-scale used by the physical final co-level block. -/
def singleFinalResolutions (n gamma : Nat) : Nat :=
  64 * singleFinalScale n gamma

/-- Raw horizon used by the physical final co-level block. -/
def singleFinalHorizon (n gamma : Nat) : Nat :=
  65536 * n * singleFinalScale n gamma

/-! ## Physical final potential -/

/-- The final physical safety boundary: either the co-level has made a large
upward excursion, or the `X` majority guard needed for the one-step contraction
has failed. -/
def SingleFinalBad (B : Nat) {n : Nat} (s : SingleState n) : Prop :=
  B <= s.1.doubleCoLevel ∨ s.1.x < 4 * s.1.y

instance (B n : Nat) : DecidablePred (SingleFinalBad B (n := n)) := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- Terminal live states for the final stopped physical chain. -/
def SingleFinalLive (B : Nat) {n : Nat} (s : SingleState n) : Prop :=
  ¬ SingleFinalBad B s ∧ ¬ BiXConsensus n s.1

instance (B n : Nat) : DecidablePred (SingleFinalLive B (n := n)) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- `Y`-base for the final physical potential.  It is exactly
`(3/2)^3`, so the safety comparison below uses integer exponents in one
common blank base. -/
noncomputable def singleFinalYBase : ENNReal :=
  ENNReal.ofReal ((27 : Real) / 8)

noncomputable def singleFinalYBaseReal : Real := (27 : Real) / 8

/-- Blank-base for the final physical potential. -/
noncomputable def singleFinalBlankBase : ENNReal :=
  ENNReal.ofReal ((3 : Real) / 2)

noncomputable def singleFinalBlankBaseReal : Real := (3 : Real) / 2

/-- Physical potential for the Single-B final block.

`(27/8)^y (3/2)^b` is chosen so that `(27/8) = (3/2)^3`.
The fair creation pair has strict average contraction, and the blank-resolution
drift is nonpositive throughout the safe region `x >= 4y`. -/
noncomputable def singleFinalV {n : Nat} (s : SingleState n) : ENNReal :=
  singleFinalYBase ^ s.1.y * (singleFinalBlankBase ^ s.1.b)

/-- Real shadow of `singleFinalV`, used only to discharge finite one-step
arithmetic. -/
noncomputable def singleFinalVReal {n : Nat} (s : SingleState n) : Real :=
  singleFinalYBaseReal ^ s.1.y * (singleFinalBlankBaseReal ^ s.1.b)

/-- Real multiplier of `singleFinalV` for each positive-weight Single-B
event. -/
noncomputable def singleFinalFactorReal : SingleComp -> Real
  | .xx => 1
  | .xyToX => (4 : Real) / 9
  | .xyToY => (3 : Real) / 2
  | .yy => 1
  | .xb => (2 : Real) / 3
  | .yb => (9 : Real) / 4
  | .bb => 1

/-- The `ℝ≥0∞` potential is finite and has the expected real value. -/
theorem singleFinalV_toReal {n : Nat} (s : SingleState n) :
    (singleFinalV s).toReal = singleFinalVReal s := by
  unfold singleFinalV singleFinalVReal
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow]
  unfold singleFinalYBase singleFinalBlankBase singleFinalYBaseReal
    singleFinalBlankBaseReal
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : Real) <= 27 / 8),
    ENNReal.toReal_ofReal (by norm_num : (0 : Real) <= 3 / 2)]

/-- The final potential never takes value `∞`. -/
theorem singleFinalV_ne_top {n : Nat} (s : SingleState n) :
    singleFinalV s ≠ ⊤ := by
  unfold singleFinalV
  apply ENNReal.mul_ne_top
  · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

/-- Every Single-B event probability is finite. -/
theorem singleCompPMF_ne_top {x y b : Nat}
    {h : 2 <= x + y + b} (k : SingleComp) :
    singleCompPMF x y b h k ≠ ⊤ := by
  rw [singleCompPMF_apply]
  apply ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
  have hpos : 0 < 2 * Nat.choose (x + y + b) 2 :=
    Nat.mul_pos (by norm_num) (Nat.choose_pos h)
  exact_mod_cast hpos.ne'

/-- Real value of a Single-B event probability. -/
theorem singleCompPMF_toReal {x y b : Nat}
    {h : 2 <= x + y + b} (k : SingleComp) :
    (singleCompPMF x y b h k).toReal =
      ((SingleComp.weight x y b k : Nat) : Real) /
        ((2 * Nat.choose (x + y + b) 2 : Nat) : Real) := by
  rw [singleCompPMF_apply, ENNReal.toReal_div]
  norm_num [ENNReal.toReal_natCast]

/-- The final potential masked off at bad states and at all-`X` consensus. -/
noncomputable def singleFinalMaskedV (B : Nat) {n : Nat}
    (s : SingleState n) : ENNReal :=
  if SingleFinalBad B s ∨ BiXConsensus n s.1 then 0 else singleFinalV s

/-- The Single-B state step's expectation, pushed onto the seven-event
alphabet. -/
theorem expect_singleStateStep (n : Nat) (hn : 2 <= n) (s : SingleState n)
    (W : SingleState n -> ENNReal) :
    expect (singleStateStep n hn s) W
      = ∑ k : SingleComp,
          singleCompPMF s.1.x s.1.y s.1.b (by
            have h := s.2
            simp only [BiCfg.DoubleInv] at h
            omega) k
            * W (SingleComp.nextSingleState s k) := by
  unfold singleStateStep
  rw [expect_map, expect_fintype]

/-- Scalar contraction behind the final physical potential.  In the safe
region `x >= 4y`, `2y+b < n/2`, and `2y+b > 0`, the relative one-step deficit
of `(27/8)^y(3/2)^b` is at least `1/(64n)`. -/
theorem singleFinal_scalar_gap
    (n x y b : Nat) (hn : 2 <= n) (hsum : x + y + b = n)
    (hmaj : 4 * y <= x) (hco : 2 * y + b < 2 * n / 3)
    (hpos : 0 < 2 * y + b) :
    let D : Real := (n : Real) * ((n - 1 : Nat) : Real)
    let deficit : Real := (1 : Real) / 18 * (x : Real) * (y : Real) +
      (1 : Real) / 6 * (b : Real) *
        (4 * (x : Real) - 15 * (y : Real))
    (1 : Real) / (64 * (n : Real)) <= deficit / D := by
  intro D deficit
  have hnposN : 0 < n := by omega
  have hnR : (0 : Real) < n := by exact_mod_cast hnposN
  have hn1R : (0 : Real) < ((n - 1 : Nat) : Real) := by
    exact_mod_cast (by omega : 0 < n - 1)
  have hDpos : 0 < D := by
    dsimp only [D]
    positivity
  have hxthirdN : n <= 3 * x := by omega
  have hxthird : (n : Real) <= 3 * (x : Real) := by exact_mod_cast hxthirdN
  have hmajR : (4 : Real) * y <= x := by exact_mod_cast hmaj
  have hxNonneg : (0 : Real) <= x := by positivity
  have hdefLower : (x : Real) / 18 <= deficit := by
    dsimp only [deficit]
    by_cases hy0 : y = 0
    · subst y
      have hbpos : 1 <= b := by omega
      have hbR : (1 : Real) <= b := by exact_mod_cast hbpos
      nlinarith [mul_nonneg (by norm_num : (0 : Real) <= 1 / 6)
        (mul_nonneg (by positivity : (0 : Real) <= (b : Real))
          (by nlinarith : (0 : Real) <= 4 * x))]
    · have hypos : 1 <= y := Nat.one_le_iff_ne_zero.mpr hy0
      have hyR : (1 : Real) <= y := by exact_mod_cast hypos
      have hresNonneg :
          0 <= (1 : Real) / 6 * (b : Real) *
            (4 * (x : Real) - 15 * (y : Real)) := by
        nlinarith [mul_nonneg (by norm_num : (0 : Real) <= 1 / 6)
          (mul_nonneg (by positivity : (0 : Real) <= (b : Real))
            (by nlinarith))]
      nlinarith [mul_nonneg (by norm_num : (0 : Real) <= 1 / 18)
        (mul_nonneg hxNonneg (by positivity : (0 : Real) <= (y : Real)))]
  have hnum : (n : Real) / 54 <= deficit := by nlinarith
  have hDle : D <= (n : Real) * (n : Real) := by
    dsimp only [D]
    have : ((n - 1 : Nat) : Real) <= n := by
      exact_mod_cast (by omega : n - 1 <= n)
    nlinarith
  rw [div_le_div_iff₀ (by positivity : (0 : Real) < 64 * n) hDpos]
  nlinarith [mul_pos (by norm_num : (0 : Real) < 64) hnR]

/-- Pointwise event-factor estimate for the final physical potential.  The
zero-weight cases are charged by the zero scheduler mass; positive-weight
cases have the exact factor listed in `singleFinalFactorReal`. -/
theorem singleFinal_term_toReal_le {n : Nat} (s : SingleState n)
    (h2 : 2 <= s.1.x + s.1.y + s.1.b) (k : SingleComp) :
    (singleCompPMF s.1.x s.1.y s.1.b h2 k *
        singleFinalV (SingleComp.nextSingleState s k)).toReal <=
      (singleCompPMF s.1.x s.1.y s.1.b h2 k).toReal *
        (singleFinalFactorReal k * singleFinalVReal s) := by
  cases k
  · by_cases hw :
        SingleComp.weight s.1.x s.1.y s.1.b SingleComp.xx = 0
    · rw [singleCompPMF_zero_of_weight_zero hw]
      simp
    · unfold SingleComp.nextSingleState
      rw [dif_neg hw, ENNReal.toReal_mul, singleFinalV_toReal]
      apply mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp [singleFinalVReal, singleFinalFactorReal, SingleComp.next]
  · by_cases hw :
        SingleComp.weight s.1.x s.1.y s.1.b SingleComp.xyToX = 0
    · rw [singleCompPMF_zero_of_weight_zero hw]
      simp
    · unfold SingleComp.nextSingleState
      rw [dif_neg hw, ENNReal.toReal_mul, singleFinalV_toReal]
      apply mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp only [singleFinalVReal, singleFinalFactorReal, SingleComp.next,
        SingleComp.weight] at hw ⊢
      rcases Nat.mul_ne_zero_iff.mp hw with ⟨_hx0, hy0⟩
      have hy1 : 1 <= y := Nat.one_le_iff_ne_zero.mpr hy0
      have hpowY : singleFinalYBaseReal ^ y =
          singleFinalYBaseReal ^ (y - 1) * singleFinalYBaseReal := by
        rw [← pow_succ]
        congr 1
        omega
      have hpowa : singleFinalBlankBaseReal ^ (b + 1) =
          singleFinalBlankBaseReal ^ b * singleFinalBlankBaseReal := by
        rw [pow_succ]
      rw [hpowY, hpowa]
      dsimp [singleFinalYBaseReal, singleFinalBlankBaseReal]
      ring_nf
      exact le_rfl
  · by_cases hw :
        SingleComp.weight s.1.x s.1.y s.1.b SingleComp.xyToY = 0
    · rw [singleCompPMF_zero_of_weight_zero hw]
      simp
    · unfold SingleComp.nextSingleState
      rw [dif_neg hw, ENNReal.toReal_mul, singleFinalV_toReal]
      apply mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp only [singleFinalVReal, singleFinalFactorReal, SingleComp.next,
        SingleComp.weight] at hw ⊢
      have hpowa : singleFinalBlankBaseReal ^ (b + 1) =
          singleFinalBlankBaseReal ^ b * singleFinalBlankBaseReal := by
        rw [pow_succ]
      rw [hpowa]
      dsimp [singleFinalBlankBaseReal]
      ring_nf
      exact le_rfl
  · by_cases hw :
        SingleComp.weight s.1.x s.1.y s.1.b SingleComp.yy = 0
    · rw [singleCompPMF_zero_of_weight_zero hw]
      simp
    · unfold SingleComp.nextSingleState
      rw [dif_neg hw, ENNReal.toReal_mul, singleFinalV_toReal]
      apply mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp [singleFinalVReal, singleFinalFactorReal, SingleComp.next]
  · by_cases hw :
        SingleComp.weight s.1.x s.1.y s.1.b SingleComp.xb = 0
    · rw [singleCompPMF_zero_of_weight_zero hw]
      simp
    · unfold SingleComp.nextSingleState
      rw [dif_neg hw, ENNReal.toReal_mul, singleFinalV_toReal]
      apply mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp only [singleFinalVReal, singleFinalFactorReal, SingleComp.next,
        SingleComp.weight] at hw ⊢
      rcases Nat.mul_ne_zero_iff.mp hw with ⟨_hx2, hb0⟩
      have hb1 : 1 <= b := Nat.one_le_iff_ne_zero.mpr hb0
      have hpowa : singleFinalBlankBaseReal ^ b =
          singleFinalBlankBaseReal ^ (b - 1) * singleFinalBlankBaseReal := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpowa]
      dsimp [singleFinalBlankBaseReal]
      ring_nf
      exact le_rfl
  · by_cases hw :
        SingleComp.weight s.1.x s.1.y s.1.b SingleComp.yb = 0
    · rw [singleCompPMF_zero_of_weight_zero hw]
      simp
    · unfold SingleComp.nextSingleState
      rw [dif_neg hw, ENNReal.toReal_mul, singleFinalV_toReal]
      apply mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp only [singleFinalVReal, singleFinalFactorReal, SingleComp.next,
        SingleComp.weight] at hw ⊢
      rcases Nat.mul_ne_zero_iff.mp hw with ⟨_hy2, hb0⟩
      have hb1 : 1 <= b := Nat.one_le_iff_ne_zero.mpr hb0
      have hpowa : singleFinalBlankBaseReal ^ b =
          singleFinalBlankBaseReal ^ (b - 1) * singleFinalBlankBaseReal := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpowa, pow_succ]
      dsimp [singleFinalYBaseReal, singleFinalBlankBaseReal]
      ring_nf
      exact le_rfl
  · by_cases hw :
        SingleComp.weight s.1.x s.1.y s.1.b SingleComp.bb = 0
    · rw [singleCompPMF_zero_of_weight_zero hw]
      simp
    · unfold SingleComp.nextSingleState
      rw [dif_neg hw, ENNReal.toReal_mul, singleFinalV_toReal]
      apply mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp [singleFinalVReal, singleFinalFactorReal, SingleComp.next]

/-- Finite-event expectation bound after converting the final potential to
Real arithmetic. -/
theorem singleFinal_expect_toReal_le_factor_sum
    (n : Nat) (hn : 2 <= n) (s : SingleState n)
    (h2 : 2 <= s.1.x + s.1.y + s.1.b) :
    (expect (singleStateStep n hn s) singleFinalV).toReal <=
      ∑ k : SingleComp,
        (singleCompPMF s.1.x s.1.y s.1.b h2 k).toReal *
          (singleFinalFactorReal k * singleFinalVReal s) := by
  rw [expect_singleStateStep n hn s singleFinalV]
  rw [ENNReal.toReal_sum]
  · exact Finset.sum_le_sum fun k _hk =>
      singleFinal_term_toReal_le s h2 k
  · intro k _hk
    exact ENNReal.mul_ne_top (singleCompPMF_ne_top k)
      (singleFinalV_ne_top (SingleComp.nextSingleState s k))

/-- Algebraic identity for the seven weighted event factors.  The deficit is
the strict contraction from the fair creation pair plus the net blank-resolution
drift. -/
theorem singleFinal_factor_weight_identity (x y b : Nat) :
    let weighted : Real :=
      (2 * Nat.choose x 2 : Nat) * 1 +
        (x * y : Nat) * ((4 : Real) / 9) +
        (x * y : Nat) * ((3 : Real) / 2) +
        (2 * Nat.choose y 2 : Nat) * 1 +
        (2 * x * b : Nat) * ((2 : Real) / 3) +
        (2 * y * b : Nat) * ((9 : Real) / 4) +
        (2 * Nat.choose b 2 : Nat) * 1
    let total : Real :=
      (2 * Nat.choose x 2 : Nat) + (x * y : Nat) + (x * y : Nat) +
        (2 * Nat.choose y 2 : Nat) + (2 * x * b : Nat) +
        (2 * y * b : Nat) + (2 * Nat.choose b 2 : Nat)
    let deficit : Real :=
      (1 : Real) / 18 * (x : Real) * (y : Real) +
        (1 : Real) / 6 * (b : Real) *
          (4 * (x : Real) - 15 * (y : Real))
    weighted = total - deficit := by
  intro weighted total deficit
  dsimp only [weighted, total, deficit]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The finite event-factor sum contracts by `1 - 1/(64n)` in the live final
region. -/
theorem singleFinal_factor_sum_le_contract
    (n : Nat) (hn : 2 <= n) (s : SingleState n)
    (h2 : 2 <= s.1.x + s.1.y + s.1.b)
    (hco : s.1.doubleCoLevel < 2 * n / 3)
    (hmaj : 4 * s.1.y <= s.1.x)
    (hncons : ¬ BiXConsensus n s.1) :
    (∑ k : SingleComp,
        (singleCompPMF s.1.x s.1.y s.1.b h2 k).toReal *
          (singleFinalFactorReal k * singleFinalVReal s)) <=
      (1 - (1 : Real) / (64 * (n : Real))) * singleFinalVReal s := by
  rcases s with ⟨⟨x, y, b⟩, hinv⟩
  simp only [BiCfg.doubleCoLevel] at hco
  simp only [BiCfg.DoubleInv] at hinv
  simp only [BiXConsensus] at hncons
  have hpos : 0 < 2 * y + b := by
    by_contra hz
    have hzero : 2 * y + b = 0 := by omega
    have hy0 : y = 0 := by omega
    have hb0 : b = 0 := by omega
    have hx : x = n := by omega
    exact hncons ⟨hx, hy0, hb0⟩
  let D : Real := (n : Real) * ((n - 1 : Nat) : Real)
  let deficit : Real :=
    (1 : Real) / 18 * (x : Real) * (y : Real) +
      (1 : Real) / 6 * (b : Real) *
        (4 * (x : Real) - 15 * (y : Real))
  let weighted : Real :=
    (2 * Nat.choose x 2 : Nat) * 1 +
      (x * y : Nat) * ((4 : Real) / 9) +
      (x * y : Nat) * ((3 : Real) / 2) +
      (2 * Nat.choose y 2 : Nat) * 1 +
      (2 * x * b : Nat) * ((2 : Real) / 3) +
      (2 * y * b : Nat) * ((9 : Real) / 4) +
      (2 * Nat.choose b 2 : Nat) * 1
  let total : Real :=
    (2 * Nat.choose x 2 : Nat) + (x * y : Nat) + (x * y : Nat) +
      (2 * Nat.choose y 2 : Nat) + (2 * x * b : Nat) +
      (2 * y * b : Nat) + (2 * Nat.choose b 2 : Nat)
  let V : Real := singleFinalVReal (⟨⟨x, y, b⟩, hinv⟩ : SingleState n)
  have hDpos : 0 < D := by
    dsimp only [D]
    have hnpos : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1pos : (0 : Real) < ((n - 1 : Nat) : Real) := by
      exact_mod_cast (by omega : 0 < n - 1)
    positivity
  have hdenNat : 2 * Nat.choose (x + y + b) 2 = n * (n - 1) := by
    rw [hinv]
    exact two_mul_choose_two n
  have hdenR :
      ((2 * Nat.choose (x + y + b) 2 : Nat) : Real) = D := by
    dsimp only [D]
    rw [hdenNat]
    norm_num only [Nat.cast_mul]
  have htotalR : total = D := by
    have hsumw := singleComp_sum_weight x y b
    have hsumwR := congrArg (fun m : Nat => (m : Real)) hsumw
    have htotalDen :
        total = ((2 * Nat.choose (x + y + b) 2 : Nat) : Real) := by
      dsimp only [total]
      rw [show (Finset.univ : Finset SingleComp) =
        {SingleComp.xx, SingleComp.xyToX, SingleComp.xyToY,
          SingleComp.yy, SingleComp.xb, SingleComp.yb,
          SingleComp.bb} from rfl] at hsumwR
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton] at hsumwR
      norm_num only [SingleComp.weight, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat] at hsumwR
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      nlinarith
    exact htotalDen.trans hdenR
  have hweighted : weighted = total - deficit := by
    simpa only [weighted, total, deficit] using
      singleFinal_factor_weight_identity x y b
  have hgap :
      (1 : Real) / (64 * (n : Real)) <= deficit / D := by
    simpa only [D, deficit] using
      singleFinal_scalar_gap n x y b hn hinv hmaj hco hpos
  have hVnonneg : 0 <= V := by
    dsimp only [V, singleFinalVReal, singleFinalYBaseReal,
      singleFinalBlankBaseReal]
    positivity
  have hleft :
      (∑ k : SingleComp,
          (singleCompPMF x y b h2 k).toReal *
            (singleFinalFactorReal k * V)) = V * (weighted / D) := by
    rw [show (Finset.univ : Finset SingleComp) =
      {SingleComp.xx, SingleComp.xyToX, SingleComp.xyToY,
        SingleComp.yy, SingleComp.xb, SingleComp.yb,
        SingleComp.bb} from rfl]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp only [singleCompPMF_toReal, singleFinalFactorReal, SingleComp.weight]
    rw [hdenR]
    dsimp only [weighted]
    field_simp [hDpos.ne']
    ring
  change
      (∑ k : SingleComp,
          (singleCompPMF x y b h2 k).toReal *
            (singleFinalFactorReal k * V)) <=
        (1 - (1 : Real) / (64 * (n : Real))) * V
  rw [hleft, hweighted, htotalR]
  have hgap' : 1 - deficit / D <= 1 - (1 : Real) / (64 * (n : Real)) := by
    linarith
  have hDne : D ≠ 0 := hDpos.ne'
  calc
    V * ((D - deficit) / D)
        = (1 - deficit / D) * V := by
          field_simp [hDne]
    _ <= (1 - (1 : Real) / (64 * (n : Real))) * V := by
      exact mul_le_mul_of_nonneg_right hgap' hVnonneg

/-- Raw-step contraction factor for the physical final potential. -/
noncomputable def singleFinalPhi (n : Nat) : ENNReal :=
  ENNReal.ofReal (1 - (1 : Real) / (64 * (n : Real)))

/-- The final potential has finite one-step expectation. -/
theorem expect_singleStateStep_singleFinalV_ne_top
    (n : Nat) (hn : 2 <= n) (s : SingleState n) :
    expect (singleStateStep n hn s) singleFinalV ≠ ⊤ := by
  rw [expect_singleStateStep n hn s singleFinalV]
  rw [ENNReal.sum_ne_top]
  intro k _hk
  exact ENNReal.mul_ne_top (singleCompPMF_ne_top k)
    (singleFinalV_ne_top (SingleComp.nextSingleState s k))

/-- One raw Single-B step contracts `singleFinalV` throughout the live final
region. -/
theorem singleFinalV_step_contract
    (n : Nat) (hn : 2 <= n) (s : SingleState n)
    (hco : s.1.doubleCoLevel < 2 * n / 3)
    (hmaj : 4 * s.1.y <= s.1.x)
    (hncons : ¬ BiXConsensus n s.1) :
    expect (singleStateStep n hn s) singleFinalV <=
      singleFinalPhi n * singleFinalV s := by
  have h2 : 2 <= s.1.x + s.1.y + s.1.b := by
    have h := s.2
    simp only [BiCfg.DoubleInv] at h
    omega
  have hleft :=
    singleFinal_expect_toReal_le_factor_sum n hn s h2
  have hfactor :=
    singleFinal_factor_sum_le_contract n hn s h2 hco hmaj hncons
  have hbaseNonneg :
      0 <= 1 - (1 : Real) / (64 * (n : Real)) := by
    have hnpos : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
    have hnge : (2 : Real) <= n := by exact_mod_cast hn
    have hδ : (1 : Real) / (64 * (n : Real)) <= 1 := by
      rw [div_le_one (by positivity : (0 : Real) < 64 * n)]
      nlinarith
    linarith
  unfold singleFinalPhi
  rw [← ENNReal.toReal_le_toReal
    (expect_singleStateStep_singleFinalV_ne_top n hn s)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (singleFinalV_ne_top s))]
  rw [ENNReal.toReal_mul, singleFinalV_toReal,
    ENNReal.toReal_ofReal hbaseNonneg]
  exact hleft.trans hfactor

/-- Final high co-level boundary used in the physical block. -/
def singleFinalBoundary (n : Nat) : Nat := 2 * n / 3

theorem singleFinal_not_bad_live_bounds {n : Nat} (s : SingleState n)
    (hbad : ¬ SingleFinalBad (singleFinalBoundary n) s) :
    s.1.doubleCoLevel < 2 * n / 3 ∧ 4 * s.1.y <= s.1.x := by
  unfold SingleFinalBad singleFinalBoundary at hbad
  constructor <;> omega

theorem singleFinalPhi_le_one (n : Nat) (hn : 1 <= n) :
    singleFinalPhi n <= 1 := by
  unfold singleFinalPhi
  rw [show (1 : ENNReal) = ENNReal.ofReal (1 : Real) by
    exact ENNReal.ofReal_one.symm]
  apply ENNReal.ofReal_le_ofReal
  have hnpos : (0 : Real) < n := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  have hδnonneg : (0 : Real) <= (1 : Real) / (64 * (n : Real)) := by
    positivity
  linarith

/-- The masked final potential is pointwise dominated by the raw potential. -/
theorem singleFinalMaskedV_le (B : Nat) {n : Nat} (s : SingleState n) :
    singleFinalMaskedV B s <= singleFinalV s := by
  unfold singleFinalMaskedV
  split_ifs <;> simp

/-- One-step contraction for the final masked potential under the chain frozen
at the high co-level boundary. -/
theorem singleFinalMaskedV_step_contract
    (n : Nat) (hn : 2 <= n) (s : SingleState n) :
    expect (freeze (SingleFinalBad (singleFinalBoundary n))
        (singleStateStep n hn) s)
        (singleFinalMaskedV (singleFinalBoundary n)) <=
      singleFinalPhi n * singleFinalMaskedV (singleFinalBoundary n) s := by
  by_cases hbad : SingleFinalBad (singleFinalBoundary n) s
  · rw [freeze_of_mem s hbad, expect_pure]
    simp [singleFinalMaskedV, hbad]
  · by_cases hcons : BiXConsensus n s.1
    · have hDX : DoubleXConsensus s := by
        simpa [DoubleXConsensus, BiXConsensus] using hcons
      rw [freeze_of_not_mem s hbad, singleStateStep_consensusX n hn s hDX,
        expect_pure]
      simp [singleFinalMaskedV, hbad, hcons]
    · rw [freeze_of_not_mem s hbad]
      rcases singleFinal_not_bad_live_bounds s hbad with ⟨hco, hmaj⟩
      have hraw := singleFinalV_step_contract n hn s hco hmaj hcons
      have hmask :
          expect (singleStateStep n hn s)
              (singleFinalMaskedV (singleFinalBoundary n)) <=
            expect (singleStateStep n hn s) singleFinalV := by
        unfold expect
        exact ENNReal.tsum_le_tsum fun z =>
          mul_le_mul_left' (singleFinalMaskedV_le (singleFinalBoundary n) z) _
      calc
        expect (singleStateStep n hn s)
            (singleFinalMaskedV (singleFinalBoundary n))
            <= expect (singleStateStep n hn s) singleFinalV := hmask
        _ <= singleFinalPhi n * singleFinalV s := hraw
        _ = singleFinalPhi n *
            singleFinalMaskedV (singleFinalBoundary n) s := by
          simp [singleFinalMaskedV, hbad, hcons]

/-- The unmasked final potential is a supermartingale for the chain stopped at
the high co-level boundary. -/
theorem singleFinalV_step_super_stopped
    (n : Nat) (hn : 2 <= n) (s : SingleState n) :
    expect (freeze (SingleFinalBad (singleFinalBoundary n))
        (singleStateStep n hn) s) singleFinalV <= singleFinalV s := by
  by_cases hbad : SingleFinalBad (singleFinalBoundary n) s
  · rw [freeze_of_mem s hbad, expect_pure]
  · by_cases hcons : BiXConsensus n s.1
    · have hDX : DoubleXConsensus s := by
        simpa [DoubleXConsensus, BiXConsensus] using hcons
      rw [freeze_of_not_mem s hbad, singleStateStep_consensusX n hn s hDX,
        expect_pure]
    · rw [freeze_of_not_mem s hbad]
      rcases singleFinal_not_bad_live_bounds s hbad with ⟨hco, hmaj⟩
      have hraw := singleFinalV_step_contract n hn s hco hmaj hcons
      calc
        expect (singleStateStep n hn s) singleFinalV
            <= singleFinalPhi n * singleFinalV s := hraw
        _ <= 1 * singleFinalV s := by
          exact mul_le_mul_right' (singleFinalPhi_le_one n (by omega : 1 <= n)) _
        _ = singleFinalV s := one_mul _

/-- The blank base in the final potential is at least one. -/
theorem singleFinalBlankBase_ge_one :
    (1 : ENNReal) <= singleFinalBlankBase := by
  rw [singleFinalBlankBase, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- The `Y` base is at least one. -/
theorem singleFinalYBase_ge_one :
    (1 : ENNReal) <= singleFinalYBase := by
  rw [singleFinalYBase, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- One blank-base unit is dominated by one `Y` factor. -/
theorem singleFinalBlankBase_le_yBase :
    singleFinalBlankBase <= singleFinalYBase := by
  rw [singleFinalBlankBase, singleFinalYBase]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Two co-units carried by a `Y` dominate the corresponding blank-base
potential. -/
theorem singleFinalBlankBase_sq_le_yBase :
    singleFinalBlankBase ^ 2 <= singleFinalYBase := by
  rw [singleFinalBlankBase, singleFinalYBase,
    ← ENNReal.ofReal_pow (by norm_num : (0 : Real) <= 3 / 2)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Three blank-base units are also dominated by one `Y` factor. -/
theorem singleFinalBlankBase_cube_le_yBase :
    singleFinalBlankBase ^ 3 <= singleFinalYBase := by
  rw [singleFinalBlankBase, singleFinalYBase,
    ← ENNReal.ofReal_pow (by norm_num : (0 : Real) <= 3 / 2)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Final potential is at least one. -/
theorem one_le_singleFinalV {n : Nat} (s : SingleState n) :
    (1 : ENNReal) <= singleFinalV s := by
  unfold singleFinalV
  exact one_le_mul (one_le_pow₀ singleFinalYBase_ge_one)
    (one_le_pow₀ singleFinalBlankBase_ge_one)

/-- If the co-level is at most `P`, then the final potential is bounded by
`YBase^P`. -/
theorem singleFinalV_le_yBase_pow_coCap {n P : Nat} (s : SingleState n)
    (hco : s.1.doubleCoLevel <= P) :
    singleFinalV s <= singleFinalYBase ^ P := by
  unfold singleFinalV
  have hblank :
      singleFinalBlankBase ^ s.1.b <= singleFinalYBase ^ s.1.b :=
    pow_le_pow_left' singleFinalBlankBase_le_yBase _
  calc
    singleFinalYBase ^ s.1.y * (singleFinalBlankBase ^ s.1.b)
        <= singleFinalYBase ^ s.1.y * singleFinalYBase ^ s.1.b := by
          exact mul_le_mul_left' hblank _
    _ = singleFinalYBase ^ (s.1.y + s.1.b) := by rw [← pow_add]
    _ <= singleFinalYBase ^ s.1.doubleCoLevel := by
      apply pow_le_pow_right₀ singleFinalYBase_ge_one
      unfold BiCfg.doubleCoLevel
      omega
    _ <= singleFinalYBase ^ P :=
      pow_le_pow_right₀ singleFinalYBase_ge_one hco

/-- Sharper start bound used for the high-boundary safety term: two co-units
cost at most one factor of `YBase`. -/
theorem singleFinalV_le_yBase_pow_half_coCap {n P : Nat} (s : SingleState n)
    (hco : s.1.doubleCoLevel <= P) :
    singleFinalV s <= singleFinalYBase ^ (P / 2 + 1) := by
  unfold singleFinalV
  have hblankPair :
      (singleFinalBlankBase ^ 2) ^ (s.1.b / 2 + 1) <=
        singleFinalYBase ^ (s.1.b / 2 + 1) :=
    pow_le_pow_left' singleFinalBlankBase_sq_le_yBase _
  have hblank :
      singleFinalBlankBase ^ s.1.b <=
        singleFinalYBase ^ (s.1.b / 2 + 1) := by
    have hb : s.1.b <= 2 * (s.1.b / 2 + 1) := by
      have hdiv := Nat.div_add_mod s.1.b 2
      have hmod := Nat.mod_lt s.1.b (by norm_num : 0 < 2)
      omega
    calc
      singleFinalBlankBase ^ s.1.b
          <= singleFinalBlankBase ^ (2 * (s.1.b / 2 + 1)) :=
            pow_le_pow_right₀ singleFinalBlankBase_ge_one hb
      _ = (singleFinalBlankBase ^ 2) ^ (s.1.b / 2 + 1) := by
        rw [pow_mul]
      _ <= singleFinalYBase ^ (s.1.b / 2 + 1) := hblankPair
  calc
    singleFinalYBase ^ s.1.y * (singleFinalBlankBase ^ s.1.b)
        <= singleFinalYBase ^ s.1.y *
          singleFinalYBase ^ (s.1.b / 2 + 1) := by
          exact mul_le_mul_left' hblank _
    _ = singleFinalYBase ^ (s.1.y + (s.1.b / 2 + 1)) := by
      rw [← pow_add]
    _ <= singleFinalYBase ^ (P / 2 + 1) := by
      apply pow_le_pow_right₀ singleFinalYBase_ge_one
      have hdiv := Nat.div_add_mod s.1.b 2
      have hmod := Nat.mod_lt s.1.b (by norm_num : 0 < 2)
      unfold BiCfg.doubleCoLevel at hco
      omega

/-- At the high co-level boundary the final potential is at least
`BlankBase^B`. -/
def singleFinalBadThreshold (n : Nat) : Nat := 3 * n / 5

/-- At either final bad boundary the final potential is at least the common
threshold `BlankBase^(3n/5)`. -/
theorem singleFinalBad_potential_ge {n : Nat} (s : SingleState n)
    (hbad : SingleFinalBad (singleFinalBoundary n) s) :
    singleFinalBlankBase ^ singleFinalBadThreshold n <= singleFinalV s := by
  unfold singleFinalV
  have hY2 :
      singleFinalBlankBase ^ (2 * s.1.y) <= singleFinalYBase ^ s.1.y := by
    rw [pow_mul]
    exact pow_le_pow_left' singleFinalBlankBase_sq_le_yBase _
  have hY3 :
      singleFinalBlankBase ^ (3 * s.1.y) <= singleFinalYBase ^ s.1.y := by
    rw [pow_mul]
    exact pow_le_pow_left' singleFinalBlankBase_cube_le_yBase _
  rcases hbad with hco | hmaj
  · have hthr : singleFinalBadThreshold n <= s.1.doubleCoLevel := by
      have hco' : 2 * n / 3 <= s.1.doubleCoLevel := by
        simpa [singleFinalBoundary] using hco
      dsimp [singleFinalBadThreshold]
      omega
    calc
      singleFinalBlankBase ^ singleFinalBadThreshold n
          <= singleFinalBlankBase ^ s.1.doubleCoLevel :=
            pow_le_pow_right₀ singleFinalBlankBase_ge_one hthr
      _ = singleFinalBlankBase ^ (2 * s.1.y + s.1.b) := by
        rfl
      _ = singleFinalBlankBase ^ (2 * s.1.y) *
            singleFinalBlankBase ^ s.1.b := by
        rw [pow_add]
      _ <= singleFinalYBase ^ s.1.y *
            singleFinalBlankBase ^ s.1.b := by
        exact mul_le_mul_right' hY2 _
  · have hthr : singleFinalBadThreshold n <= 3 * s.1.y + s.1.b := by
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp only [singleFinalBadThreshold, BiCfg.DoubleInv] at hinv ⊢
      simp only at hmaj
      omega
    calc
      singleFinalBlankBase ^ singleFinalBadThreshold n
          <= singleFinalBlankBase ^ (3 * s.1.y + s.1.b) :=
            pow_le_pow_right₀ singleFinalBlankBase_ge_one hthr
      _ = singleFinalBlankBase ^ (3 * s.1.y) *
            singleFinalBlankBase ^ s.1.b := by
        rw [pow_add]
      _ <= singleFinalYBase ^ s.1.y *
            singleFinalBlankBase ^ s.1.b := by
        exact mul_le_mul_right' hY3 _

/-- A late checkpoint is exactly a physical co-level cap. -/
theorem singleLateCheckpoint_co_le {n P : Nat} (s : SingleState n)
    (hs : SingleLateCheckpoint n P s) :
    s.1.doubleCoLevel <= P := by
  rcases s with ⟨⟨x, y, b⟩, hinv⟩
  simp only [SingleLateCheckpoint, BiCfg.doubleLevel, BiCfg.doubleCoLevel,
    BiCfg.DoubleInv] at hs hinv ⊢
  omega

/-- Floor arithmetic for comparing two dyadic scales two rungs apart. -/
theorem div_le_four_mul_div_add_three (n a : Nat) (ha : 0 < a) :
    n / a <= 4 * (n / (4 * a)) + 3 := by
  have hden : 0 < 4 * a := by positivity
  have hdiv := Nat.div_add_mod n (4 * a)
  have hmod := Nat.mod_lt n hden
  have hlt :
      n < a * (4 * (n / (4 * a)) + 4) := by
    calc
      n = 4 * a * (n / (4 * a)) + n % (4 * a) := hdiv.symm
      _ < 4 * a * (n / (4 * a)) + 4 * a := by
        exact Nat.add_lt_add_left hmod _
      _ = a * (4 * (n / (4 * a)) + 4) := by ring
  have hdivlt :
      n / a < 4 * (n / (4 * a)) + 4 :=
    (Nat.div_lt_iff_lt_mul ha).2 (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt)
  omega

/-- The concrete Single-B late target is at most `2*gamma*log₂ n+3`. -/
theorem singleLateTargetCap_le_two_gamma_log_add
    (n gamma : Nat) (hlog : 1024 <= Nat.log 2 n)
    (hgamma : 1 <= gamma)
    (hsize : 6 * gamma * Nat.log 2 n <= n) :
    singleLateTargetCap n gamma <= 2 * (gamma * Nat.log 2 n) + 3 := by
  have htwo :=
    singleLate_phase2StageCount_two_le n gamma hlog hgamma hsize
  have hne : ¬ singleLateDyadicStages n gamma = 0 := by
    unfold singleLateDyadicStages
    omega
  have hidx :
      1 + singleLateDyadicStages n gamma =
        phase2StageCount n gamma := by
    unfold singleLateDyadicStages
    omega
  let k := phase2StageCount n gamma
  have htarget :
      singleLateTargetCap n gamma = phase2Scale n k := by
    simp [singleLateTargetCap, singleLateDyadicCap, hne, hidx, k]
  have hscale :
      phase2Scale n k <= 4 * phase2Scale n (2 + k) + 3 := by
    unfold phase2Scale
    have ha : 0 < 2 ^ k := by positivity
    have hpow : 2 ^ (2 + k) = 4 * 2 ^ k := by
      rw [pow_add]
      norm_num
    rw [hpow]
    exact div_le_four_mul_div_add_three n (2 ^ k) ha
  have hspec := phase2StageCount_spec n gamma
  change 2 * phase2Scale n (2 + k) <= gamma * Nat.log 2 n at hspec
  rw [htarget]
  omega

/-- Numeric room in the final safety denominator after rewriting
`YBase = BlankBase^3`.  With `G = γ log₂ n`, the late cap contributes at most
`3*(G+2)` blank-base exponents, while the bad threshold keeps an additional
`G/2` exponents of slack. -/
theorem singleFinalSafety_exponent_room
    {n G P : Nat} (hG : 1024 <= G) (hP : P <= 2 * G + 3)
    (hsize : 6 * G <= n) :
    3 * (P / 2 + 1) + G / 2 <= 3 * n / 5 := by
  omega

theorem singleFinalBlankBaseReal_log_ge :
    (1 / 3 : Real) <= Real.log singleFinalBlankBaseReal := by
  have hpos : (0 : Real) < (2 / 3 : Real) := by norm_num
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hinv :
      Real.log ((2 : Real) / 3) =
        - Real.log singleFinalBlankBaseReal := by
    rw [show ((2 : Real) / 3) = singleFinalBlankBaseReal⁻¹ by
      unfold singleFinalBlankBaseReal
      field_simp]
    rw [Real.log_inv]
  rw [hinv] at hlog
  norm_num at hlog ⊢
  linarith

theorem singleFinalBlankBaseReal_log_le :
    Real.log singleFinalBlankBaseReal <= (1 / 2 : Real) := by
  have hpos : (0 : Real) < singleFinalBlankBaseReal := by
    unfold singleFinalBlankBaseReal
    norm_num
  have hlog := Real.log_le_sub_one_of_pos hpos
  unfold singleFinalBlankBaseReal at hlog ⊢
  norm_num at hlog ⊢
  linarith

theorem singleFinalYBaseReal_log_le :
    Real.log singleFinalYBaseReal <= (3 / 2 : Real) := by
  have hpow : singleFinalYBaseReal = singleFinalBlankBaseReal ^ 3 := by
    unfold singleFinalYBaseReal singleFinalBlankBaseReal
    norm_num
  rw [hpow, Real.log_pow]
  nlinarith [singleFinalBlankBaseReal_log_le]

theorem singleFinal_realLog_le_natLog
    (n : Nat) (hn : 0 < n) (hlog : 128 <= Nat.log 2 n) :
    Real.log (n : Real) <= (Nat.log 2 n : Real) := by
  have hlogn :
      Real.log n <= ((Nat.log 2 n : Real) + 1) * Real.log 2 := by
    have hup : n < 2 ^ (Nat.log 2 n + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : Nat)) n
    have hlt :
        Real.log n < Real.log (2 ^ (Nat.log 2 n + 1)) :=
      Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast hup)
    rw [Real.log_pow] at hlt
    push_cast at hlt
    linarith
  have hfactor :
      ((Nat.log 2 n : Real) + 1) * Real.log 2 <=
        (Nat.log 2 n : Real) := by
    have hlog2 : Real.log 2 < (0.6931471808 : Real) :=
      Real.log_two_lt_d9
    have hlog2Nonneg : 0 <= Real.log 2 :=
      (Real.log_pos (by norm_num)).le
    have hL : (128 : Real) <= Nat.log 2 n := by exact_mod_cast hlog
    nlinarith
  exact hlogn.trans hfactor

theorem singleFinal_ofReal_exp_neg_le_inv_rpow
    (n : Nat) (hn : 0 < n) (S a : Real)
    (hS : Real.log (n : Real) * a <= S) :
    ENNReal.ofReal (Real.exp (-S)) <=
      (n : ENNReal)⁻¹ ^ a := by
  have hrpow :
      (n : ENNReal)⁻¹ ^ a =
        ENNReal.ofReal ((n : Real) ^ (-a)) := by
    rw [ENNReal.inv_rpow, ← ENNReal.ofReal_natCast n,
      ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hn),
      ← ENNReal.ofReal_inv_of_pos (by positivity),
      Real.rpow_neg (by positivity)]
  rw [hrpow]
  apply ENNReal.ofReal_le_ofReal
  have hpExp : (0 : Real) < Real.exp (-S) := Real.exp_pos _
  have hpPow : (0 : Real) < (n : Real) ^ (-a) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hlogIneq :
      Real.log (Real.exp (-S)) <= Real.log ((n : Real) ^ (-a)) := by
    rw [Real.log_exp, Real.log_rpow (by exact_mod_cast hn)]
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlogIneq
  rwa [Real.exp_log hpExp, Real.exp_log hpPow] at hexp

theorem singleFinal_exp_gamma_log_le_power
    (n gamma : Nat) (hlog : 128 <= Nat.log 2 n) :
    ENNReal.ofReal
        (Real.exp (-((gamma * Nat.log 2 n : Nat) : Real) / 16)) <=
      (n : ENNReal)⁻¹ ^ ((1 / 64 : Real) * (gamma : Real)) := by
  have hn : 0 < n := by
    have hnLarge : 4096 <= n :=
      phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hpow :=
    singleFinal_ofReal_exp_neg_le_inv_rpow n hn
      (((gamma * Nat.log 2 n : Nat) : Real) / 16)
      ((1 / 64 : Real) * (gamma : Real)) (by
        have hlogn := singleFinal_realLog_le_natLog n hn hlog
        have hγ0 : (0 : Real) <= gamma := by positivity
        have hmul :
            Real.log (n : Real) * ((1 / 64 : Real) * (gamma : Real)) <=
              (Nat.log 2 n : Real) *
                ((1 / 64 : Real) * (gamma : Real)) := by
          exact mul_le_mul_of_nonneg_right hlogn (by positivity)
        norm_num only [Nat.cast_mul]
        nlinarith)
  simpa [neg_div] using hpow

/-- Safety term for the final physical block. -/
noncomputable def singleFinalSafetyTerm (n gamma : Nat) : ENNReal :=
  singleFinalYBase ^ (singleLateTargetCap n gamma / 2 + 1) /
    (singleFinalBlankBase ^ singleFinalBadThreshold n)

/-- Live deadline term for the final physical block. -/
noncomputable def singleFinalLiveTerm (n gamma : Nat) : ENNReal :=
  singleFinalPhi n ^ singleFinalHorizon n gamma *
    singleFinalYBase ^ singleLateTargetCap n gamma

noncomputable def singleFinalError (n gamma : Nat) : ENNReal :=
  singleFinalSafetyTerm n gamma + singleFinalLiveTerm n gamma

theorem singleFinalSafetyTerm_ne_top (n gamma : Nat) :
    singleFinalSafetyTerm n gamma ≠ ⊤ := by
  unfold singleFinalSafetyTerm
  apply ENNReal.div_ne_top
  · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  · apply pow_ne_zero
    rw [singleFinalBlankBase]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)

theorem singleFinalSafetyTerm_toReal (n gamma : Nat) :
    (singleFinalSafetyTerm n gamma).toReal =
      singleFinalYBaseReal ^ (singleLateTargetCap n gamma / 2 + 1) /
        singleFinalBlankBaseReal ^ singleFinalBadThreshold n := by
  unfold singleFinalSafetyTerm
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_pow]
  unfold singleFinalYBase singleFinalBlankBase singleFinalYBaseReal
    singleFinalBlankBaseReal
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : Real) <= 27 / 8),
    ENNReal.toReal_ofReal (by norm_num : (0 : Real) <= 3 / 2)]

/-- The safety stream in the physical final block has exponential slack
`exp(-γ log₂ n / 16)`. -/
theorem singleFinalSafetyTerm_le_exp
    (n gamma : Nat) (hlog : 1024 <= Nat.log 2 n)
    (hgamma : 1 <= gamma)
    (hsize : 6 * gamma * Nat.log 2 n <= n) :
    singleFinalSafetyTerm n gamma <=
      ENNReal.ofReal
        (Real.exp (-((gamma * Nat.log 2 n : Nat) : Real) / 16)) := by
  rw [← ENNReal.toReal_le_toReal
    (singleFinalSafetyTerm_ne_top n gamma) ENNReal.ofReal_ne_top]
  rw [singleFinalSafetyTerm_toReal,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  set G : Nat := gamma * Nat.log 2 n
  set P : Nat := singleLateTargetCap n gamma
  set m : Nat := P / 2 + 1
  set θ : Nat := singleFinalBadThreshold n
  have hP : P <= 2 * G + 3 := by
    dsimp only [P, G]
    exact singleLateTargetCap_le_two_gamma_log_add n gamma hlog hgamma
      hsize
  have hG : 1024 <= G := by
    dsimp only [G]
    calc
      1024 <= Nat.log 2 n := hlog
      _ = 1 * Nat.log 2 n := by ring
      _ <= gamma * Nat.log 2 n :=
        Nat.mul_le_mul_right _ hgamma
  have hsizeG : 6 * G <= n := by
    dsimp only [G]
    simpa [Nat.mul_assoc] using hsize
  have hroom :
      3 * m + G / 2 <= θ := by
    dsimp only [m, θ]
    exact singleFinalSafety_exponent_room (n := n) (G := G) (P := P)
      hG hP hsizeG
  have hYpos : (0 : Real) < singleFinalYBaseReal := by
    unfold singleFinalYBaseReal
    norm_num
  have hBpos : (0 : Real) < singleFinalBlankBaseReal := by
    unfold singleFinalBlankBaseReal
    norm_num
  have hExprPos :
      (0 : Real) <
        singleFinalYBaseReal ^ m /
          singleFinalBlankBaseReal ^ θ := by
    exact div_pos (pow_pos hYpos _) (pow_pos hBpos _)
  have hYlog :
      Real.log singleFinalYBaseReal =
        3 * Real.log singleFinalBlankBaseReal := by
    have hpow : singleFinalYBaseReal = singleFinalBlankBaseReal ^ 3 := by
      unfold singleFinalYBaseReal singleFinalBlankBaseReal
      norm_num
    rw [hpow, Real.log_pow]
    norm_num
  have hlogEq :
      Real.log
          (singleFinalYBaseReal ^ m /
            singleFinalBlankBaseReal ^ θ) =
        (3 * (m : Real) - (θ : Real)) *
          Real.log singleFinalBlankBaseReal := by
    rw [Real.log_div (pow_ne_zero _ hYpos.ne')
      (pow_ne_zero _ hBpos.ne'), Real.log_pow, Real.log_pow, hYlog]
    ring
  have hroomR : ((3 * m + G / 2 : Nat) : Real) <= (θ : Real) := by
    exact_mod_cast hroom
  have hfloorNat : G <= 3 * (G / 2) := by
    omega
  have hfloorR : (G : Real) / 3 <= ((G / 2 : Nat) : Real) := by
    have hcast : (G : Real) <= 3 * ((G / 2 : Nat) : Real) := by
      exact_mod_cast hfloorNat
    nlinarith
  have hslack :
      (G : Real) / 3 <= (θ : Real) - 3 * (m : Real) := by
    norm_num only [Nat.cast_add, Nat.cast_mul] at hroomR
    nlinarith
  have hslackNonneg :
      0 <= (θ : Real) - 3 * (m : Real) := by
    have hG0 : (0 : Real) <= G := by positivity
    nlinarith
  have hprod :
      (G : Real) / 9 <=
        ((θ : Real) - 3 * (m : Real)) *
          Real.log singleFinalBlankBaseReal := by
    have hmul := mul_le_mul hslack singleFinalBlankBaseReal_log_ge
      (by norm_num : (0 : Real) <= 1 / 3) hslackNonneg
    nlinarith
  have hlogLe :
      Real.log
          (singleFinalYBaseReal ^ m /
            singleFinalBlankBaseReal ^ θ) <=
        -((G : Real) / 16) := by
    rw [hlogEq]
    have hneg :
        (3 * (m : Real) - (θ : Real)) *
            Real.log singleFinalBlankBaseReal =
          -(((θ : Real) - 3 * (m : Real)) *
            Real.log singleFinalBlankBaseReal) := by
      ring
    rw [hneg]
    have hG0 : (0 : Real) <= G := by positivity
    have hprod16 :
        (G : Real) / 16 <=
          ((θ : Real) - 3 * (m : Real)) *
            Real.log singleFinalBlankBaseReal := by
      nlinarith
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlogLe
  rw [Real.exp_log hExprPos] at hexp
  simpa [G, P, m, θ, neg_div] using hexp

/-- The live stopped-supermartingale stream is far below the common final
exponential envelope.  The raw horizon gives `1024*(γ log₂ n+1)` units of
geometric decay, while the starting potential costs only `O(γ log₂ n)`. -/
theorem singleFinalLiveTerm_le_exp
    (n gamma : Nat) (hlog : 1024 <= Nat.log 2 n)
    (hgamma : 1 <= gamma)
    (hsize : 6 * gamma * Nat.log 2 n <= n) :
    singleFinalLiveTerm n gamma <=
      ENNReal.ofReal
        (Real.exp (-((gamma * Nat.log 2 n : Nat) : Real) / 16)) := by
  set G : Nat := gamma * Nat.log 2 n
  set P : Nat := singleLateTargetCap n gamma
  set T : Nat := singleFinalHorizon n gamma
  let δ : Real := (1 : Real) / (64 * (n : Real))
  have hnLarge : 4096 <= n :=
    phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
  have hn : 0 < n := by omega
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hδ0 : 0 <= δ := by
    dsimp only [δ]
    positivity
  have hδ1 : δ <= 1 := by
    dsimp only [δ]
    exact (div_le_one (by positivity : (0 : Real) < 64 * n)).2
      (by
        have hnOneR : (1 : Real) <= n := by
          exact_mod_cast (Nat.succ_le_iff.mp hn)
        nlinarith)
  have hphiBase :
      singleFinalPhi n <= ENNReal.ofReal (1 - δ) := by
    unfold singleFinalPhi
    rfl
  have hphi :
      singleFinalPhi n ^ T <=
        ENNReal.ofReal (Real.exp (-(δ * (T : Real)))) :=
    enn_pow_le_ofReal_exp (singleFinalPhi n) δ T hδ0 hδ1 hphiBase
  have hYreal :
      singleFinalYBaseReal ^ P <=
        Real.exp ((3 / 2 : Real) * (P : Real)) := by
    have hYpos : (0 : Real) < singleFinalYBaseReal := by
      unfold singleFinalYBaseReal
      norm_num
    rw [← Real.exp_log (pow_pos hYpos P)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    nlinarith [singleFinalYBaseReal_log_le]
  have hY :
      singleFinalYBase ^ P <=
        ENNReal.ofReal (Real.exp ((3 / 2 : Real) * (P : Real))) := by
    unfold singleFinalYBase
    rw [← ENNReal.ofReal_pow (by norm_num : (0 : Real) <= 27 / 8)]
    simpa [singleFinalYBaseReal] using ENNReal.ofReal_le_ofReal hYreal
  have hP : P <= 2 * G + 3 := by
    dsimp only [P, G]
    exact singleLateTargetCap_le_two_gamma_log_add n gamma hlog hgamma
      hsize
  have hdeltaT :
      δ * (T : Real) =
        1024 * ((G + 1 : Nat) : Real) := by
    dsimp only [δ, T, G]
    unfold singleFinalHorizon singleFinalScale
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hnR.ne']
    ring
  have hexponent :
      -(δ * (T : Real)) + (3 / 2 : Real) * (P : Real) <=
        -((G : Real) / 16) := by
    have hPcast : (P : Real) <= 2 * (G : Real) + 3 := by
      exact_mod_cast hP
    rw [hdeltaT]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hG0 : (0 : Real) <= G := by positivity
    nlinarith
  calc
    singleFinalLiveTerm n gamma
        = singleFinalPhi n ^ singleFinalHorizon n gamma *
          singleFinalYBase ^ singleLateTargetCap n gamma := by
          rfl
    _ <= ENNReal.ofReal (Real.exp (-(δ * (T : Real)))) *
          ENNReal.ofReal (Real.exp ((3 / 2 : Real) * (P : Real))) := by
          simpa [P, T] using mul_le_mul hphi hY
    _ = ENNReal.ofReal
          (Real.exp (-(δ * (T : Real)) +
            (3 / 2 : Real) * (P : Real))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    _ <= ENNReal.ofReal
          (Real.exp (-((G : Real) / 16))) := by
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)
    _ = ENNReal.ofReal
          (Real.exp (-((gamma * Nat.log 2 n : Nat) : Real) / 16)) := by
      simp [G, neg_div]

/-- The two final physical streams fit an inverse-power envelope. -/
theorem singleFinalError_le_power
    (n gamma : Nat) (hlog : 1024 <= Nat.log 2 n)
    (hgamma : 1 <= gamma)
    (hsize : 6 * gamma * Nat.log 2 n <= n) :
    singleFinalError n gamma <=
      2 * (n : ENNReal)⁻¹ ^ ((1 / 64 : Real) * (gamma : Real)) := by
  let X : ENNReal :=
    (n : ENNReal)⁻¹ ^ ((1 / 64 : Real) * (gamma : Real))
  let E : ENNReal :=
    ENNReal.ofReal
      (Real.exp (-((gamma * Nat.log 2 n : Nat) : Real) / 16))
  have hE : E <= X := by
    dsimp only [E, X]
    exact singleFinal_exp_gamma_log_le_power n gamma
      (hlog.trans' (by norm_num))
  have hs : singleFinalSafetyTerm n gamma <= E := by
    dsimp only [E]
    exact singleFinalSafetyTerm_le_exp n gamma hlog hgamma hsize
  have hl : singleFinalLiveTerm n gamma <= E := by
    dsimp only [E]
    exact singleFinalLiveTerm_le_exp n gamma hlog hgamma hsize
  unfold singleFinalError
  calc
    singleFinalSafetyTerm n gamma + singleFinalLiveTerm n gamma
        <= E + E := add_le_add hs hl
    _ <= X + X := add_le_add hE hE
    _ = 2 * X := by ring

/-- Explicit two-stream final non-consensus bound from the late co-cap
checkpoint. -/
theorem singleFinal_noncons_mass_bound
    (n : Nat) (hn : 2 <= n) (gamma : Nat)
    (hboundary : 0 < singleFinalBoundary n)
    (s : SingleState n)
    (hs : SingleLateCheckpoint n (singleLateTargetCap n gamma) s) :
    (∑' z : SingleState n,
        if BiXConsensus n z.1 then 0
        else iter (singleStateStep n hn) (singleFinalHorizon n gamma) s z)
      <= singleFinalSafetyTerm n gamma + singleFinalLiveTerm n gamma := by
  let B := singleFinalBoundary n
  let T := singleFinalHorizon n gamma
  let Kf : SingleState n -> PMF (SingleState n) :=
    freeze (SingleFinalBad B) (singleStateStep n hn)
  let A : SingleState n -> Prop := fun z => BiXConsensus n z.1
  have hcoStart := singleLateCheckpoint_co_le s hs
  have hV0 :
      singleFinalV s <=
        singleFinalYBase ^ singleLateTargetCap n gamma :=
    singleFinalV_le_yBase_pow_coCap s hcoStart
  have hV0Safety :
      singleFinalV s <=
        singleFinalYBase ^ (singleLateTargetCap n gamma / 2 + 1) :=
    singleFinalV_le_yBase_pow_half_coCap s hcoStart
  have hdisj : ∀ z : SingleState n, A z -> ¬ SingleFinalBad B z := by
    intro z hA hz
    rcases z with ⟨⟨x, y, b⟩, hinv⟩
    simp only [A, BiXConsensus, SingleFinalBad, BiCfg.doubleCoLevel,
      BiCfg.DoubleInv] at hA hz hinv
    rcases hA with ⟨rfl, rfl, rfl⟩
    omega
  have hfreeze :=
    failure_le_failure_freeze
      (B := SingleFinalBad B) (A := A)
      (K := singleStateStep n hn) hdisj T s
  have hsplit :
      (∑' z : SingleState n, if A z then 0 else iter Kf T s z)
        <=
      (∑' z : SingleState n, if SingleFinalBad B z then
          iter Kf T s z else 0) +
        (∑' z : SingleState n, if SingleFinalLive B z then
          iter Kf T s z else 0) := by
    calc
      (∑' z : SingleState n, if A z then 0 else iter Kf T s z)
          <= ∑' z : SingleState n,
            ((if SingleFinalBad B z then iter Kf T s z else 0) +
              (if SingleFinalLive B z then iter Kf T s z else 0)) := by
            apply ENNReal.tsum_le_tsum
            intro z
            by_cases hA : A z
            · simp [hA]
            · by_cases hB : SingleFinalBad B z
              · simp [hA, hB]
              · have hlive : SingleFinalLive B z := ⟨hB, hA⟩
                simp [hA, hB, hlive]
      _ = (∑' z : SingleState n, if SingleFinalBad B z then
            iter Kf T s z else 0) +
          (∑' z : SingleState n, if SingleFinalLive B z then
            iter Kf T s z else 0) := by
            rw [ENNReal.tsum_add]
  have hbad :
      (∑' z : SingleState n, if SingleFinalBad B z then
          iter Kf T s z else 0)
        <= singleFinalYBase ^ (singleLateTargetCap n gamma / 2 + 1) /
          (singleFinalBlankBase ^ singleFinalBadThreshold n) := by
    have hθ0 : singleFinalBlankBase ^ singleFinalBadThreshold n ≠ 0 := by
      apply pow_ne_zero
      rw [singleFinalBlankBase]
      exact ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)
    have hθtop : singleFinalBlankBase ^ singleFinalBadThreshold n ≠ ⊤ :=
      ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hraw :=
      stopped_bad_mass_le Kf singleFinalV (SingleFinalBad B)
        (singleFinalBlankBase ^ singleFinalBadThreshold n) hθ0 hθtop
        (by
          intro z
          exact singleFinalV_step_super_stopped n hn z)
        (by
          intro z hz
          simpa [B] using singleFinalBad_potential_ge z hz)
        T s
    exact hraw.trans (ENNReal.div_le_div_right hV0Safety _)
  have hlive :
      (∑' z : SingleState n, if SingleFinalLive B z then
          iter Kf T s z else 0)
        <= singleFinalPhi n ^ T *
          singleFinalYBase ^ singleLateTargetCap n gamma := by
    have hθ0 : (1 : ENNReal) ≠ 0 := by norm_num
    have hθtop : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
    have hmarkov :=
      bad_mass_le_expect_div (iter Kf T s)
        (singleFinalMaskedV B) (SingleFinalLive B)
        1 hθ0 hθtop
        (by
          intro z hz
          rcases hz with ⟨hzB, hzA⟩
          unfold singleFinalMaskedV
          simp [hzB, hzA, one_le_singleFinalV z])
    have hiter :=
      expect_iter_le Kf (singleFinalMaskedV B) (singleFinalPhi n)
        (by
          intro z
          simpa [Kf, B] using singleFinalMaskedV_step_contract n hn z)
        T s
    calc
      (∑' z : SingleState n, if SingleFinalLive B z then
          iter Kf T s z else 0)
          <= expect (iter Kf T s) (singleFinalMaskedV B) / 1 := hmarkov
      _ <= (singleFinalPhi n ^ T * singleFinalMaskedV B s) / 1 := by
        exact ENNReal.div_le_div_right hiter _
      _ = singleFinalPhi n ^ T * singleFinalMaskedV B s := by simp
      _ <= singleFinalPhi n ^ T *
            singleFinalYBase ^ singleLateTargetCap n gamma := by
        exact mul_le_mul_left'
          ((singleFinalMaskedV_le B s).trans hV0) _
  calc
    (∑' z : SingleState n,
        if BiXConsensus n z.1 then 0
        else iter (singleStateStep n hn) T s z)
        <= ∑' z : SingleState n, if A z then 0 else iter Kf T s z := hfreeze
    _ <= (∑' z : SingleState n, if SingleFinalBad B z then
          iter Kf T s z else 0) +
        (∑' z : SingleState n, if SingleFinalLive B z then
          iter Kf T s z else 0) := hsplit
    _ <= singleFinalYBase ^ (singleLateTargetCap n gamma / 2 + 1) /
          (singleFinalBlankBase ^ singleFinalBadThreshold n) +
        singleFinalPhi n ^ T *
          singleFinalYBase ^ singleLateTargetCap n gamma := by
      exact add_le_add hbad hlive
    _ = singleFinalSafetyTerm n gamma + singleFinalLiveTerm n gamma := by
      simp [singleFinalSafetyTerm, singleFinalLiveTerm, B, T]

/-- Explicit-error final consensus block from the late co-level checkpoint. -/
theorem singleFinalConsensus_reaches_raw
    (n : Nat) (hn : 2 <= n) (gamma : Nat)
    (hlog : 128 <= Nat.log 2 n) :
    Reaches (singleStateStep n hn) (singleFinalHorizon n gamma)
      (SingleLateCheckpoint n (singleLateTargetCap n gamma))
      (fun s : SingleState n => BiXConsensus n s.1)
      (singleFinalError n gamma) := by
  have hnLarge : 4096 <= n :=
    phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
  intro s hs
  have hboundary : 0 < singleFinalBoundary n := by
    unfold singleFinalBoundary
    omega
  simpa [singleFinalError] using
    singleFinal_noncons_mass_bound n hn gamma hboundary s hs

/-- Power-law form of the final physical consensus block. -/
theorem singleFinalConsensus_reaches_power
    (n : Nat) (hn : 2 <= n) (gamma : Nat)
    (hlog : 1024 <= Nat.log 2 n) (hgamma : 1 <= gamma)
    (hsize : 6 * gamma * Nat.log 2 n <= n) :
    Reaches (singleStateStep n hn) (singleFinalHorizon n gamma)
      (SingleLateCheckpoint n (singleLateTargetCap n gamma))
      (fun s : SingleState n => BiXConsensus n s.1)
      (2 * (n : ENNReal)⁻¹ ^
        ((1 / 64 : Real) * (gamma : Real))) := by
  apply (singleFinalConsensus_reaches_raw n hn gamma
    (hlog.trans' (by norm_num))).mono_error
  exact singleFinalError_le_power n gamma hlog hgamma hsize

/-- On the Single-B invariant subtype, co-level zero is exactly all-`X`
consensus. -/
theorem single_coLevel_eq_zero_iff_biXConsensus {n : Nat}
    (s : SingleState n) :
    s.1.doubleCoLevel = 0 ↔ BiXConsensus n s.1 := by
  rcases s with ⟨⟨x, y, b⟩, hinv⟩
  simp only [BiCfg.doubleCoLevel, BiCfg.DoubleInv, BiXConsensus] at hinv ⊢
  omega

/-- Non-consensus is equivalently positive co-level. -/
theorem single_nonconsensus_iff_coLevel_pos {n : Nat}
    (s : SingleState n) :
    ¬ BiXConsensus n s.1 ↔ 0 < s.1.doubleCoLevel := by
  rw [← single_coLevel_eq_zero_iff_biXConsensus s]
  omega

/-- The public zero co-cap checkpoint is exactly all-`X` consensus. -/
theorem singleLateCheckpoint_zero_iff_biXConsensus {n : Nat}
    (s : SingleState n) :
    SingleLateCheckpoint n 0 s ↔ BiXConsensus n s.1 := by
  rcases s with ⟨⟨x, y, b⟩, hinv⟩
  simp only [SingleLateCheckpoint, BiCfg.doubleLevel, BiCfg.DoubleInv,
    BiXConsensus, Nat.add_zero] at hinv ⊢
  omega

/-- The subtype and raw Single-B consensus predicates agree. -/
theorem doubleXConsensus_iff_biXConsensus {n : Nat} (s : SingleState n) :
    DoubleXConsensus s ↔ BiXConsensus n s.1 := by
  rfl

/-- All-`X` consensus is absorbing for the Single-B state kernel, stated with
the raw `BiXConsensus` predicate used by Theorem 2. -/
theorem singleStateStep_biXConsensus
    (n : Nat) (hn : 2 <= n) (s : SingleState n)
    (hs : BiXConsensus n s.1) :
    singleStateStep n hn s = PMF.pure s := by
  exact singleStateStep_consensusX n hn s
    ((doubleXConsensus_iff_biXConsensus s).2 hs)

/-- All-`X` consensus is absorbing for the raw Single-B chain. -/
theorem singleBChain_consensusX (n : Nat) (hn : 2 <= n) :
    singleBChain ⟨n, 0, 0⟩ = PMF.pure ⟨n, 0, 0⟩ := by
  let s : SingleState n := ⟨⟨n, 0, 0⟩, by
    simp only [BiCfg.DoubleInv]
    omega⟩
  have hmap := singleStateStep_map_val n hn s
  have hstep :
      singleStateStep n hn s = PMF.pure s := by
    apply singleStateStep_biXConsensus n hn s
    exact ⟨rfl, rfl, rfl⟩
  rw [hstep, PMF.pure_map] at hmap
  simpa only [s] using hmap.symm

/-- Formal obstruction to closing the final block by setting the existing
level-form structural rung's exit to `2*n`.  Its side conditions then force
all positive analytic budgets to be zero, so the corrected-level route cannot
produce an exponential final block. -/
theorem singleFinal_level_top_side_conditions_force_zero_budgets
    {n Lexit hiΛ D M c : Nat}
    (hLexit : Lexit = 2 * n)
    (htargetHi : Lexit + D + 1 <= hiΛ)
    (hcoClock : hiΛ + 2 * M + 2 * c <= 2 * n + 1) :
    D = 0 ∧ M = 0 ∧ c = 0 := by
  omega

end Tri

#print axioms Tri.singleFinalScale
#print axioms Tri.singleFinalResolutions
#print axioms Tri.singleFinalHorizon
#print axioms Tri.single_coLevel_eq_zero_iff_biXConsensus
#print axioms Tri.single_nonconsensus_iff_coLevel_pos
#print axioms Tri.singleLateCheckpoint_zero_iff_biXConsensus
#print axioms Tri.doubleXConsensus_iff_biXConsensus
#print axioms Tri.singleStateStep_biXConsensus
#print axioms Tri.singleBChain_consensusX
#print axioms Tri.singleFinal_level_top_side_conditions_force_zero_budgets

/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBClockTrace
import Tri.MaskedCounting

/-!
# The normal/free-Y branch of the Single-B occupation clock

On a normal tick (`n ≤ 16y`), the masked fuel labels are the two fair
creations and the `Y`-resolution.  Their doubled raw weight is
`xy + xy + 2yb = 2·y·(x+b)`, so over the doubled scheduler denominator
`2·C(n,2)` the factor two cancels and the mass is `y·(x+b)/C(n,2)` — exactly
the Double-B/Heavy-B shape.  The `1/16` floor therefore survives the doubled
scheduler unchanged; the level floor `n ≤ 2x+b` is supplied by the live band
through the repaired guard (`¬lower`, `¬CreationBadY`, `¬boundary` give
`doubleLevel ≥ aLoΛ+1−D ≥ n`).
-/

namespace Tri

open scoped ENNReal

/-- Total population of a Single-B ledger state is at least two. -/
theorem single_two_entities {n : ℕ} (hn : 2 ≤ n) (q : SingleLedger n) :
    2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b := by
  have h := q.cfg.2
  simp only [BiCfg.DoubleInv] at h
  omega

/-- Normal-branch masked fuel mass, with the ambient denominator `C(n,2)`. -/
noncomputable def singleNormalFuelMass {n : ℕ} (q : SingleLedger n) : ℝ≥0∞ :=
  ((q.cfg.1.y * (q.cfg.1.x + q.cfg.1.b) : ℕ) : ℝ≥0∞) /
    ((Nat.choose n 2 : ℕ) : ℝ≥0∞)

/-- The three masked-fuel event masses aggregate to `y·(x+b)/C(n,2)`: the
doubled factor cancels against the doubled scheduler denominator. -/
theorem singleCompPMF_normalFuel_mass {n : ℕ} (q : SingleLedger n)
    (h : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b) :
    singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .xyToX
        + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .xyToY
        + singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b h .yb
      = singleNormalFuelMass q := by
  have hpop : q.cfg.1.x + q.cfg.1.y + q.cfg.1.b = n := q.cfg.2
  unfold singleNormalFuelMass
  simp only [singleCompPMF_apply, SingleComp.weight]
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, hpop]
  rw [show ((q.cfg.1.x * q.cfg.1.y : ℕ) : ℝ≥0∞)
        + ((q.cfg.1.x * q.cfg.1.y : ℕ) : ℝ≥0∞)
        + ((2 * q.cfg.1.y * q.cfg.1.b : ℕ) : ℝ≥0∞)
      = 2 * ((q.cfg.1.y * (q.cfg.1.x + q.cfg.1.b) : ℕ) : ℝ≥0∞) by
    push_cast
    ring]
  exact ennreal_two_mul_div_two_mul
    ((q.cfg.1.y * (q.cfg.1.x + q.cfg.1.b) : ℕ) : ℝ≥0∞)
    ((Nat.choose n 2 : ℕ) : ℝ≥0∞)

/-- Normal-fuel cross bound over the ambient denominator. -/
theorem singleB_normalFuel_cross {n x y b : ℕ}
    (_hinv : x + y + b = n)
    (hlevel : n ≤ 2 * x + b)
    (hnormal : n ≤ 16 * y) :
    Nat.choose n 2 ≤ 16 * (y * (x + b)) := by
  have hmul : n * n ≤ (16 * y) * (2 * x + b) :=
    Nat.mul_le_mul hnormal hlevel
  have hchoose := two_mul_choose_two n
  have hsub : n * (n - 1) ≤ n * n :=
    Nat.mul_le_mul_left n (Nat.sub_le n 1)
  nlinarith

/-- On a live state of the repaired stopped band with `n + D ≤ aLoΛ + 1`, the
physical doubled level is at least `n`. -/
theorem singleClock_live_level_floor {n aLoΛ hiΛ D H : ℕ}
    (q : SingleLedger n)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q)
    (hfloor : n + D ≤ aLoΛ + 1) :
    n ≤ q.cfg.1.doubleLevel := by
  have hnotLow : ¬ (q.cfg.1.doubleLevel + q.cy ≤ aLoΛ + q.cx) :=
    fun h => hlive (Or.inl h)
  have hnotBad : ¬ CreationBadY D H q :=
    fun h => hlive (Or.inr (Or.inr (Or.inl h)))
  have hnotBoundary : ¬ singleCreationBoundary H q :=
    fun h => hlive (Or.inr (Or.inr (Or.inr h)))
  have hbudget : q.cx + q.cy ≤ H := by
    unfold singleCreationBoundary at hnotBoundary
    omega
  have hbal : q.cy ≤ q.cx + D := by
    by_contra hbal
    exact hnotBad ⟨hbudget, by omega⟩
  omega

/-- On a live normal tick, the masked fuel mass is at least `1/16` — the
honest constant survives the doubled scheduler because the doubled fuel weight
cancels the doubled denominator. -/
theorem singleNormalFuelMass_ge_sixteenth {n aLoΛ hiΛ D H : ℕ}
    (hn : 2 ≤ n) (q : SingleLedger n)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q)
    (hnormal : q.NormalTick)
    (hfloor : n + D ≤ aLoΛ + 1) :
    (1 : ℝ≥0∞) / 16 ≤ singleNormalFuelMass q := by
  have hlevel := singleClock_live_level_floor q hlive hfloor
  simp only [BiCfg.doubleLevel] at hlevel
  unfold SingleLedger.NormalTick at hnormal
  have hcross :
      Nat.choose n 2 ≤ 16 * (q.cfg.1.y * (q.cfg.1.x + q.cfg.1.b)) :=
    singleB_normalFuel_cross q.cfg.2 hlevel hnormal
  unfold singleNormalFuelMass
  have hden0 : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  have hdenTop : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)).2
  calc
    (1 : ℝ≥0∞) / 16 * ((Nat.choose n 2 : ℕ) : ℝ≥0∞)
        = ((Nat.choose n 2 : ℕ) : ℝ≥0∞) / 16 := by
          simp only [div_eq_mul_inv]
          ac_rfl
    _ ≤ ((q.cfg.1.y * (q.cfg.1.x + q.cfg.1.b) : ℕ) : ℝ≥0∞) := by
          apply ENNReal.div_le_of_le_mul
          exact_mod_cast
            (by simpa [mul_comm, mul_left_comm, mul_assoc] using hcross)

/-- The expectation of any clock potential over one live stopped-clock step,
pushed onto the seven-event alphabet with an arbitrary entity witness. -/
theorem expect_singleClockBandStep_live
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ) (q : SingleClockTrace n)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q.core)
    (W : SingleClockTrace n → ℝ≥0∞)
    (h2 : 2 ≤ q.core.cfg.1.x + q.core.cfg.1.y + q.core.cfg.1.b) :
    expect (singleClockBandStep n hn aLoΛ hiΛ D H q) W
      = ∑ k : SingleComp,
          singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 k
            * W (SingleComp.nextSingleClockTrace q k) := by
  unfold singleClockBandStep
  rw [if_neg hlive, expect_map, expect_fintype]

/-- Exact masked-potential expansion at a live normal tick. -/
theorem singleClockBandStep_expect_normal
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (q : SingleClockTrace n) (η w : ℝ≥0∞)
    (h2 : 2 ≤ q.core.cfg.1.x + q.core.cfg.1.y + q.core.cfg.1.b)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q.core)
    (hnormal : q.core.NormalTick) :
    expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
        (maskedCountPotential SingleClockTrace.normalTicks
          SingleClockTrace.normalFuel η w) =
      (singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 .xx
          + singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 .yy
          + singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 .bb
          + singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 .xb)
          * (η ^ (q.normalTicks + 1) * w ^ q.normalFuel)
        + singleNormalFuelMass q.core
          * (η ^ (q.normalTicks + 1) * w ^ (q.normalFuel + 1)) := by
  have key : ∀ k : SingleComp,
      singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 k *
          maskedCountPotential SingleClockTrace.normalTicks
            SingleClockTrace.normalFuel η w
            (SingleComp.nextSingleClockTrace q k) =
        singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 k *
          (η ^ (q.normalTicks + 1) *
            w ^ (q.normalFuel + k.singleNormalFuelInc)) := by
    intro k
    by_cases hw :
        SingleComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
    · rw [singleCompPMF_zero_of_weight_zero hw]
      simp
    · unfold SingleComp.nextSingleClockTrace
      rw [dif_neg hw]
      simp only [maskedCountPotential, hnormal, if_true]
  rw [expect_singleClockBandStep_live n hn aLoΛ hiΛ D H q hlive _ h2]
  rw [show (Finset.univ : Finset SingleComp) =
      {SingleComp.xx, SingleComp.xyToX, SingleComp.xyToY, SingleComp.yy,
        SingleComp.xb, SingleComp.yb, SingleComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [key .xx, key .xyToX, key .xyToY, key .yy, key .xb, key .yb, key .bb]
  rw [← singleCompPMF_normalFuel_mass q.core h2]
  simp only [SingleComp.singleNormalFuelInc]
  ring

/-- At a live complementary tick the normal masked potential is unchanged in
expectation. -/
theorem singleClockBandStep_expect_not_normal
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (q : SingleClockTrace n) (η w : ℝ≥0∞)
    (hlive : ¬ SingleBandFrozen n aLoΛ hiΛ D H q.core)
    (hnormal : ¬ q.core.NormalTick) :
    expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
        (maskedCountPotential SingleClockTrace.normalTicks
          SingleClockTrace.normalFuel η w) =
      maskedCountPotential SingleClockTrace.normalTicks
        SingleClockTrace.normalFuel η w q := by
  have h2 := single_two_entities hn q.core
  have key : ∀ k : SingleComp,
      singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 k *
          maskedCountPotential SingleClockTrace.normalTicks
            SingleClockTrace.normalFuel η w
            (SingleComp.nextSingleClockTrace q k) =
        singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 k *
          maskedCountPotential SingleClockTrace.normalTicks
            SingleClockTrace.normalFuel η w q := by
    intro k
    by_cases hw :
        SingleComp.weight q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b k = 0
    · rw [singleCompPMF_zero_of_weight_zero hw]
      simp
    · unfold SingleComp.nextSingleClockTrace
      rw [dif_neg hw]
      simp only [maskedCountPotential, hnormal, if_false, add_zero]
  rw [expect_singleClockBandStep_live n hn aLoΛ hiΛ D H q hlive _ h2]
  rw [show (Finset.univ : Finset SingleComp) =
      {SingleComp.xx, SingleComp.xyToX, SingleComp.xyToY, SingleComp.yy,
        SingleComp.xb, SingleComp.yb, SingleComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [key .xx, key .xyToX, key .xyToY, key .yy, key .xb, key .yb, key .bb]
  have hsum := singleCompPMF_sum_seven
    q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2
  conv_rhs =>
    rw [← one_mul
      (maskedCountPotential SingleClockTrace.normalTicks
        SingleClockTrace.normalFuel η w q), ← hsum]
  ring

/-- The normal masked potential is a one-step supermartingale throughout the
repaired stopped Single-B band with gap floor `n + D ≤ aLoΛ + 1`. -/
theorem singleClockBandStep_normal_super
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (hfloor : n + D ≤ aLoΛ + 1) (η w : ℝ≥0∞)
    (hw1 : w ≤ 1)
    (hfactor :
      η * ((15 : ℝ≥0∞) / 16 + (1 / 16) * w) ≤ 1) :
    ∀ q : SingleClockTrace n,
      expect (singleClockBandStep n hn aLoΛ hiΛ D H q)
          (maskedCountPotential SingleClockTrace.normalTicks
            SingleClockTrace.normalFuel η w) ≤
        maskedCountPotential SingleClockTrace.normalTicks
          SingleClockTrace.normalFuel η w q := by
  intro q
  by_cases hlive : SingleBandFrozen n aLoΛ hiΛ D H q.core
  · unfold singleClockBandStep
    rw [if_pos hlive, expect_pure]
  · by_cases hnormal : q.core.NormalTick
    · have h2 := single_two_entities hn q.core
      rw [singleClockBandStep_expect_normal n hn aLoΛ hiΛ D H q η w
        h2 hlive hnormal]
      set idle :=
        singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 .xx
          + singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 .yy
          + singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 .bb
          + singleCompPMF q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2 .xb
        with hidle
      have hm : singleNormalFuelMass q.core + idle = 1 := by
        rw [hidle, ← singleCompPMF_normalFuel_mass q.core h2]
        have hsum := singleCompPMF_sum_seven
          q.core.cfg.1.x q.core.cfg.1.y q.core.cfg.1.b h2
        rw [← hsum]
        ring
      have hq :
          (1 : ℝ≥0∞) / 16 ≤ singleNormalFuelMass q.core :=
        singleNormalFuelMass_ge_sixteenth hn q.core hlive hnormal hfloor
      have hp : (1 : ℝ≥0∞) / 16 + 15 / 16 = 1 := by
        rw [ENNReal.div_add_div_same]
        have hnum : (1 : ℝ≥0∞) + 15 = 16 := by norm_num
        rw [hnum]
        exact ENNReal.div_self
          (by norm_num : (16 : ℝ≥0∞) ≠ 0)
          (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)
      have hscalar :
          idle + singleNormalFuelMass q.core * w ≤
            15 / 16 + (1 / 16 : ℝ≥0∞) * w :=
        step_factor_antitone_ennreal hp hm hw1 hq
      calc
        idle * (η ^ (q.normalTicks + 1) * w ^ q.normalFuel) +
            singleNormalFuelMass q.core *
              (η ^ (q.normalTicks + 1) * w ^ (q.normalFuel + 1))
            = η * (idle + singleNormalFuelMass q.core * w) *
                maskedCountPotential SingleClockTrace.normalTicks
                  SingleClockTrace.normalFuel η w q := by
                    unfold maskedCountPotential
                    rw [pow_succ η q.normalTicks, pow_succ w q.normalFuel]
                    ring
        _ ≤ η * (15 / 16 + (1 / 16 : ℝ≥0∞) * w) *
              maskedCountPotential SingleClockTrace.normalTicks
                SingleClockTrace.normalFuel η w q := by
          gcongr
        _ ≤ 1 * maskedCountPotential SingleClockTrace.normalTicks
              SingleClockTrace.normalFuel η w q := by
          gcongr
        _ = maskedCountPotential SingleClockTrace.normalTicks
              SingleClockTrace.normalFuel η w q := one_mul _
    · rw [singleClockBandStep_expect_not_normal n hn aLoΛ hiΛ D H q η w
        hlive hnormal]

/-- Finite-horizon lower tail for the number of masked-fuel labels observed on
normal ticks of the stopped Single-B band. -/
theorem singleClock_normal_tail
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (hfloor : n + D ≤ aLoΛ + 1) (η w : ℝ≥0∞)
    (hη1 : 1 ≤ η) (hηtop : η ≠ ⊤)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hfactor :
      η * ((15 : ℝ≥0∞) / 16 + (1 / 16) * w) ≤ 1)
    (T Hocc m : ℕ) (q₀ : SingleClockTrace n) :
    ∑' z, (if Hocc ≤ z.normalTicks ∧ z.normalFuel ≤ m then
        iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) ≤
      maskedCountPotential SingleClockTrace.normalTicks
          SingleClockTrace.normalFuel η w q₀ /
        (η ^ Hocc * w ^ m) := by
  exact masked_count_tail
    (singleClockBandStep n hn aLoΛ hiΛ D H)
    SingleClockTrace.normalTicks SingleClockTrace.normalFuel
    η w hη1 hηtop hw1 hw0
    (singleClockBandStep_normal_super n hn aLoΛ hiΛ D H hfloor η w hw1 hfactor)
    T Hocc m q₀

/-- The concrete `w = 1/2`, `η = 32/31` normal-tail specialization. -/
theorem singleClock_normal_tail_half
    (n : ℕ) (hn : 2 ≤ n) (aLoΛ hiΛ D H : ℕ)
    (hfloor : n + D ≤ aLoΛ + 1)
    (T Hocc m : ℕ) (q₀ : SingleClockTrace n) :
    ∑' z, (if Hocc ≤ z.normalTicks ∧ z.normalFuel ≤ m then
        iter (singleClockBandStep n hn aLoΛ hiΛ D H) T q₀ z else 0) ≤
      maskedCountPotential SingleClockTrace.normalTicks
          SingleClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) q₀ /
        (((32 : ℝ≥0∞) / 31) ^ Hocc * (1 / 2) ^ m) := by
  apply singleClock_normal_tail n hn aLoΛ hiΛ D H hfloor
      ((32 : ℝ≥0∞) / 31) (1 / 2)
  · rw [← ENNReal.toReal_le_toReal (by norm_num)
        (ENNReal.div_ne_top (by norm_num) (by norm_num))]
    norm_num
  · exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  · norm_num
  · norm_num
  · rw [← ENNReal.toReal_le_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num

section Inhabitation

example :
    ∀ q : SingleClockTrace 160,
      expect (singleClockBandStep 160 (by norm_num) 166 168 5 20737 q)
          (maskedCountPotential SingleClockTrace.normalTicks
            SingleClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2)) ≤
        maskedCountPotential SingleClockTrace.normalTicks
          SingleClockTrace.normalFuel ((32 : ℝ≥0∞) / 31) (1 / 2) q := by
  apply singleClockBandStep_normal_super
  · norm_num
  · norm_num
  · rw [← ENNReal.toReal_le_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num

example :
    (1 : ℝ≥0∞) / 16 ≤ singleNormalFuelMass
      (⟨⟨⟨17, 10, 133⟩, by norm_num [BiCfg.DoubleInv]⟩, 0, 0, 0, 0⟩ :
        SingleLedger 160) := by
  apply singleNormalFuelMass_ge_sixteenth
    (aLoΛ := 166) (hiΛ := 168) (D := 5) (H := 20737)
  · norm_num
  · norm_num [SingleBandFrozen, BiCfg.doubleLevel, CreationBadY,
      singleCreationBoundary]
  · norm_num [SingleLedger.NormalTick]
  · norm_num

end Inhabitation

end Tri

#print axioms Tri.singleCompPMF_normalFuel_mass
#print axioms Tri.singleB_normalFuel_cross
#print axioms Tri.singleClock_live_level_floor
#print axioms Tri.singleNormalFuelMass_ge_sixteenth
#print axioms Tri.singleClockBandStep_normal_super
#print axioms Tri.singleClock_normal_tail
#print axioms Tri.singleClock_normal_tail_half

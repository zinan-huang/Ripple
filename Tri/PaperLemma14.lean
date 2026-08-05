/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma15Prefix
import Tri.SameHorizon

/-!
# Paper Lemma 14: sampling without replacement

The urn state stores the remaining red and blue populations.  After `s`
reveals, with `u + s + 1 = R + B`, the selected-red deviation divided by
`u+1` is exactly the change in the remaining red fraction.  The theorem below
gives the two-sided finite-population tail, followed by the paper's simpler
Hoeffding-scale envelope.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The good event for a fixed without-replacement sample, expressed through
the remaining red fraction. -/
def Lemma14UrnGood
    (c₀ δ : ℝ) (z : ℕ × ℕ) : Prop :=
  |urnM c₀ z| ≤ δ

noncomputable instance lemma14UrnGoodDecidable
    (c₀ δ : ℝ) :
    DecidablePred (Lemma14UrnGood c₀ δ) :=
  Classical.decPred _

/-- The paper's event, stated directly in terms of the number of selected red
balls.  Integer subtraction records the selected count without truncated
natural subtraction. -/
def Lemma14SelectedGood
    (R B s : ℕ) (D : ℝ) (z : ℕ × ℕ) : Prop :=
  |((((R : ℤ) - (z.1 : ℤ)) : ℤ) : ℝ) -
      (s : ℝ) * (R : ℝ) / ((R : ℝ) + (B : ℝ))| ≤ D

noncomputable instance lemma14SelectedGoodDecidable
    (R B s : ℕ) (D : ℝ) :
    DecidablePred (Lemma14SelectedGood R B s D) :=
  Classical.decPred _

/-- On a supported endpoint, selected-red deviation is the remaining-red
fraction deviation multiplied by the remaining population. -/
theorem lemma14_selected_deviation_eq
    (s u R B : ℕ) (z : ℕ × ℕ)
    (hclock : u + s + 1 = R + B)
    (htotal : z.1 + z.2 = u + 1) :
    ((((R : ℤ) - (z.1 : ℤ)) : ℤ) : ℝ) -
        (s : ℝ) * (R : ℝ) / ((R : ℝ) + (B : ℝ)) =
      ((u : ℝ) + 1) *
        urnM
          ((R : ℝ) / ((R : ℝ) + (B : ℝ))) z := by
  have hnu :
      (R : ℝ) + (B : ℝ) =
        (u : ℝ) + (s : ℝ) + 1 := by
    exact_mod_cast hclock.symm
  have hrem :
      (z.1 : ℝ) + (z.2 : ℝ) = (u : ℝ) + 1 := by
    exact_mod_cast htotal
  have hnuPos : (0 : ℝ) < (R : ℝ) + (B : ℝ) := by
    rw [hnu]
    positivity
  have hremPos : (0 : ℝ) < (z.1 : ℝ) + (z.2 : ℝ) := by
    rw [hrem]
    positivity
  unfold urnM
  push_cast
  rw [hnu, hrem]
  field_simp
  ring

/-- The fraction-deviation event implies the paper's selected-count event on
every supported endpoint. -/
theorem lemma14_urn_good_implies_selected_good
    (D : ℝ) (s u R B : ℕ) (z : ℕ × ℕ)
    (hclock : u + s + 1 = R + B)
    (htotal : z.1 + z.2 = u + 1)
    (hgood :
      Lemma14UrnGood
        ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
        (D / ((u : ℝ) + 1)) z) :
    Lemma14SelectedGood R B s D z := by
  unfold Lemma14SelectedGood
  rw [lemma14_selected_deviation_eq s u R B z hclock htotal,
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (u : ℝ) + 1)]
  unfold Lemma14UrnGood at hgood
  calc
    ((u : ℝ) + 1) *
        |urnM
          ((R : ℝ) / ((R : ℝ) + (B : ℝ))) z|
        ≤ ((u : ℝ) + 1) * (D / ((u : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hgood (by positivity)
    _ = D := by field_simp

/-- Exact two-sided fixed-sample tail, including the finite-population
correction.  The variance budget is stated subtraction-free using
`u + s + 1 = R + B`. -/
theorem lemma14_without_replacement_exact
    (δ : ℝ) (s u R B : ℕ)
    (hδ : 0 < δ)
    (hs : 0 < s)
    (hclock : u + s + 1 = R + B) :
    terminalFailureMass
        (iter urnStopped s (R, B))
        (Lemma14UrnGood
          ((R : ℝ) / ((R : ℝ) + (B : ℝ))) δ)
      ≤
    2 * ENNReal.ofReal
      (Real.exp
        (-(2 * δ ^ 2 /
          (2 * (s : ℝ) /
            (((u : ℝ) + 1) *
              ((R : ℝ) + (B : ℝ))))))) := by
  let c₀ : ℝ :=
    (R : ℝ) / ((R : ℝ) + (B : ℝ))
  let A : ℝ :=
    2 * (s : ℝ) /
      (((u : ℝ) + 1) * ((R : ℝ) + (B : ℝ)))
  let lam : ℝ := 4 * δ / A
  let ε : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-(2 * δ ^ 2 / A)))
  let PosBad : ℕ × ℕ → Prop :=
    UrnWindowBad c₀ δ lam u
  let NegBad : ℕ × ℕ → Prop :=
    UrnWindowBad c₀ δ (-lam) u
  let μ := iter urnStopped s (R, B)
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by
    positivity
  have hRB : (0 : ℝ) < (R : ℝ) + (B : ℝ) := by
    have hpos : 0 < R + B := by
      omega
    exact_mod_cast hpos
  have hsR : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast hs
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hlam : 0 < lam := by
    dsimp only [lam]
    positivity
  have hbudget :
      urnA (R + B - 1) ≤ A + urnA u := by
    simpa [A] using
      urn_telescope_budget u s R B hclock
  have hPosHit :
      (⨆ T : ℕ, hitProb PosBad urnStopped T (R, B)) ≤ ε := by
    simpa [PosBad, c₀, lam, ε] using
      urn_window_tail δ A u R B hA hδ.le hbudget
  have hNegHit :
      (⨆ T : ℕ, hitProb NegBad urnStopped T (R, B)) ≤ ε := by
    simpa [NegBad, c₀, lam, ε] using
      urn_window_tail_neg δ A u R B hA hδ.le hbudget
  have hPosTerminal :
      terminalFailureMass μ (fun z => ¬ PosBad z) ≤ ε := by
    calc
      terminalFailureMass μ (fun z => ¬ PosBad z)
          ≤ hitProb PosBad urnStopped s (R, B) := by
            simpa [μ] using
              terminalEventMass_iter_le_hitProb
                PosBad urnStopped s (R, B)
      _ ≤ ⨆ T : ℕ,
          hitProb PosBad urnStopped T (R, B) :=
        le_iSup (fun T =>
          hitProb PosBad urnStopped T (R, B)) s
      _ ≤ ε := hPosHit
  have hNegTerminal :
      terminalFailureMass μ (fun z => ¬ NegBad z) ≤ ε := by
    calc
      terminalFailureMass μ (fun z => ¬ NegBad z)
          ≤ hitProb NegBad urnStopped s (R, B) := by
            simpa [μ] using
              terminalEventMass_iter_le_hitProb
                NegBad urnStopped s (R, B)
      _ ≤ ⨆ T : ℕ,
          hitProb NegBad urnStopped T (R, B) :=
        le_iSup (fun T =>
          hitProb NegBad urnStopped T (R, B)) s
      _ ≤ ε := hNegHit
  have hpoint :
      ∀ z,
        (if Lemma14UrnGood c₀ δ z then 0 else μ z) ≤
          (if PosBad z then μ z else 0) +
            (if NegBad z then μ z else 0) := by
    intro z
    by_cases hzμ : μ z = 0
    · simp [hzμ]
    have htotal :=
      urnStopped_iter_total s (R, B) z
        (by omega) (by simpa [μ] using hzμ)
    have hleft :
        (if Lemma14UrnGood c₀ δ z then
            0
          else μ z) ≤ μ z := by
      by_cases hgood :
          Lemma14UrnGood c₀ δ z <;>
        simp [hgood]
    by_cases hgood : Lemma14UrnGood c₀ δ z
    · simp [hgood]
    · have habs :
          δ < |urnM c₀ z| := by
        unfold Lemma14UrnGood at hgood
        exact lt_of_not_ge hgood
      by_cases hM : 0 ≤ urnM c₀ z
      · have hdev : δ ≤ urnM c₀ z := by
          rw [abs_of_nonneg hM] at habs
          exact habs.le
        have hPos : PosBad z := by
          refine ⟨by omega, ?_⟩
          dsimp only [PosBad]
          rw [abs_of_pos hlam]
          exact mul_le_mul_of_nonneg_left hdev hlam.le
        exact hleft.trans (by simp [hPos])
      · have hMneg : urnM c₀ z < 0 := lt_of_not_ge hM
        have hdev : δ ≤ -urnM c₀ z := by
          rw [abs_of_neg hMneg] at habs
          exact habs.le
        have hNeg : NegBad z := by
          refine ⟨by omega, ?_⟩
          dsimp only [NegBad]
          rw [abs_neg, abs_of_pos hlam]
          nlinarith
        exact hleft.trans (by simp [hNeg])
  unfold terminalFailureMass
  calc
    (∑' z, if Lemma14UrnGood
          ((R : ℝ) / ((R : ℝ) + (B : ℝ))) δ z
        then 0 else (iter urnStopped s (R, B)) z)
        ≤ ∑' z,
            ((if PosBad z then μ z else 0) +
              (if NegBad z then μ z else 0)) := by
          simpa [c₀, μ] using
            ENNReal.tsum_le_tsum hpoint
    _ =
      (∑' z, if PosBad z then μ z else 0) +
        (∑' z, if NegBad z then μ z else 0) :=
      ENNReal.tsum_add
    _ ≤ ε + ε := by
      exact add_le_add
        (by simpa [terminalFailureMass] using hPosTerminal)
        (by simpa [terminalFailureMass] using hNegTerminal)
    _ = 2 * ε := by ring
    _ = 2 * ENNReal.ofReal
        (Real.exp
          (-(2 * δ ^ 2 /
            (2 * (s : ℝ) /
              (((u : ℝ) + 1) *
                ((R : ℝ) + (B : ℝ))))))) := by
      rfl

/-- Threshold form for the equivalent remaining-red fraction event. -/
theorem lemma14_fraction
    (L D : ℝ) (s u R B : ℕ)
    (hD : 0 < D)
    (hs : 0 < s)
    (hclock : u + s + 1 = R + B)
    (hscale : L * (s : ℝ) ≤ D ^ 2) :
    terminalFailureMass
        (iter urnStopped s (R, B))
        (Lemma14UrnGood
          ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
          (D / ((u : ℝ) + 1)))
      ≤
    2 * ENNReal.ofReal (Real.exp (-L)) := by
  let δ : ℝ := D / ((u : ℝ) + 1)
  let A : ℝ :=
    2 * (s : ℝ) /
      (((u : ℝ) + 1) * ((R : ℝ) + (B : ℝ)))
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by
    positivity
  have hRB : (0 : ℝ) < (R : ℝ) + (B : ℝ) := by
    have hpos : 0 < R + B := by
      omega
    exact_mod_cast hpos
  have hsR : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast hs
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hrate :
      L ≤ 2 * δ ^ 2 / A := by
    dsimp only [δ, A]
    have hnu :
        (R : ℝ) + (B : ℝ) =
          (u : ℝ) + (s : ℝ) + 1 := by
      exact_mod_cast hclock.symm
    have hrateEq :
        2 * (D / ((u : ℝ) + 1)) ^ 2 /
            (2 * (s : ℝ) /
              (((u : ℝ) + 1) *
                ((R : ℝ) + (B : ℝ)))) =
          D ^ 2 * ((R : ℝ) + (B : ℝ)) /
            ((s : ℝ) * ((u : ℝ) + 1)) := by
      field_simp
    rw [hrateEq, le_div_iff₀ (mul_pos hsR hu1)]
    calc
      L * ((s : ℝ) * ((u : ℝ) + 1))
          = (L * (s : ℝ)) * ((u : ℝ) + 1) := by ring
      _ ≤ D ^ 2 * ((u : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hscale hu1.le
      _ ≤ D ^ 2 * ((R : ℝ) + (B : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg D)
        linarith
  calc
    terminalFailureMass
        (iter urnStopped s (R, B))
        (Lemma14UrnGood
          ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
          (D / ((u : ℝ) + 1)))
        ≤ 2 * ENNReal.ofReal
          (Real.exp (-(2 * δ ^ 2 / A))) := by
            simpa [δ, A] using
              lemma14_without_replacement_exact
                δ s u R B hδ hs hclock
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-L)) := by
      have hexp :
          Real.exp (-(2 * δ ^ 2 / A)) ≤
            Real.exp (-L) :=
        Real.exp_le_exp.mpr (by linarith [hrate])
      have hof :
          ENNReal.ofReal (Real.exp (-(2 * δ ^ 2 / A))) ≤
            ENNReal.ofReal (Real.exp (-L)) :=
        ENNReal.ofReal_le_ofReal hexp
      simpa [mul_comm] using
        mul_le_mul_left hof (2 : ℝ≥0∞)

/-- **Paper Lemma 14.**  In a sample of `s` balls without replacement, the
number of selected red balls differs from its mean `sR/(R+B)` by at most `D`,
except on mass at most `2 exp(-L)`, whenever `D² ≥ Ls`. -/
theorem lemma14
    (L D : ℝ) (s u R B : ℕ)
    (hD : 0 < D)
    (hs : 0 < s)
    (hclock : u + s + 1 = R + B)
    (hscale : L * (s : ℝ) ≤ D ^ 2) :
    terminalFailureMass
        (iter urnStopped s (R, B))
        (Lemma14SelectedGood R B s D)
      ≤
    2 * ENNReal.ofReal (Real.exp (-L)) := by
  let μ := iter urnStopped s (R, B)
  have hpoint :
      ∀ z,
        (if Lemma14SelectedGood R B s D z then 0 else μ z) ≤
          (if Lemma14UrnGood
              ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
              (D / ((u : ℝ) + 1)) z
            then 0 else μ z) := by
    intro z
    by_cases hzμ : μ z = 0
    · simp [hzμ]
    have htotal :=
      urnStopped_iter_total s (R, B) z
        (by omega) (by simpa [μ] using hzμ)
    have hrem : z.1 + z.2 = u + 1 := by
      omega
    have himp :
        Lemma14UrnGood
            ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
            (D / ((u : ℝ) + 1)) z →
          Lemma14SelectedGood R B s D z :=
      lemma14_urn_good_implies_selected_good
        D s u R B z hclock hrem
    by_cases hsel : Lemma14SelectedGood R B s D z
    · simp [hsel]
    · have hurn :
          ¬ Lemma14UrnGood
            ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
            (D / ((u : ℝ) + 1)) z := by
        intro hz
        exact hsel (himp hz)
      simp [hsel, hurn]
  calc
    terminalFailureMass
        (iter urnStopped s (R, B))
        (Lemma14SelectedGood R B s D)
        ≤ terminalFailureMass
          (iter urnStopped s (R, B))
          (Lemma14UrnGood
            ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
            (D / ((u : ℝ) + 1))) := by
          unfold terminalFailureMass
          simpa [μ] using ENNReal.tsum_le_tsum hpoint
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-L)) :=
      lemma14_fraction L D s u R B hD hs hclock hscale

end

end Tri

#print axioms Tri.lemma14_selected_deviation_eq
#print axioms Tri.lemma14_urn_good_implies_selected_good
#print axioms Tri.lemma14_without_replacement_exact
#print axioms Tri.lemma14_fraction
#print axioms Tri.lemma14

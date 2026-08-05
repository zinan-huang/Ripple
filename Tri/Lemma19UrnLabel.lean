/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.FiniteHorizonUnion
import Tri.PaperLemma14
import Tri.TimeChangeHitting

/-!
# Full-pool immutable-label tails for Lemma 19

The first-`k` maximal potential used in Lemmas 16 and 17 deliberately spends a
constant fraction of the remaining urn.  Lemma 19 instead needs every prefix
up to the last unrevealed identity.  Here a finite union of the fixed-time
Lemma 14 bound retains the correct `D² / population` exponent.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Relative to initial counts `(B,R)`, the selected identities have strict
adverse `Y-X` excess larger than `D`.  Additive witnesses avoid natural
subtraction in the event statement. -/
def UrnSelectedYExcessBad
    (D B R : ℕ) (z : ℕ × ℕ) : Prop :=
  ∃ xSel ySel,
    xSel + z.1 = B ∧
      ySel + z.2 = R ∧
      xSel + D < ySel

noncomputable instance urnSelectedYExcessBadDecidable
    (D B R : ℕ) :
    DecidablePred (UrnSelectedYExcessBad D B R) :=
  Classical.decPred _

/-- At a supported fixed-time endpoint, Lemma 14's selected-`X` event
excludes a selected `Y-X` excess. -/
theorem lemma14SelectedGood_not_yExcess
    (D j u B R : ℕ) (z : ℕ × ℕ)
    (hD : 0 < D)
    (hmajor : R ≤ B)
    (hclock : u + j + 1 = B + R)
    (htotal : z.1 + z.2 + j = B + R)
    (hgood :
      Lemma14SelectedGood B R j ((D : ℝ) / 2) z) :
    ¬ UrnSelectedYExcessBad D B R z := by
  intro hbad
  rcases hbad with
    ⟨xSel, ySel, hx, hy, hxy⟩
  have hselected : xSel + ySel = j := by
    omega
  have hdenom : (0 : ℝ) < (B : ℝ) + (R : ℝ) := by
    have : 0 < B + R := by omega
    exact_mod_cast this
  have hhalf :
      (1 / 2 : ℝ) ≤
        (B : ℝ) / ((B : ℝ) + (R : ℝ)) := by
    rw [le_div_iff₀ hdenom]
    have hmajorR : (R : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hmajor
    nlinarith
  have hxInt :
      (B : ℤ) - (z.1 : ℤ) = (xSel : ℤ) := by
    omega
  have hxyR :
      (xSel : ℝ) + (D : ℝ) <
        (ySel : ℝ) := by
    exact_mod_cast hxy
  have hselectedR :
      (xSel : ℝ) + (ySel : ℝ) = (j : ℝ) := by
    exact_mod_cast hselected
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hdev :
      (xSel : ℝ) -
          (j : ℝ) *
            ((B : ℝ) / ((B : ℝ) + (R : ℝ))) <
        -((D : ℝ) / 2) := by
    have hmul :
        (j : ℝ) * (1 / 2 : ℝ) ≤
          (j : ℝ) *
            ((B : ℝ) / ((B : ℝ) + (R : ℝ))) :=
      mul_le_mul_of_nonneg_left hhalf hj0
    nlinarith
  have hneg :
      (xSel : ℝ) -
          (j : ℝ) *
            ((B : ℝ) / ((B : ℝ) + (R : ℝ))) <
        0 := by
    have hDreal : (0 : ℝ) < (D : ℝ) := by
      exact_mod_cast hD
    linarith
  unfold Lemma14SelectedGood at hgood
  rw [hxInt] at hgood
  norm_cast at hgood
  have hterm :
      (((j * B : ℕ) : ℝ) / ((B + R : ℕ) : ℝ)) =
        (j : ℝ) *
          ((B : ℝ) / ((B : ℝ) + (R : ℝ))) := by
    push_cast
    ring
  rw [hterm] at hgood
  rw [abs_of_neg hneg] at hgood
  linarith

/-- Fixed-time selected `Y-X` excess tail from a majority-`X` urn. -/
theorem urnSelectedYExcess_fixed_tail
    (L : ℝ) (D j u B R : ℕ)
    (hD : 0 < D)
    (hj : 0 < j)
    (hmajor : R ≤ B)
    (hclock : u + j + 1 = B + R)
    (hscale :
      L * (j : ℝ) ≤ ((D : ℝ) / 2) ^ 2) :
    terminalFailureMass
        (iter urnStopped j (B, R))
        (fun z => ¬ UrnSelectedYExcessBad D B R z)
      ≤
    2 * ENNReal.ofReal (Real.exp (-L)) := by
  let μ := iter urnStopped j (B, R)
  have hcontain :
      terminalFailureMass μ
          (fun z => ¬ UrnSelectedYExcessBad D B R z)
        ≤
      terminalFailureMass μ
          (Lemma14SelectedGood B R j ((D : ℝ) / 2)) := by
    unfold terminalFailureMass
    exact ENNReal.tsum_le_tsum fun z => by
      by_cases hzμ : μ z = 0
      · simp [hzμ]
      · have htotal :=
          urnStopped_iter_total j (B, R) z
            (by omega) (by simpa [μ] using hzμ)
        have himp :=
          lemma14SelectedGood_not_yExcess
            D j u B R z hD hmajor hclock htotal
        by_cases hgood :
            Lemma14SelectedGood B R j ((D : ℝ) / 2) z
        · have hnBad := himp hgood
          simp [hgood, hnBad]
        · by_cases hbad :
              UrnSelectedYExcessBad D B R z
          · simp [hgood, hbad]
          · simp [hgood, hbad]
  calc
    terminalFailureMass
        (iter urnStopped j (B, R))
        (fun z => ¬ UrnSelectedYExcessBad D B R z)
        ≤
      terminalFailureMass
        (iter urnStopped j (B, R))
        (Lemma14SelectedGood B R j ((D : ℝ) / 2)) := by
          simpa [μ] using hcontain
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-L)) :=
      lemma14 L ((D : ℝ) / 2) j u B R
        (by positivity) hj hclock hscale

/-- A finite first-hit horizon costs only its number of fixed-time
marginals.  The common scale condition uses the full initial pool. -/
theorem urnSelectedYExcess_hitProb
    (L : ℝ) (D k B R : ℕ)
    (hD : 0 < D)
    (hmajor : R ≤ B)
    (hroom : k + 1 ≤ B + R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((D : ℝ) / 2) ^ 2) :
    hitProb
        (UrnSelectedYExcessBad D B R)
        urnStopped k (B, R)
      ≤
    (k + 1 : ℝ≥0∞) *
      (2 * ENNReal.ofReal (Real.exp (-L))) := by
  let ε : ℝ≥0∞ :=
    2 * ENNReal.ofReal (Real.exp (-L))
  have hfixed :
      ∀ j ∈ Finset.range (k + 1),
        terminalFailureMass
            (iter urnStopped j (B, R))
            (fun z =>
              ¬ UrnSelectedYExcessBad D B R z)
          ≤ ε := by
    intro j hjRange
    have hjk : j ≤ k := by
      simpa [Finset.mem_range] using hjRange
    by_cases hj0 : j = 0
    · subst j
      have hnot :
          ¬ UrnSelectedYExcessBad D B R (B, R) := by
        intro hbad
        rcases hbad with
          ⟨xSel, ySel, hx, hy, hxy⟩
        omega
      simp [iter, terminalFailureMass_pure, hnot, ε]
    · have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
      have hjRoom : j + 1 ≤ B + R := by omega
      obtain ⟨u, hu⟩ :=
        Nat.exists_eq_add_of_le hjRoom
      have hclock : u + j + 1 = B + R := by
        omega
      have hscaleJ :
          L * (j : ℝ) ≤ ((D : ℝ) / 2) ^ 2 := by
        have hjPool : (j : ℝ) ≤ ((B + R : ℕ) : ℝ) := by
          exact_mod_cast (show j ≤ B + R by omega)
        by_cases hL : 0 ≤ L
        · exact
            (mul_le_mul_of_nonneg_left hjPool hL).trans
              hscale
        · have hleft : L * (j : ℝ) ≤ 0 := by
            exact mul_nonpos_of_nonpos_of_nonneg
              (le_of_not_ge hL) (Nat.cast_nonneg j)
          exact hleft.trans (sq_nonneg _)
      simpa [ε] using
        urnSelectedYExcess_fixed_tail
          L D j u B R hD hjPos hmajor hclock hscaleJ
  calc
    hitProb
        (UrnSelectedYExcessBad D B R)
        urnStopped k (B, R)
        ≤
      ∑ j ∈ Finset.range (k + 1),
        terminalFailureMass
          (iter urnStopped j (B, R))
          (fun z =>
            ¬ UrnSelectedYExcessBad D B R z) :=
      hitProb_le_sum_terminalEventMass
        (UrnSelectedYExcessBad D B R)
        urnStopped k (B, R)
    _ ≤
      ∑ _j ∈ Finset.range (k + 1), ε := by
        exact Finset.sum_le_sum hfixed
    _ =
      (k + 1 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) := by
          simp [ε]

/-- A stopped urn started with `k+1` balls cannot first enter a target after
time `k`, provided the target is absent on the one-ball floor. -/
theorem urnStopped_hitProb_le_clock
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad]
    (k : ℕ) :
    ∀ (q : ℕ × ℕ),
      k + 1 = q.1 + q.2 →
      (∀ z, z.1 + z.2 ≤ 1 → ¬ Bad z) →
      ∀ T,
        hitProb Bad urnStopped T q ≤
          hitProb Bad urnStopped k q := by
  induction k with
  | zero =>
      intro q hclock hfloor T
      have htotal : q.1 + q.2 ≤ 1 := by omega
      have hnot : ¬ Bad q := hfloor q htotal
      have hurn : urnStopped q = PMF.pure q := by
        unfold urnStopped
        rw [freeze_of_mem q htotal]
      have hfreeze :
          freeze Bad urnStopped q = PMF.pure q := by
        rw [freeze_of_not_mem q hnot, hurn]
      have hiter :
          ∀ U, iter (freeze Bad urnStopped) U q =
            PMF.pure q := by
        intro U
        induction U with
        | zero => rfl
        | succ U ih =>
            rw [iter_succ, hfreeze, PMF.pure_bind, ih]
      have hzero :
          ∀ U, hitProb Bad urnStopped U q = 0 := by
        intro U
        unfold hitProb
        rw [hiter U, expect_pure]
        simp [ind, hnot]
      rw [hzero T, hzero 0]
  | succ k ih =>
      intro q hclock hfloor T
      by_cases hqBad : Bad q
      · rw [hitProb_eq_one_of_mem Bad urnStopped T q hqBad,
          hitProb_eq_one_of_mem Bad urnStopped (k + 1) q hqBad]
      · cases T with
        | zero =>
            have hzero :
                hitProb Bad urnStopped 0 q = 0 := by
              unfold hitProb
              rw [show
                iter (freeze Bad urnStopped) 0 q =
                  PMF.pure q by rfl, expect_pure]
              simp [ind, hqBad]
            rw [hzero]
            exact bot_le
        | succ T =>
            rw [hitProb_succ_of_not
                Bad urnStopped T q hqBad,
              hitProb_succ_of_not
                Bad urnStopped k q hqBad]
            exact ENNReal.tsum_le_tsum fun z => by
              by_cases hz : urnStopped q z = 0
              · simp [hz]
              · have hqLive :
                    ¬ q.1 + q.2 ≤ 1 := by
                  omega
                have hurn :
                    urnStopped q = urnChain q := by
                  unfold urnStopped
                  rw [freeze_of_not_mem q hqLive]
                have hzChain : urnChain q z ≠ 0 := by
                  rw [← hurn]
                  exact hz
                have hstep :=
                  urnChain_support_total q (by omega) z hzChain
                have hzclock :
                    k + 1 = z.1 + z.2 := by
                  omega
                exact mul_le_mul_left'
                  (ih z hzclock hfloor T) _

/-- Unbounded-horizon form of the deterministic urn clock. -/
theorem urnStopped_everHit_le_clock
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad]
    (k : ℕ) (q : ℕ × ℕ)
    (hclock : k + 1 = q.1 + q.2)
    (hfloor : ∀ z, z.1 + z.2 ≤ 1 → ¬ Bad z) :
    everHit Bad urnStopped q ≤
      hitProb Bad urnStopped k q := by
  unfold everHit
  exact iSup_le fun T =>
    urnStopped_hitProb_le_clock
      Bad k q hclock hfloor T

/-- The full-pool maximal selected-label tail.  The last one-ball floor
cannot carry a strict adverse excess when `D>0` and the initial pool has an
`X` majority. -/
theorem urnSelectedYExcess_everHit
    (L : ℝ) (D k B R : ℕ)
    (hD : 0 < D)
    (hmajor : R ≤ B)
    (hclock : k + 1 = B + R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((D : ℝ) / 2) ^ 2) :
    everHit
        (UrnSelectedYExcessBad D B R)
        urnStopped (B, R)
      ≤
    (k + 1 : ℝ≥0∞) *
      (2 * ENNReal.ofReal (Real.exp (-L))) := by
  have hfloor :
      ∀ z, z.1 + z.2 ≤ 1 →
        ¬ UrnSelectedYExcessBad D B R z := by
    intro z hz hbad
    rcases hbad with
      ⟨xSel, ySel, hx, hy, hxy⟩
    omega
  calc
    everHit
        (UrnSelectedYExcessBad D B R)
        urnStopped (B, R)
        ≤
      hitProb
        (UrnSelectedYExcessBad D B R)
        urnStopped k (B, R) :=
      urnStopped_everHit_le_clock
        (UrnSelectedYExcessBad D B R)
        k (B, R) (by simpa using hclock) hfloor
    _ ≤
      (k + 1 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) :=
      urnSelectedYExcess_hitProb
        L D k B R hD hmajor (by omega) hscale

end

end Tri

#print axioms Tri.lemma14SelectedGood_not_yExcess
#print axioms Tri.urnSelectedYExcess_fixed_tail
#print axioms Tri.urnSelectedYExcess_hitProb
#print axioms Tri.urnStopped_hitProb_le_clock
#print axioms Tri.urnStopped_everHit_le_clock
#print axioms Tri.urnSelectedYExcess_everHit

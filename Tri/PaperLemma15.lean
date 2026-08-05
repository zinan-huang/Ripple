/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma15Assembly
import Tri.SameHorizon

/-!
# Paper Lemma 15: prefixes of a contiguous activation block

The first `a` urn reveals model the activations preceding a fixed contiguous
block.  The next `s` reveals model the block itself.  The theorem controls
every prefix of that block, while retaining the random urn composition at the
block's opening as an anchor.

The prefix and window estimates are both discharged here.  Thus the public
theorem has no abstract probability hypotheses left.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The paper's adverse event: in some prefix of length `k ≤ s`, the selected
`Y` count `w` has excess `2w-k` at least `D`. -/
def GlobalYExcessBad
    (D : ℝ) (s : ℕ) (q z : ℕ × ℕ) : Prop :=
  ∃ w k : ℕ,
    z.1 + w = q.1 ∧
      k + (z.1 + z.2) = q.1 + q.2 ∧
      k ≤ s ∧
      D + (k : ℝ) ≤ 2 * (w : ℝ)

noncomputable instance globalYExcessBadDecidable
    (D : ℝ) (s : ℕ) (q : ℕ × ℕ) :
    DecidablePred (GlobalYExcessBad D s q) :=
  Classical.decPred _

/-- If the global `Y` fraction is at most one half, a `Y`-excess of `D`
forces a global-centred selected-`Y` deviation of `D/2`. -/
theorem globalYExcessBad_to_globalBad
    (c D : ℝ) (s : ℕ) (q z : ℕ × ℕ)
    (hc : c ≤ 1 / 2)
    (hbad : GlobalYExcessBad D s q z) :
    GlobalBad c (D / 2) s q z := by
  obtain ⟨w, k, hw, htotal, hks, hexcess⟩ := hbad
  refine ⟨w, k, hw, htotal, hks, ?_⟩
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

/-- Prefix error in the paper Lemma 15 capstone.  A block starting at the
first reveal has no prefix error. -/
noncomputable def lemma15PrefixError
    (Δ : ℝ) (s ν₂ a R B : ℕ) : ℝ≥0∞ :=
  if a = 0 then 0
  else
    ENNReal.ofReal
      (Real.exp
        (-(2 * (Δ / (3 * (s : ℝ))) ^ 2 /
          (2 * (a : ℝ) /
            ((ν₂ : ℝ) * ((R : ℝ) + (B : ℝ)))))))

/-- Maximal-window error in the paper Lemma 15 capstone. -/
noncomputable def lemma15WindowError
    (Δ : ℝ) (s u ν₂ : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp
      (-(2 * (2 * Δ / (3 * (ν₂ : ℝ))) ^ 2 /
        (2 * (s : ℝ) /
          (((u : ℝ) + 1) * (ν₂ : ℝ))))))

/-- The fixed-time estimate for the random composition at the opening of the
block. -/
theorem lemma15_prefix_failure
    (Δ : ℝ) (s u ν₂ a R B : ℕ)
    (hΔ : 0 < Δ)
    (hs : 0 < s)
    (ha : 0 < a)
    (hprefix : a + ν₂ = R + B)
    (hwindow : u + s + 1 = ν₂) :
    terminalFailureMass
        (iter urnStopped a (R, B))
        (PrefixGood
          ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
          Δ s ν₂)
      ≤
    ENNReal.ofReal
      (Real.exp
        (-(2 * (Δ / (3 * (s : ℝ))) ^ 2 /
          (2 * (a : ℝ) /
            ((ν₂ : ℝ) * ((R : ℝ) + (B : ℝ))))))) := by
  let c : ℝ := (R : ℝ) / ((R : ℝ) + (B : ℝ))
  let δ : ℝ := Δ / (3 * (s : ℝ))
  let A : ℝ :=
    2 * (a : ℝ) /
      ((ν₂ : ℝ) * ((R : ℝ) + (B : ℝ)))
  let lam : ℝ := -(4 * δ / A)
  let Bad : ℕ × ℕ → Prop :=
    UrnWindowBad c δ lam (u + s)
  let μ := iter urnStopped a (R, B)
  have hsR : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast hs
  have haR : (0 : ℝ) < (a : ℝ) := by
    exact_mod_cast ha
  have hν₂ : 0 < ν₂ := by omega
  have hν₂R : (0 : ℝ) < (ν₂ : ℝ) := by
    exact_mod_cast hν₂
  have hRB : (0 : ℝ) < (R : ℝ) + (B : ℝ) := by
    have : 0 < R + B := by omega
    exact_mod_cast this
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hlam : lam < 0 := by
    dsimp only [lam]
    have : 0 < 4 * δ / A := by positivity
    linarith
  have hclock : (u + s) + a + 1 = R + B := by
    omega
  have hν₂cast :
      (ν₂ : ℝ) = (u : ℝ) + (s : ℝ) + 1 := by
    exact_mod_cast hwindow.symm
  have hpoint :
      ∀ z,
        (if PrefixGood c Δ s ν₂ z then 0 else μ z) ≤
          (if Bad z then μ z else 0) := by
    intro z
    by_cases hzμ : μ z = 0
    · simp [hzμ]
    have htotal :=
      urnStopped_iter_total a (R, B) z
        (by omega) (by simpa [μ] using hzμ)
    have hzν₂ : z.1 + z.2 = ν₂ := by
      omega
    by_cases hgood : PrefixGood c Δ s ν₂ z
    · simp [hgood]
    · have hdrift :
          c + δ <
            (z.1 : ℝ) / ((z.1 : ℝ) + (z.2 : ℝ)) := by
        have hnot :
            ¬ ((z.1 : ℝ) / ((z.1 : ℝ) + (z.2 : ℝ))
                ≤ c + Δ / (3 * (s : ℝ))) := by
          intro hle
          exact hgood ⟨hzν₂, hle⟩
        simpa [δ] using lt_of_not_ge hnot
      have hdev :
          δ ≤
            (z.1 : ℝ) / ((z.1 : ℝ) + (z.2 : ℝ)) - c := by
        linarith
      have hBad : Bad z := by
        refine ⟨by omega, ?_⟩
        dsimp only [Bad]
        rw [abs_of_neg hlam]
        have hmul :=
          mul_le_mul_of_nonneg_left hdev (neg_nonneg.mpr hlam.le)
        unfold urnM
        nlinarith
      simp [hgood, hBad]
  have hterminal :
      terminalFailureMass μ (PrefixGood c Δ s ν₂) ≤
        terminalFailureMass μ (fun z => ¬ Bad z) := by
    unfold terminalFailureMass
    calc
      (∑' z, if PrefixGood c Δ s ν₂ z then 0 else μ z)
          ≤ ∑' z, if Bad z then μ z else 0 :=
        ENNReal.tsum_le_tsum hpoint
      _ = ∑' z, if ¬ Bad z then 0 else μ z := by
        apply tsum_congr
        intro z
        by_cases hz : Bad z <;> simp [hz]
  calc
    terminalFailureMass
        (iter urnStopped a (R, B))
        (PrefixGood
          ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
          Δ s ν₂)
        ≤ terminalFailureMass μ (fun z => ¬ Bad z) := by
          simpa [c, μ] using hterminal
    _ ≤ hitProb Bad urnStopped a (R, B) := by
      simpa [μ] using
        terminalEventMass_iter_le_hitProb
          Bad urnStopped a (R, B)
    _ ≤ ⨆ T : ℕ, hitProb Bad urnStopped T (R, B) :=
      le_iSup (fun T => hitProb Bad urnStopped T (R, B)) a
    _ ≤ ENNReal.ofReal
        (Real.exp (-(2 * δ ^ 2 / A))) := by
      simpa [Bad, c, δ, A, lam, hν₂cast, add_assoc] using
        urn_window_tail_telescope_neg
          δ (u + s) a R B hδ.le hclock ha
    _ = ENNReal.ofReal
        (Real.exp
          (-(2 * (Δ / (3 * (s : ℝ))) ^ 2 /
            (2 * (a : ℝ) /
              ((ν₂ : ℝ) *
                ((R : ℝ) + (B : ℝ))))))) := by
      rfl

/-- Pointwise maximal-window estimate from every good random anchor. -/
theorem lemma15_window_failure
    (c Δ : ℝ) (s u ν₂ : ℕ) (q : ℕ × ℕ)
    (hΔ : 0 < Δ)
    (hs : 0 < s)
    (hwindow : u + s + 1 = ν₂)
    (hq : PrefixGood c Δ s ν₂ q) :
    hitProb (GlobalBad c Δ s q) urnStopped s q
      ≤ lemma15WindowError Δ s u ν₂ := by
  obtain ⟨hqtotal, hqdrift⟩ := hq
  have hqcast :
      (q.1 : ℝ) + (q.2 : ℝ) = (ν₂ : ℝ) := by
    exact_mod_cast hqtotal
  let δ : ℝ := 2 * Δ / (3 * (ν₂ : ℝ))
  let A : ℝ :=
    2 * (s : ℝ) /
      (((u : ℝ) + 1) * (ν₂ : ℝ))
  let lam : ℝ := 4 * δ / A
  have hν₂ : 0 < ν₂ := by omega
  have hν₂R : (0 : ℝ) < (ν₂ : ℝ) := by
    exact_mod_cast hν₂
  have hsR : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast hs
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hlam : 0 < lam := by
    dsimp only [lam]
    positivity
  have hdom :
      ∀ z, GlobalBad c Δ s q z →
        UrnWindowBad
          ((q.1 : ℝ) / ((q.1 : ℝ) + (q.2 : ℝ)))
          δ lam u z := by
    intro z hz
    have hraw :=
      urn_global_dominates
        c Δ s u q z lam hs hΔ.le hlam
        (by omega) (by omega) hqdrift hz
    have hδeq :
        2 * Δ /
            (3 * ((q.1 : ℝ) + (q.2 : ℝ))) =
          δ := by
      rw [hqcast]
    rw [hδeq] at hraw
    exact hraw
  calc
    hitProb (GlobalBad c Δ s q) urnStopped s q
        ≤ hitProb
          (UrnWindowBad
            ((q.1 : ℝ) / ((q.1 : ℝ) + (q.2 : ℝ)))
            δ lam u)
          urnStopped s q :=
      hitProb_mono_target hdom s q
    _ ≤ ⨆ T : ℕ,
        hitProb
          (UrnWindowBad
            ((q.1 : ℝ) / ((q.1 : ℝ) + (q.2 : ℝ)))
            δ lam u)
          urnStopped T q :=
      le_iSup
        (fun T =>
          hitProb
            (UrnWindowBad
              ((q.1 : ℝ) / ((q.1 : ℝ) + (q.2 : ℝ)))
              δ lam u)
            urnStopped T q) s
    _ ≤ ENNReal.ofReal
        (Real.exp (-(2 * δ ^ 2 / A))) := by
      simpa [δ, A, lam, hqcast] using
        urn_window_tail_telescope
          δ u s q.1 q.2 hδ.le (by omega) hs
    _ = lemma15WindowError Δ s u ν₂ := by
      rfl

/-- Fully discharged one-sided capstone for the global-centred window event. -/
theorem lemma15_global
    (Δ : ℝ) (s u ν₂ a R B : ℕ)
    (hΔ : 0 < Δ)
    (hs : 0 < s)
    (hprefix : a + ν₂ = R + B)
    (hwindow : u + s + 1 = ν₂) :
    ∑' q,
      iter urnStopped a (R, B) q *
        hitProb
          (GlobalBad
            ((R : ℝ) / ((R : ℝ) + (B : ℝ)))
            Δ s q)
          urnStopped s q
      ≤
    lemma15PrefixError Δ s ν₂ a R B +
      lemma15WindowError Δ s u ν₂ := by
  let c : ℝ := (R : ℝ) / ((R : ℝ) + (B : ℝ))
  let Good : ℕ × ℕ → Prop := PrefixGood c Δ s ν₂
  let Bad : ℕ × ℕ → ℕ × ℕ → Prop := GlobalBad c Δ s
  let εpre : ℝ≥0∞ := lemma15PrefixError Δ s ν₂ a R B
  let εwin : ℝ≥0∞ := lemma15WindowError Δ s u ν₂
  have hgood :
      ∀ q, Good q →
        hitProb (Bad q) urnStopped s q ≤ εwin := by
    intro q hq
    exact
      lemma15_window_failure
        c Δ s u ν₂ q hΔ hs hwindow hq
  by_cases ha0 : a = 0
  · subst a
    have hstart : Good (R, B) := by
      refine ⟨by omega, ?_⟩
      dsimp only [Good, c]
      have hnonneg :
          0 ≤ Δ / (3 * (s : ℝ)) := by
        positivity
      linarith
    have hpre :
        (∑' q,
          if Good q then 0
          else iter urnStopped 0 (R, B) q) ≤ εpre := by
      have hzero :
          terminalFailureMass
              (iter urnStopped 0 (R, B)) Good = 0 := by
        rw [terminalFailureMass_eq_expect]
        simp [iter, hstart]
      simpa [terminalFailureMass, εpre,
        lemma15PrefixError] using hzero.le
    simpa [c, Good, Bad, εpre, εwin] using
      recentred_split
        urnStopped 0 s (R, B) Good Bad εpre εwin
        hpre hgood
  · have ha : 0 < a := Nat.pos_of_ne_zero ha0
    have hpre :
        (∑' q,
          if Good q then 0
          else iter urnStopped a (R, B) q) ≤ εpre := by
      simpa [Good, c, εpre, lemma15PrefixError, ha0] using
        lemma15_prefix_failure
          Δ s u ν₂ a R B hΔ hs ha hprefix hwindow
    simpa [c, Good, Bad, εpre, εwin] using
      recentred_split
        urnStopped a s (R, B) Good Bad εpre εwin
        hpre hgood

/-- **Paper Lemma 15.**  Let the first coordinate be the initially inactive
`Y` population and suppose its fraction is at most one half.  For a fixed
contiguous block of `s` activations, the probability that any prefix has
`Y`-excess at least `D` is bounded by the two explicit
sampling-without-replacement errors. -/
theorem lemma15
    (D : ℝ) (s u ν₂ a Y X : ℕ)
    (hD : 0 < D)
    (hs : 0 < s)
    (hminority : 2 * Y ≤ Y + X)
    (hprefix : a + ν₂ = Y + X)
    (hwindow : u + s + 1 = ν₂) :
    ∑' q,
      iter urnStopped a (Y, X) q *
        hitProb (GlobalYExcessBad D s q)
          urnStopped s q
      ≤
    lemma15PrefixError (D / 2) s ν₂ a Y X +
      lemma15WindowError (D / 2) s u ν₂ := by
  let c : ℝ := (Y : ℝ) / ((Y : ℝ) + (X : ℝ))
  have hYX : (0 : ℝ) < (Y : ℝ) + (X : ℝ) := by
    have : 0 < Y + X := by omega
    exact_mod_cast this
  have hc : c ≤ 1 / 2 := by
    dsimp only [c]
    rw [div_le_iff₀ hYX]
    have hcast : (2 : ℝ) * (Y : ℝ) ≤ (Y : ℝ) + (X : ℝ) := by
      exact_mod_cast hminority
    nlinarith
  have hpoint :
      ∀ q,
        iter urnStopped a (Y, X) q *
            hitProb (GlobalYExcessBad D s q)
              urnStopped s q
          ≤
        iter urnStopped a (Y, X) q *
            hitProb (GlobalBad c (D / 2) s q)
              urnStopped s q := by
    intro q
    apply mul_le_mul_left'
    exact hitProb_mono_target
      (fun z hz =>
        globalYExcessBad_to_globalBad
          c D s q z hc hz)
      s q
  calc
    (∑' q,
      iter urnStopped a (Y, X) q *
        hitProb (GlobalYExcessBad D s q)
          urnStopped s q)
        ≤ ∑' q,
          iter urnStopped a (Y, X) q *
            hitProb (GlobalBad c (D / 2) s q)
              urnStopped s q :=
      ENNReal.tsum_le_tsum hpoint
    _ ≤ lemma15PrefixError (D / 2) s ν₂ a Y X +
        lemma15WindowError (D / 2) s u ν₂ := by
      simpa [c] using
        lemma15_global
          (D / 2) s u ν₂ a Y X
          (by positivity) hs hprefix hwindow

end

end Tri

#print axioms Tri.globalYExcessBad_to_globalBad
#print axioms Tri.lemma15_prefix_failure
#print axioms Tri.lemma15_window_failure
#print axioms Tri.lemma15_global
#print axioms Tri.lemma15

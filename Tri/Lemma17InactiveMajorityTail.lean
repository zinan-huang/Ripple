/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17PoolTail

/-!
# Inactive-majority tails for Lemma 17

If the inactive pool starts with an `X` advantage of at least `D`, then any
later prefix whose remaining pool has a strict `Y` majority lies in the
positive-tilt Lemma 16 urn event.  This is the global anchor event needed
between Lemma 17 doubling stages.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Losing an initial inactive `X` advantage forces a positive centred
deviation of the remaining `X` fraction. -/
theorem lemma17_remaining_majority_fail_implies_urnWindowBad
    (D u k B R xRem yRem : ℕ)
    (hBR : B + R = u + k + 1)
    (hgap : R + D ≤ B)
    (hclock : u + 1 ≤ xRem + yRem)
    (hfail : xRem < yRem)
    (hk : 0 < k) :
    Lemma16UrnWindowBad D u k B R (xRem, yRem) := by
  have hBRPos : 0 < B + R := by omega
  have hremPos : 0 < xRem + yRem := by omega
  have hBRPosR : (0 : ℝ) < (B : ℝ) + (R : ℝ) := by
    exact_mod_cast hBRPos
  have hremPosR :
      (0 : ℝ) < (xRem : ℝ) + (yRem : ℝ) := by
    exact_mod_cast hremPos
  have hgapR : (R : ℝ) + (D : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hgap
  have hfailR : (xRem : ℝ) < (yRem : ℝ) := by
    exact_mod_cast hfail
  have hnum :
      (D : ℝ) *
            ((xRem : ℝ) + (yRem : ℝ)) / 2 ≤
        (B : ℝ) * (yRem : ℝ) -
          (R : ℝ) * (xRem : ℝ) := by
    nlinarith
  have hdelta :
      (D : ℝ) /
            (2 * ((B : ℝ) + (R : ℝ))) ≤
        (B : ℝ) / ((B : ℝ) + (R : ℝ)) -
          (xRem : ℝ) /
            ((xRem : ℝ) + (yRem : ℝ)) := by
    field_simp [ne_of_gt hBRPosR, ne_of_gt hremPosR]
    nlinarith [hnum]
  refine ⟨hclock, ?_⟩
  let delta : ℝ :=
    (D : ℝ) / (2 * ((B : ℝ) + (R : ℝ)))
  let A : ℝ :=
    2 * (k : ℝ) /
      (((u : ℝ) + 1) * ((B : ℝ) + (R : ℝ)))
  let lam : ℝ := 4 * delta / A
  have hkR : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta]
    positivity
  have hlam0 : 0 ≤ lam := by
    dsimp only [lam]
    positivity
  change
    |lam| * delta ≤
      lam *
        urnM
          ((B : ℝ) / ((B : ℝ) + (R : ℝ)))
          (xRem, yRem)
  rw [abs_of_nonneg hlam0]
  unfold urnM
  exact mul_le_mul_of_nonneg_left hdelta hlam0

/-- Positive-tilt urn tail for an arbitrary current inactive pool. -/
theorem lemma17_urn_window_tail_pool
    (q D a k u nu B R : ℕ)
    (hqa : q * a ≤ D ^ 2)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hBR : B + R = nu)
    (hquarter : 4 * a ≤ nu + 1)
    (hk0 : 0 < k) :
    ⨆ T : ℕ,
        hitProb (Lemma16UrnWindowBad D u k B R)
          urnStopped T (B, R)
      ≤ lemma16UrnError q := by
  have hsum : u + k + 1 = B + R := by omega
  have htail :=
    urn_window_tail_telescope
      ((D : ℝ) / (2 * ((B : ℝ) + (R : ℝ))))
      u k B R (by positivity) hsum hk0
  refine htail.trans ?_
  unfold lemma16UrnError
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hBRReal :
      (B : ℝ) + (R : ℝ) = (nu : ℝ) := by
    exact_mod_cast hBR
  have hexp :
      2 * ((D : ℝ) /
            (2 * ((B : ℝ) + (R : ℝ)))) ^ 2 /
          (2 * (k : ℝ) /
            (((u : ℝ) + 1) *
              ((B : ℝ) + (R : ℝ)))) =
        ((D : ℝ) / (2 * (nu : ℝ))) ^ 2 *
          (nu : ℝ) * ((u : ℝ) + 1) / (k : ℝ) := by
    rw [hBRReal]
    field_simp
  rw [hexp]
  have hfloor :=
    lemma17_pool_exponent_floor
      (q : ℝ) (D : ℝ) a k u nu
      (by positivity)
      (by exact_mod_cast hqa)
      hk huk hquarter hk0
  linarith

/-- The remaining inactive pool has lost its `X` majority. -/
def Lemma17TraceInactiveMajorityBad
    {n : ℕ} (q : InfectionRevealTraceState n) : Prop :=
  q.current.xIds.card < q.current.yIds.card

noncomputable instance lemma17TraceInactiveMajorityBadDecidable
    {n : ℕ} :
    DecidablePred (@Lemma17TraceInactiveMajorityBad n) :=
  Classical.decPred _

/-- On the anchored reveal-trace invariant, loss of the remaining majority
forces the positive-tilt urn event. -/
theorem lemma17_traceInactiveMajorityBad_implies_urnWindowBad
    {n : ℕ} (v : InfectionInactiveView n)
    (D u k B R : ℕ)
    (hBR : B + R = u + k + 1)
    (hgap : R + D ≤ B)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (z : InfectionRevealTraceState n)
    (hz : Lemma16TracePrefixInv v k z)
    (hbad : Lemma17TraceInactiveMajorityBad z) :
    Lemma16UrnWindowBad D u k B R
      (infectionRevealTraceCounts z) := by
  have hanchor :
      z.anchor.ids.card = B + R := by
    calc
      z.anchor.ids.card =
          z.anchor.xIds.card + z.anchor.yIds.card := by
        rw [InfectionInactiveView.xIds_card_add_yIds_card]
      _ = B + R := by rw [hz.1, hx0, hy0]
  have hcurrent :=
    InfectionInactiveView.xIds_card_add_yIds_card
      z.current
  have hledger := z.revealed_length_add_current
  have hlen : z.revealed.length ≤ k := hz.2
  have htotal :
      z.revealed.length + z.current.ids.card =
        u + k + 1 := by
    omega
  have hclockIds :
      u + 1 ≤ z.current.ids.card := by
    omega
  have hclock :
      u + 1 ≤
        z.current.xIds.card + z.current.yIds.card := by
    simpa [hcurrent] using hclockIds
  exact
    lemma17_remaining_majority_fail_implies_urnWindowBad
      D u k B R
      z.current.xIds.card z.current.yIds.card
      hBR hgap hclock hbad hk

/-- Every current inactive-majority failure along the first `k` ordinary
reveals is controlled by the same positive-tilt urn event. -/
theorem lemma17_trace_inactive_majority_everHit_le_urn
    {n : ℕ} (v : InfectionInactiveView n)
    (D u k B R : ℕ)
    (hBR : B + R = u + k + 1)
    (hgap : R + D ≤ B)
    (hx0 : v.xIds.card = B)
    (hy0 : v.yIds.card = R)
    (hk : 0 < k)
    (hroom : k + 2 ≤ v.ids.card) :
    everHit
        Lemma17TraceInactiveMajorityBad
        (infectionRevealTraceFirstKStep k)
        (infectionRevealTraceInitial v)
      ≤
    everHit
        (Lemma16UrnWindowBad D u k B R)
        urnStopped (B, R) := by
  let Bad := Lemma16UrnWindowBad D u k B R
  let K := @infectionRevealTraceFirstKStep n k
  let P := Lemma16TracePrefixInv v k
  let V : InfectionRevealTraceState n → ℝ≥0∞ :=
    fun z => everHit Bad urnStopped
      (infectionRevealTraceCounts z)
  have hclosed :
      ∀ s, P s → ∀ z, K s z ≠ 0 → P z := by
    intro s hs z hz
    exact
      infectionRevealTraceFirstKStep_prefixInv_closed
        v k s z hs hz
  have hsuper :
      ∀ s, P s → expect (K s) V ≤ V s := by
    intro s hs
    exact
      expect_infectionRevealTraceFirstKStep_urnEverHit_le
        v k hroom Bad s hs
  have hcontain :
      ∀ z, P z → Lemma17TraceInactiveMajorityBad z →
        (1 : ℝ≥0∞) ≤ V z := by
    intro z hzP hz
    have hurn :=
      lemma17_traceInactiveMajorityBad_implies_urnWindowBad
        v D u k B R hBR hgap hx0 hy0 hk z hzP hz
    rw [show V z = 1 by
      exact everHit_eq_one_of_mem
        Bad urnStopped
        (infectionRevealTraceCounts z) hurn]
  have hinitial :
      P (infectionRevealTraceInitial v) :=
    ⟨rfl, by simp [infectionRevealTraceInitial]⟩
  have h :=
    ville_frozen_of_support_invariant
      K Lemma17TraceInactiveMajorityBad
      P V 1 (by simp) (by simp)
      hcontain hclosed hsuper
      (infectionRevealTraceInitial v) hinitial
  have hcounts :
      infectionRevealTraceCounts
          (infectionRevealTraceInitial v) =
        (B, R) := by
    simp [infectionRevealTraceCounts,
      infectionRevealTraceInitial,
      infectionInactiveCounts, hx0, hy0]
  unfold everHit at h ⊢
  dsimp only [V] at h
  rw [hcounts] at h
  simpa [K, P, Bad] using h

end

end Tri

#print axioms Tri.lemma17_remaining_majority_fail_implies_urnWindowBad
#print axioms Tri.lemma17_urn_window_tail_pool
#print axioms Tri.lemma17_traceInactiveMajorityBad_implies_urnWindowBad
#print axioms Tri.lemma17_trace_inactive_majority_everHit_le_urn

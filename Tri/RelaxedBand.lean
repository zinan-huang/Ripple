/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedDirection
import Tri.DoubleBAssembly
import Tri.RelaxedFeller

/-!
# Finite raw-time bands for unequal reaction rates

This file puts the productive-event direction tail and the adapted raw clock on
the same chain, frozen at both band boundaries.
-/

namespace Tri

open scoped ENNReal

/-- Lower ruin or upper success for a finite `X`-count band. -/
def RelaxedBandBoundary
    (lower target : ℕ) (q : ℕ × ℕ) : Prop :=
  q.1 ≤ lower ∨ target ≤ q.1

instance relaxedBandBoundaryDecidable
    (lower target : ℕ) :
    DecidablePred (RelaxedBandBoundary lower target) := by
  intro q
  unfold RelaxedBandBoundary
  infer_instance

/-- Counted relaxed chain frozen at both band boundaries. -/
noncomputable def relaxedBandStop
    (r : RelaxedRate) (n lower target : ℕ) :
    ℕ × ℕ → PMF (ℕ × ℕ) :=
  freeze (RelaxedBandBoundary lower target) (relaxedCount r n)

/-- The full direction potential is a supermartingale on the two-boundary
band chain. -/
theorem relaxedBandStop_theta_super
    (r : RelaxedRate)
    (n lower target bHi : ℕ)
    (beta slack tau : NNReal)
    (h3 : 3 ≤ n) (htarget : target ≤ n)
    (hband : lower + bHi + 2 = n)
    (hslack : r.fire + slack ≤ beta)
    (htau : tau * (bHi : NNReal) ≤ slack)
    (hB : 1 < beta + tau)
    (hcorner :
      beta * (bHi + 1 : NNReal) ≤
        r.fire * (lower + 1 : NNReal)) :
    ∀ q,
      expect (relaxedBandStop r n lower target q)
          (relaxedTheta
            (relaxedDirW (beta + tau) : ℝ≥0∞)
            (relaxedDirEta (beta + tau) : ℝ≥0∞)) ≤
        1 * relaxedTheta
          (relaxedDirW (beta + tau) : ℝ≥0∞)
          (relaxedDirEta (beta + tau) : ℝ≥0∞)
          q := by
  intro q
  by_cases hq : RelaxedBandBoundary lower target q
  · rw [relaxedBandStop, freeze_of_mem q hq, expect_pure, one_mul]
  · rw [relaxedBandStop, freeze_of_not_mem q hq]
    have hlive : lower + 1 ≤ q.1 := by
      unfold RelaxedBandBoundary at hq
      omega
    have hsuper :=
      relaxedDirStop_super r n lower bHi beta slack tau
        h3 hband hslack htau hB hcorner q
    unfold relaxedDirStop at hsuper
    rw [if_pos hlive] at hsuper
    exact hsuper

/-- Finite-band wrong-direction tail above a productive-event threshold. -/
theorem relaxedBandStop_direction_tail
    (r : RelaxedRate)
    (n lower target bHi thr M T : ℕ)
    (beta slack tau : NNReal)
    (h3 : 3 ≤ n) (htarget : target ≤ n)
    (hband : lower + bHi + 2 = n)
    (hslack : r.fire + slack ≤ beta)
    (htau : tau * (bHi : NNReal) ≤ slack)
    (hB : 1 < beta + tau)
    (hcorner :
      beta * (bHi + 1 : NNReal) ≤
        r.fire * (lower + 1 : NNReal))
    (q0 : ℕ × ℕ) (hc0 : q0.2 = 0) :
    ∑' q, (if q.1 ≤ thr ∧ M ≤ q.2 then
        iter (relaxedBandStop r n lower target) T q0 q else 0) ≤
      (relaxedDirW (beta + tau) : ℝ≥0∞) ^ q0.1 /
        ((relaxedDirW (beta + tau) : ℝ≥0∞) ^ thr *
          (relaxedDirEta (beta + tau) : ℝ≥0∞) ^ M) := by
  let w : ℝ≥0∞ := relaxedDirW (beta + tau)
  let eta : ℝ≥0∞ := relaxedDirEta (beta + tau)
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    exact_mod_cast le_of_lt (relaxedDir_w_lt_one hB)
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    simp only [ne_eq, ENNReal.coe_eq_zero]
    unfold relaxedDirW
    positivity
  have heta1 : 1 ≤ eta := by
    dsimp only [eta]
    exact_mod_cast le_of_lt (relaxedDir_eta_gt_one hB)
  have hwt : w ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hetat : eta ≠ ⊤ := by finiteness
  let theta : ℝ≥0∞ := w ^ thr * eta ^ M
  have htheta0 : theta ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ hw0)
    apply pow_ne_zero
    intro heta0
    rw [heta0] at heta1
    simp at heta1
  have hthetatop : theta ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt)
      (ENNReal.pow_ne_top hetat)
  have hsub : ∀ q,
      (if q.1 ≤ thr ∧ M ≤ q.2 then
          iter (relaxedBandStop r n lower target) T q0 q else 0) ≤
        (if theta ≤ relaxedTheta w eta q then
          iter (relaxedBandStop r n lower target) T q0 q else 0) := by
    intro q
    by_cases hq : q.1 ≤ thr ∧ M ≤ q.2
    · have hle : theta ≤ relaxedTheta w eta q := by
        dsimp only [theta, relaxedTheta]
        exact mul_le_mul'
          (pow_le_pow_right_of_le_one' hw1 hq.1)
          (pow_le_pow_right₀ heta1 hq.2)
      simp [hq, hle]
    · simp [hq]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div
      (iter (relaxedBandStop r n lower target) T q0)
      (relaxedTheta w eta) theta htheta0 hthetatop) ?_
  have hiter :=
    expect_iter_le
      (relaxedBandStop r n lower target)
      (relaxedTheta w eta) 1
      (by
        simpa [w, eta] using
          relaxedBandStop_theta_super r n lower target bHi
            beta slack tau h3 htarget hband hslack htau hB hcorner)
      T q0
  have hthetaInit :
      relaxedTheta w eta q0 = w ^ q0.1 := by
    simp [relaxedTheta, hc0]
  rw [one_pow, one_mul, hthetaInit] at hiter
  dsimp only [theta]
  simpa [w, eta] using
    ENNReal.div_le_div_right hiter
      (w ^ thr * eta ^ M)

/-- Exact stage floor obtained from lower bounds on both species counts. -/
noncomputable def relaxedBandProductiveFloor
    (r : RelaxedRate) (n xLo yLo : ℕ) : ℝ≥0∞ :=
  (r.fire : ℝ≥0∞) *
    (((3 * (xLo * yLo) : ℕ) : ℝ≥0∞) /
      ((n * (n - 1) : ℕ) : ℝ≥0∞))

/-- The rectangular stage floor bounds the productive mass at every live
interior state. -/
theorem relaxedBandProductiveFloor_le
    (r : RelaxedRate)
    (n lower target yLo a b : ℕ)
    (h3 : 3 ≤ n) (hpop : a + b + 2 = n)
    (hyLo : target + yLo = n + 1)
    (ha : lower ≤ a) (ht : a + 1 < target) :
    relaxedBandProductiveFloor r n (lower + 1) yLo ≤
      relaxedTriStep r (a + 1) (b + 1) (by omega) a +
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) := by
  have hy : yLo ≤ b + 1 := by omega
  have hK :
      (lower + 1) * yLo ≤ (a + 1) * (b + 1) :=
    Nat.mul_le_mul (by omega) hy
  have hfloor :=
    relaxed_productive_mass_ge r a b n
      ((lower + 1) * yLo) h3 hpop hK
  have hden : a + b + 1 = n - 1 := by omega
  simpa [relaxedBandProductiveFloor, hden] using hfloor

/-- Vanishing counter potential for the two-boundary band chain. -/
theorem relaxedBandStop_count_super
    (r : RelaxedRate)
    (n lower target yLo : ℕ)
    (w p p' : ℝ≥0∞)
    (h3 : 3 ≤ n) (htarget : target ≤ n)
    (hyLo : target + yLo = n + 1)
    (hw : w ≤ 1) (hp : p + p' = 1)
    (hpFloor :
      p ≤ relaxedBandProductiveFloor r n (lower + 1) yLo) :
    ∀ q,
      expect (relaxedBandStop r n lower target q)
          (fun z =>
            if RelaxedBandBoundary lower target z then 0 else w ^ z.2) ≤
        (p' + p * w) *
          (if RelaxedBandBoundary lower target q then 0 else w ^ q.2) := by
  intro q
  by_cases hq : RelaxedBandBoundary lower target q
  · rw [relaxedBandStop, freeze_of_mem q hq, expect_pure]
    simp [hq]
  · rw [relaxedBandStop, freeze_of_not_mem q hq, if_neg hq]
    have hxlo : lower < q.1 := by
      unfold RelaxedBandBoundary at hq
      omega
    have hxhi : q.1 < target := by
      unfold RelaxedBandBoundary at hq
      omega
    obtain ⟨a, haEq⟩ : ∃ a, q.1 = a + 1 :=
      ⟨q.1 - 1, by omega⟩
    obtain ⟨b, hpop⟩ : ∃ b, a + b + 2 = n :=
      ⟨n - a - 2, by omega⟩
    have hprod :
        p ≤ relaxedTriStep r (a + 1) (b + 1) (by omega) a +
          relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) :=
      hpFloor.trans
        (relaxedBandProductiveFloor_le r n lower target yLo a b
          h3 hpop hyLo (by omega) (by omega))
    rw [show q = (a + 1, q.2) by ext <;> simp [haEq]]
    calc
      expect (relaxedCount r n (a + 1, q.2))
          (fun z =>
            if RelaxedBandBoundary lower target z then 0 else w ^ z.2)
          ≤ expect (relaxedCount r n (a + 1, q.2))
              (fun z => w ^ z.2) := by
            unfold expect
            exact ENNReal.tsum_le_tsum fun z =>
              mul_le_mul_left' (by
                change
                  (if RelaxedBandBoundary lower target z then 0
                    else w ^ z.2) ≤ w ^ z.2
                split_ifs <;> simp) _
      _ ≤ (p' + p * w) * w ^ q.2 :=
        relaxedCount_step_of_productive_lower
          r hpop h3 hp hw hprod

/-- Adapted lower tail for insufficient productive events while still live. -/
theorem relaxedBandStop_productivity_tail
    (r : RelaxedRate)
    (n lower target yLo T M : ℕ)
    (w p p' : ℝ≥0∞)
    (h3 : 3 ≤ n) (htarget : target ≤ n)
    (hyLo : target + yLo = n + 1)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hp : p + p' = 1)
    (hpFloor :
      p ≤ relaxedBandProductiveFloor r n (lower + 1) yLo)
    (q0 : ℕ × ℕ) :
    ∑' q, (if q.2 ≤ M ∧
        ¬ RelaxedBandBoundary lower target q then
        iter (relaxedBandStop r n lower target) T q0 q else 0) ≤
      (p' + p * w) ^ T *
        (if RelaxedBandBoundary lower target q0 then 0 else w ^ q0.2) /
          w ^ M := by
  exact count_tail_frozen
    (relaxedCount r n)
    (RelaxedBandBoundary lower target)
    Prod.snd w (p' + p * w) hw1 hw0
    (relaxedBandStop_count_super r n lower target yLo
      w p p' h3 htarget hyLo hw1 hp hpFloor)
    T M q0

/-- Set-cover split of failure to reach the upper boundary. -/
theorem relaxedBand_failure_split
    (r : RelaxedRate)
    (n lower target M T : ℕ) (q0 : ℕ × ℕ) :
    ∑' q, (if q.1 + 1 ≤ target then
        iter (relaxedBandStop r n lower target) T q0 q else 0) ≤
      (∑' q, (if q.1 ≤ lower then
          iter (relaxedBandStop r n lower target) T q0 q else 0)) +
      (∑' q, (if q.1 ≤ target - 1 ∧ M ≤ q.2 then
          iter (relaxedBandStop r n lower target) T q0 q else 0)) +
      (∑' q, (if lower + 1 ≤ q.1 ∧ q.1 + 1 ≤ target ∧ q.2 < M then
          iter (relaxedBandStop r n lower target) T q0 q else 0)) := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun q => ?_
  set mass := iter (relaxedBandStop r n lower target) T q0 q
  by_cases hfail : q.1 + 1 ≤ target
  · rw [if_pos hfail]
    by_cases hruin : q.1 ≤ lower
    · rw [if_pos hruin]
      exact le_trans (self_le_add_right _ _) (self_le_add_right _ _)
    · rw [if_neg hruin]
      by_cases hm : M ≤ q.2
      · rw [if_pos ⟨by omega, hm⟩, zero_add]
        exact self_le_add_right _ _
      · rw [if_neg (by tauto),
          if_pos ⟨by omega, hfail, by omega⟩, zero_add, zero_add]
  · rw [if_neg hfail]
    positivity

/-- Forgetting the productive counter gives the physical two-boundary chain. -/
theorem relaxedBandStop_map_fst
    (r : RelaxedRate) (n lower target : ℕ) (q : ℕ × ℕ) :
    (relaxedBandStop r n lower target q).map Prod.fst =
      freeze (fun x : ℕ => x ≤ lower ∨ target ≤ x)
        (relaxedTriChain r n) q.1 := by
  by_cases hq : RelaxedBandBoundary lower target q
  · rw [relaxedBandStop, freeze_of_mem q hq,
      freeze_of_mem q.1 (by
        simpa [RelaxedBandBoundary] using hq),
      PMF.pure_map]
  · rw [relaxedBandStop, freeze_of_not_mem q hq,
      freeze_of_not_mem q.1 (by
        simpa [RelaxedBandBoundary] using hq)]
    exact relaxedCount_map_fst r n q

/-- Freezing the physical chain at the union of the boundaries is the same as
first freezing at upper success and then at lower ruin. -/
theorem relaxedStateBand_eq_doubleFreeze
    (r : RelaxedRate) (n lower target : ℕ) :
    freeze (fun x : ℕ => x ≤ lower ∨ target ≤ x)
        (relaxedTriChain r n) =
      freeze (fun x : ℕ => x ≤ lower)
        (freeze (fun x : ℕ => target ≤ x) (relaxedTriChain r n)) := by
  funext x
  by_cases hlo : x ≤ lower
  · rw [freeze_of_mem x (Or.inl hlo), freeze_of_mem x hlo]
  · by_cases hhi : target ≤ x
    · rw [freeze_of_mem x (Or.inr hhi), freeze_of_not_mem x hlo,
        freeze_of_mem x hhi]
    · rw [freeze_of_not_mem x (by tauto), freeze_of_not_mem x hlo,
        freeze_of_not_mem x hhi]

/-- The counted band ruin mass is the physical lower-first hitting
probability. -/
theorem relaxedBand_ruin_mass_eq_hitProb
    (r : RelaxedRate) (n lower target T : ℕ) (q0 : ℕ × ℕ) :
    ∑' q, (if q.1 ≤ lower then
        iter (relaxedBandStop r n lower target) T q0 q else 0) =
      hitProb (fun x : ℕ => x ≤ lower)
        (freeze (fun x : ℕ => target ≤ x) (relaxedTriChain r n))
        T q0.1 := by
  have hmap :
      (iter (relaxedBandStop r n lower target) T q0).map Prod.fst =
        iter
          (freeze (fun x : ℕ => x ≤ lower ∨ target ≤ x)
            (relaxedTriChain r n))
          T q0.1 :=
    iter_map_of_step_map _ _ Prod.fst
      (relaxedBandStop_map_fst r n lower target) T q0
  rw [relaxedStateBand_eq_doubleFreeze r n lower target] at hmap
  unfold hitProb
  rw [← hmap, expect_map]
  unfold expect ind
  refine tsum_congr fun q => ?_
  by_cases hq : q.1 ≤ lower <;>
    simp [hq]

/-- Concrete Feller bound for the ruin term of the counted band chain. -/
theorem relaxedBand_ruin_term_le
    (r : RelaxedRate) (beta : NNReal)
    (n lower target bHi gap T : ℕ)
    (h3 : 3 ≤ n) (hband : lower + bHi + 2 = n)
    (hbeta1 : 1 ≤ beta)
    (hcorner :
      beta * (bHi + 1 : NNReal) ≤
        r.fire * (lower + 1 : NNReal))
    (q0 : ℕ × ℕ) (hstart : q0.1 = lower + gap) :
    ∑' q, (if q.1 ≤ lower then
        iter (relaxedBandStop r n lower target) T q0 q else 0) ≤
      (beta : ℝ≥0∞)⁻¹ ^ gap := by
  rw [relaxedBand_ruin_mass_eq_hitProb, hstart]
  refine le_trans
    (le_iSup
      (fun t => hitProb (fun x : ℕ => x ≤ lower)
        (freeze (fun x : ℕ => target ≤ x) (relaxedTriChain r n))
        t (lower + gap)) T) ?_
  apply relaxed_band_feller_varying_beta
    r n lower target gap beta (fun _ => beta) h3 hbeta1
  intro a b hpop ha _
  refine ⟨le_rfl, ?_⟩
  have hb : b ≤ bHi := by omega
  exact relaxed_bias_on_region r beta ha hb hcorner

/-- The live few-productivity term is bounded by the frozen counter tail. -/
theorem relaxedBand_live_few_le
    (r : RelaxedRate)
    (n lower target yLo T M : ℕ)
    (w p p' : ℝ≥0∞)
    (h3 : 3 ≤ n) (htarget : target ≤ n)
    (hyLo : target + yLo = n + 1)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hp : p + p' = 1)
    (hpFloor :
      p ≤ relaxedBandProductiveFloor r n (lower + 1) yLo)
    (q0 : ℕ × ℕ) :
    ∑' q, (if lower + 1 ≤ q.1 ∧ q.1 + 1 ≤ target ∧ q.2 < M then
        iter (relaxedBandStop r n lower target) T q0 q else 0) ≤
      (p' + p * w) ^ T *
        (if RelaxedBandBoundary lower target q0 then 0 else w ^ q0.2) /
          w ^ M := by
  refine le_trans (ENNReal.tsum_le_tsum fun q => ?_)
    (relaxedBandStop_productivity_tail r n lower target yLo T M
      w p p' h3 htarget hyLo hw1 hw0 hp hpFloor q0)
  by_cases hq :
      lower + 1 ≤ q.1 ∧ q.1 + 1 ≤ target ∧ q.2 < M
  · rw [if_pos hq]
    have hnB : ¬ RelaxedBandBoundary lower target q := by
      unfold RelaxedBandBoundary
      omega
    rw [if_pos ⟨by omega, hnB⟩]
  · rw [if_neg hq]
    positivity

/-- Complete raw finite-stage failure estimate: Feller ruin, productive-event
direction, and adapted insufficient-productivity clock. -/
theorem relaxedBand_phase_fail
    (r : RelaxedRate)
    (n lower target bHi gap M T yLo : ℕ)
    (beta slack tau : NNReal)
    (wp p p' : ℝ≥0∞)
    (h3 : 3 ≤ n) (htarget : target ≤ n)
    (hband : lower + bHi + 2 = n)
    (hyLo : target + yLo = n + 1)
    (hbeta1 : 1 ≤ beta)
    (hslack : r.fire + slack ≤ beta)
    (htau : tau * (bHi : NNReal) ≤ slack)
    (hB : 1 < beta + tau)
    (hcorner :
      beta * (bHi + 1 : NNReal) ≤
        r.fire * (lower + 1 : NNReal))
    (hwp1 : wp ≤ 1) (hwp0 : wp ≠ 0) (hp : p + p' = 1)
    (hpFloor :
      p ≤ relaxedBandProductiveFloor r n (lower + 1) yLo)
    (q0 : ℕ × ℕ) (hstart : q0.1 = lower + gap)
    (hstartLive : lower < q0.1 ∧ q0.1 < target)
    (hc0 : q0.2 = 0) :
    ∑' q, (if q.1 + 1 ≤ target then
        iter (relaxedBandStop r n lower target) T q0 q else 0) ≤
      (beta : ℝ≥0∞)⁻¹ ^ gap +
      (relaxedDirW (beta + tau) : ℝ≥0∞) ^ q0.1 /
        ((relaxedDirW (beta + tau) : ℝ≥0∞) ^ (target - 1) *
          (relaxedDirEta (beta + tau) : ℝ≥0∞) ^ M) +
      (p' + p * wp) ^ T * 1 / wp ^ M := by
  refine (relaxedBand_failure_split r n lower target M T q0).trans ?_
  apply add_le_add
  · apply add_le_add
    · exact relaxedBand_ruin_term_le
        r beta n lower target bHi gap T h3 hband hbeta1 hcorner
        q0 hstart
    · exact relaxedBandStop_direction_tail
        r n lower target bHi (target - 1) M T beta slack tau
        h3 htarget hband hslack htau hB hcorner q0 hc0
  · simpa [hc0, show ¬ RelaxedBandBoundary lower target q0 by
        unfold RelaxedBandBoundary
        omega] using
      relaxedBand_live_few_le
        r n lower target yLo T M wp p p'
        h3 htarget hyLo hwp1 hwp0 hp hpFloor q0

end Tri

#print axioms Tri.relaxedBandStop_direction_tail
#print axioms Tri.relaxedBandProductiveFloor_le
#print axioms Tri.relaxedBandStop_productivity_tail
#print axioms Tri.relaxedBand_failure_split
#print axioms Tri.relaxedBand_phase_fail

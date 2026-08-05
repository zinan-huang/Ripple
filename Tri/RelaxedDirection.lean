/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedProgress

/-!
# Finite productive-event direction tail for unequal reaction rates

The strict odds available in a finite band are spent through the joint
potential `w^x * eta^count`. The chain is frozen only at the lower boundary;
keeping the full potential there is essential for the final Markov bound.
-/

namespace Tri

open scoped ENNReal

/-- A direct productive up/down odds bound gives the joint one-step
supermartingale with the exact direction parameters. -/
theorem relaxedCount_theta_super_of_odds
    (r : RelaxedRate) (B : NNReal)
    (n a b c : ℕ)
    (hpop : a + b + 2 = n) (h3 : 3 ≤ n)
    (hB : 1 < B)
    (hmass :
      (B : ℝ≥0∞) *
          relaxedTriStep r (a + 1) (b + 1) (by omega) a ≤
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) :
    expect (relaxedCount r n (a + 1, c))
        (relaxedTheta
          (relaxedDirW B : ℝ≥0∞)
          (relaxedDirEta B : ℝ≥0∞)) ≤
      relaxedTheta
        (relaxedDirW B : ℝ≥0∞)
        (relaxedDirEta B : ℝ≥0∞)
        (a + 1, c) := by
  let dn : ℝ≥0∞ :=
    relaxedTriStep r (a + 1) (b + 1) (by omega) a
  let neu : ℝ≥0∞ :=
    relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 1)
  let up : ℝ≥0∞ :=
    relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)
  let u : ℝ≥0∞ := (B : ℝ≥0∞)⁻¹
  let w : ℝ≥0∞ := relaxedDirW B
  let eta : ℝ≥0∞ := relaxedDirEta B
  have hsum : dn + neu + up = 1 := by
    dsimp only [dn, neu, up]
    exact relaxedTriStep_masses_sum r a (b + 1) (by omega)
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero]
    exact ne_of_gt (lt_trans zero_lt_one hB)
  have hBtop : (B : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hdle : dn ≤ up * u := by
    dsimp only [u]
    rw [← div_eq_mul_inv]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hB0) (Or.inl hBtop)).2
    simpa only [mul_comm, dn, up] using hmass
  have hrel : eta * (u + w ^ 2) = w * (u + 1) := by
    have hBpos : 0 < B := lt_trans zero_lt_one hB
    have hrelNN := relaxedDir_relation B hBpos
    dsimp only [eta, w, u]
    have hu :
        ((relaxedDirU B : NNReal) : ℝ≥0∞) =
          (B : ℝ≥0∞)⁻¹ := by
      unfold relaxedDirU
      rw [ENNReal.coe_div (ne_of_gt hBpos)]
      simp
    rw [← hu]
    exact_mod_cast hrelNN
  have hweta : w ≤ eta := by
    dsimp only [w, eta]
    exact_mod_cast relaxedDir_w_le_eta hB
  have hdt : dn ≠ ⊤ := by
    dsimp only [dn]
    exact PMF.apply_ne_top _ _
  have hnt : neu ≠ ⊤ := by
    dsimp only [neu]
    exact PMF.apply_ne_top _ _
  have hut : up ≠ ⊤ := by
    dsimp only [up]
    exact PMF.apply_ne_top _ _
  have hwt : w ≠ ⊤ := by finiteness
  have hetat : eta ≠ ⊤ := by finiteness
  have hutop : u ≠ ⊤ := ENNReal.inv_ne_top.mpr hB0
  have hscalar :
      neu * w + eta * (dn + up * w ^ 2) ≤ w :=
    doubleDir_scalar dn neu up u w eta
      hsum hdle hrel hweta hdt hnt hut hwt hetat hutop
  unfold relaxedTheta
  rw [relaxedCount_expect_level_count r n a b c hpop h3
    (fun L C => w ^ L * eta ^ C)]
  change
    dn * (w ^ a * eta ^ (c + 1)) +
        neu * (w ^ (a + 1) * eta ^ c) +
        up * (w ^ (a + 2) * eta ^ (c + 1)) ≤
      w ^ (a + 1) * eta ^ c
  calc
    dn * (w ^ a * eta ^ (c + 1)) +
          neu * (w ^ (a + 1) * eta ^ c) +
          up * (w ^ (a + 2) * eta ^ (c + 1))
        = (w ^ a * eta ^ c) *
            (neu * w + eta * (dn + up * w ^ 2)) := by
      rw [pow_succ eta c, pow_succ w a,
        show a + 2 = (a + 1) + 1 by omega,
        pow_succ w (a + 1)]
      ring
    _ ≤ (w ^ a * eta ^ c) * w := by
      simpa [mul_comm] using
        mul_le_mul_left hscalar (w ^ a * eta ^ c)
    _ = w ^ (a + 1) * eta ^ c := by
      rw [pow_succ w a]
      ring

/-- At or beyond the all-`X` endpoint, the counted relaxed chain is inert. -/
theorem relaxedCount_pure_of_n_le
    (r : RelaxedRate) (n x c : ℕ) (h3 : 3 ≤ n) (hnx : n ≤ x) :
    relaxedCount r n (x, c) = PMF.pure (x, c) := by
  have hchain : relaxedTriChain r n x = PMF.pure x := by
    by_cases hxn : x = n
    · subst x
      exact relaxedTriChain_consensus_X r h3
    · unfold relaxedTriChain
      rw [dif_neg]
      omega
  unfold relaxedCount
  rw [hchain, PMF.pure_map]
  simp

/-- Counted relaxed chain frozen after reaching the lower boundary. -/
noncomputable def relaxedDirStop
    (r : RelaxedRate) (n lower : ℕ) :
    ℕ × ℕ → PMF (ℕ × ℕ) := fun q =>
  if lower + 1 ≤ q.1 then relaxedCount r n q else PMF.pure q

/-- Uniform joint supermartingale throughout a rectangular majority region. -/
theorem relaxedDirStop_super
    (r : RelaxedRate)
    (n lower bHi : ℕ)
    (beta slack tau : NNReal)
    (h3 : 3 ≤ n)
    (hband : lower + bHi + 2 = n)
    (hslack : r.fire + slack ≤ beta)
    (htau : tau * (bHi : NNReal) ≤ slack)
    (hB : 1 < beta + tau)
    (hcorner :
      beta * (bHi + 1 : NNReal) ≤
        r.fire * (lower + 1 : NNReal)) :
    ∀ q,
      expect (relaxedDirStop r n lower q)
          (relaxedTheta
            (relaxedDirW (beta + tau) : ℝ≥0∞)
            (relaxedDirEta (beta + tau) : ℝ≥0∞)) ≤
        1 * relaxedTheta
          (relaxedDirW (beta + tau) : ℝ≥0∞)
          (relaxedDirEta (beta + tau) : ℝ≥0∞)
          q := by
  rintro ⟨x, c⟩
  rw [one_mul]
  unfold relaxedDirStop
  split_ifs with hlive
  · by_cases hxn : x < n
    · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 :=
        ⟨x - 1, by omega⟩
      obtain ⟨b, hpop⟩ : ∃ b, a + b + 2 = n :=
        ⟨n - a - 2, by omega⟩
      have ha : lower ≤ a := by omega
      have hb : b ≤ bHi := by omega
      have hbias :
          beta * (b + 1 : NNReal) ≤
            r.fire * (a + 1 : NNReal) :=
        relaxed_bias_on_region r beta ha hb hcorner
      have hmass :=
        relaxedTriStep_mass_bias_strong_on_band
          r (by omega) hslack hbias hb htau
      exact relaxedCount_theta_super_of_odds
        r (beta + tau) n a b c hpop h3 hB hmass
    · rw [relaxedCount_pure_of_n_le r n x c h3 (by omega), expect_pure]
  · rw [expect_pure]

/-- Finite-time wrong-direction tail with a productive-event threshold. -/
theorem relaxedDirStop_tail
    (r : RelaxedRate)
    (n lower bHi thr M T : ℕ)
    (beta slack tau : NNReal)
    (h3 : 3 ≤ n)
    (hband : lower + bHi + 2 = n)
    (hslack : r.fire + slack ≤ beta)
    (htau : tau * (bHi : NNReal) ≤ slack)
    (hB : 1 < beta + tau)
    (hcorner :
      beta * (bHi + 1 : NNReal) ≤
        r.fire * (lower + 1 : NNReal))
    (q0 : ℕ × ℕ) (hc0 : q0.2 = 0) :
    ∑' q, (if q.1 ≤ thr ∧ M ≤ q.2 then
        iter (relaxedDirStop r n lower) T q0 q else 0) ≤
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
    exact ne_of_gt (by
      unfold relaxedDirW
      positivity)
  have heta1 : 1 ≤ eta := by
    dsimp only [eta]
    exact_mod_cast le_of_lt (relaxedDir_eta_gt_one hB)
  have hwt : w ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hetat : eta ≠ ⊤ := by finiteness
  let theta : ℝ≥0∞ := w ^ thr * eta ^ M
  have htheta0 : theta ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ hw0)
    exact pow_ne_zero _ (by
      intro heta0
      rw [heta0] at heta1
      simp at heta1)
  have hthetatop : theta ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt)
      (ENNReal.pow_ne_top hetat)
  have hsub : ∀ q,
      (if q.1 ≤ thr ∧ M ≤ q.2 then
          iter (relaxedDirStop r n lower) T q0 q else 0) ≤
        (if theta ≤ relaxedTheta w eta q then
          iter (relaxedDirStop r n lower) T q0 q else 0) := by
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
      (iter (relaxedDirStop r n lower) T q0)
      (relaxedTheta w eta) theta htheta0 hthetatop) ?_
  have hiter :=
    expect_iter_le
      (relaxedDirStop r n lower)
      (relaxedTheta w eta) 1
      (by
        simpa [w, eta] using
          relaxedDirStop_super r n lower bHi beta slack tau
            h3 hband hslack htau hB hcorner)
      T q0
  have hthetaInit :
      relaxedTheta w eta q0 = w ^ q0.1 := by
    simp [relaxedTheta, hc0]
  rw [one_pow, one_mul, hthetaInit] at hiter
  dsimp only [theta]
  simpa [w, eta] using
    ENNReal.div_le_div_right hiter
      (w ^ thr * eta ^ M)

end Tri

#print axioms Tri.relaxedCount_theta_super_of_odds
#print axioms Tri.relaxedDirStop_super
#print axioms Tri.relaxedDirStop_tail

/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBCreation

/-!
# The creation potential is a supermartingale for the full seven-event kernel

`Tri/SingleBCreation.lean` proved the per-event behaviour and the scalar
content. This file assembles them into the one-step inequality

```text
expect (singleLedgerStep n hn q) (creationG lam) ≤ creationG lam q
```

## The assembly avoids truncated subtraction entirely

The obvious route — "five inert terms give `1 − 2p`, then apply the real
scalar step" — forces `1 − 2p` in `ℝ≥0∞`, where subtraction is truncated and
every step needs a side condition.

There is no need. Write `S` for the total mass of the five non-creation events
and `p` for each creation's mass. The kernel is a PMF, so

```text
S + p + p = 1
```

and the goal `S·G + p·G·E₊ + p·G·E₋ ≤ G` becomes, after factoring `G`,

```text
S + p·E₊ + p·E₋  ≤  S + 2p
```

which reduces by `add_le_add_left` to `p·(E₊ + E₋) ≤ p·2`, i.e. to

```text
E₊ + E₋ ≤ 2
```

alone. No subtraction, truncated or otherwise, and the fairness enters exactly
once — in the step where both creation masses are written as the same `p`.
-/

namespace Tri

open scoped ENNReal

/-- The real content, extracted: the two compensated creation factors sum to
at most `2`.  This is the fair Rademacher MGF with the compensator moved to
the other side. -/
theorem creation_exp_sum_le_two (lam : ℝ) :
    Real.exp (lam - lam ^ 2 / 2) + Real.exp (-lam - lam ^ 2 / 2) ≤ 2 := by
  have hrad := rademacher_mgf_le lam
  have hEpos : 0 < Real.exp (lam ^ 2 / 2) := Real.exp_pos _
  have hsplit : Real.exp (lam - lam ^ 2 / 2)
      = Real.exp lam * (Real.exp (lam ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  have hsplit' : Real.exp (-lam - lam ^ 2 / 2)
      = Real.exp (-lam) * (Real.exp (lam ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  rw [hsplit, hsplit', ← add_mul]
  rw [mul_inv_le_iff₀ hEpos]
  linarith [hrad]

/-- The `ℝ≥0∞` form of the same. -/
theorem creationFactor_sum_le_two (lam : ℝ) :
    ENNReal.ofReal (Real.exp (lam - lam ^ 2 / 2))
        + ENNReal.ofReal (Real.exp (-lam - lam ^ 2 / 2))
      ≤ 2 := by
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
  calc ENNReal.ofReal (Real.exp (lam - lam ^ 2 / 2)
          + Real.exp (-lam - lam ^ 2 / 2))
      ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (creation_exp_sum_le_two lam)
    _ = 2 := by norm_num

/-- Expectation against a `Fintype`-supported PMF is a `Finset.sum`. -/
theorem expect_fintype {α : Type*} [Fintype α] (p : PMF α) (V : α → ℝ≥0∞) :
    expect p V = ∑ k, p k * V k := by
  unfold expect
  exact tsum_fintype _

/-- The ledger step's expectation, pushed onto the event alphabet. -/
theorem expect_singleLedgerStep (n : ℕ) (hn : 2 ≤ n) (q : SingleLedger n)
    (W : SingleLedger n → ℝ≥0∞) :
    expect (singleLedgerStep n hn q) W
      = ∑ k : SingleComp,
          singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b (by
            have h := q.cfg.2
            simp only [BiCfg.DoubleInv] at h
            omega) k
            * W (SingleComp.nextSingleLedger q k) := by
  unfold singleLedgerStep
  rw [expect_map, expect_fintype]

/-- The event alphabet expanded, so the five inert terms can be collected. -/
theorem singleComp_sum_expand (F : SingleComp → ℝ≥0∞) :
    ∑ k : SingleComp, F k
      = (F .xx + F .yy + F .bb + F .xb + F .yb) + (F .xyToX + F .xyToY) := by
  rw [show (Finset.univ : Finset SingleComp) =
    {SingleComp.xx, SingleComp.xyToX, SingleComp.xyToY, SingleComp.yy,
      SingleComp.xb, SingleComp.yb, SingleComp.bb} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- The two creation factors, as `ℝ≥0∞` multipliers of the potential. -/
theorem creationG_xyToX {n : ℕ} (lam : ℝ) (q : SingleLedger n)
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b
      SingleComp.xyToX ≠ 0) :
    creationG lam (SingleComp.nextSingleLedger q SingleComp.xyToX)
      = creationG lam q * ENNReal.ofReal (Real.exp (lam - lam ^ 2 / 2)) := by
  unfold creationG
  rw [creationExp_xyToX lam q hw, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]

theorem creationG_xyToY {n : ℕ} (lam : ℝ) (q : SingleLedger n)
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b
      SingleComp.xyToY ≠ 0) :
    creationG lam (SingleComp.nextSingleLedger q SingleComp.xyToY)
      = creationG lam q * ENNReal.ofReal (Real.exp (-lam - lam ^ 2 / 2)) := by
  unfold creationG
  rw [creationExp_xyToY lam q hw, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- **The supermartingale step for the full seven-event Single-B kernel.**

The five non-creation events fix the potential; the two creations, which carry
EQUAL mass, multiply it by `E₊` and `E₋`.  Since the masses sum to one, the
inequality collapses to `E₊ + E₋ ≤ 2` with no subtraction anywhere. -/
theorem creationG_step (n : ℕ) (hn : 2 ≤ n) (lam : ℝ) (q : SingleLedger n) :
    expect (singleLedgerStep n hn q) (creationG lam) ≤ creationG lam q := by
  have hq2 : 2 ≤ q.cfg.1.x + q.cfg.1.y + q.cfg.1.b := by
    have h := q.cfg.2
    simp only [BiCfg.DoubleInv] at h
    omega
  rw [expect_singleLedgerStep, singleComp_sum_expand]
  set P := singleCompPMF q.cfg.1.x q.cfg.1.y q.cfg.1.b hq2 with hP
  set G := creationG lam q with hG
  -- the five non-creation events fix the potential
  rw [creationG_of_noncreation lam q SingleComp.xx (by decide) (by decide),
    creationG_of_noncreation lam q SingleComp.yy (by decide) (by decide),
    creationG_of_noncreation lam q SingleComp.bb (by decide) (by decide),
    creationG_of_noncreation lam q SingleComp.xb (by decide) (by decide),
    creationG_of_noncreation lam q SingleComp.yb (by decide) (by decide)]
  -- the masses sum to one
  have htotal : ∑ k : SingleComp, P k = 1 := by
    have h := PMF.tsum_coe P
    rwa [tsum_fintype] at h
  rw [singleComp_sum_expand] at htotal
  -- FAIRNESS, used exactly once: the two creation masses are the same
  have heq : P SingleComp.xyToY = P SingleComp.xyToX := rfl
  rw [heq] at htotal ⊢
  by_cases hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b
      SingleComp.xyToX = 0
  · -- degenerate: no creation is possible, so both creation terms vanish
    have hp0 : P SingleComp.xyToX = 0 := by
      rw [hP, singleCompPMF_apply, hw]
      simp
    rw [hp0] at htotal ⊢
    simp only [zero_mul, add_zero] at htotal ⊢
    refine le_of_eq ?_
    calc P SingleComp.xx * G + P SingleComp.yy * G + P SingleComp.bb * G
            + P SingleComp.xb * G + P SingleComp.yb * G
        = (P SingleComp.xx + P SingleComp.yy + P SingleComp.bb
            + P SingleComp.xb + P SingleComp.yb) * G := by ring
      _ = 1 * G := by rw [htotal]
      _ = G := one_mul _
  · -- live: both creations are possible and carry the same mass
    have hw' : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b
        SingleComp.xyToY ≠ 0 := by
      rw [← singleComp_creation_weight_eq]; exact hw
    rw [creationG_xyToX lam q hw, creationG_xyToY lam q hw']
    have hGsplit : G = (P SingleComp.xx + P SingleComp.yy + P SingleComp.bb
        + P SingleComp.xb + P SingleComp.yb) * G
        + (P SingleComp.xyToX + P SingleComp.xyToX) * G := by
      rw [← add_mul, htotal, one_mul]
    calc P SingleComp.xx * G + P SingleComp.yy * G + P SingleComp.bb * G
            + P SingleComp.xb * G + P SingleComp.yb * G
          + (P SingleComp.xyToX
              * (G * ENNReal.ofReal (Real.exp (lam - lam ^ 2 / 2)))
            + P SingleComp.xyToX
              * (G * ENNReal.ofReal (Real.exp (-lam - lam ^ 2 / 2))))
        = (P SingleComp.xx + P SingleComp.yy + P SingleComp.bb
            + P SingleComp.xb + P SingleComp.yb) * G
          + P SingleComp.xyToX * G
            * (ENNReal.ofReal (Real.exp (lam - lam ^ 2 / 2))
              + ENNReal.ofReal (Real.exp (-lam - lam ^ 2 / 2))) := by ring
      _ ≤ (P SingleComp.xx + P SingleComp.yy + P SingleComp.bb
            + P SingleComp.xb + P SingleComp.yb) * G
          + P SingleComp.xyToX * G * 2 :=
        by gcongr
           exact creationFactor_sum_le_two lam
      _ = (P SingleComp.xx + P SingleComp.yy + P SingleComp.bb
            + P SingleComp.xb + P SingleComp.yb) * G
          + (P SingleComp.xyToX + P SingleComp.xyToX) * G := by ring
      _ = G := hGsplit.symm

/-- **The iterated bound**, with contraction factor exactly `1` — the walk is
fair, so the compensated potential is a martingale up to the compensator and
nothing decays. -/
theorem creationG_iter_le (n : ℕ) (hn : 2 ≤ n) (lam : ℝ) (T : ℕ)
    (q : SingleLedger n) :
    expect (iter (singleLedgerStep n hn) T q) (creationG lam)
      ≤ creationG lam q := by
  have h := expect_iter_le (singleLedgerStep n hn) (creationG lam) 1
    (fun s => by simpa using creationG_step n hn lam s) T q
  simpa using h

/-- **The Markov tail for the creation imbalance.**  The mass of ledgers whose
compensated potential has reached `θ` after `T` events is at most `G(q)/θ`.

Instantiating `θ = ofReal (exp (λ·D − λ²/2·H))` and optimising `λ` gives the
deviation bound `CX − CY ≥ D` needs; the creation-count bound `H` is what the
blank ledger supplies. -/
theorem creationG_markov (n : ℕ) (hn : 2 ≤ n) (lam : ℝ) (T : ℕ)
    (q : SingleLedger n) (θ : ℝ≥0∞) (hθ : θ ≠ 0) (htop : θ ≠ ⊤) :
    ∑' z, (if θ ≤ creationG lam z then
        iter (singleLedgerStep n hn) T q z else 0)
      ≤ creationG lam q / θ := by
  refine le_trans (markov_div (iter (singleLedgerStep n hn) T q)
    (creationG lam) θ hθ htop) ?_
  exact ENNReal.div_le_div_right (creationG_iter_le n hn lam T q) θ

end Tri

#print axioms Tri.creation_exp_sum_le_two
#print axioms Tri.creationFactor_sum_le_two
#print axioms Tri.expect_fintype
#print axioms Tri.expect_singleLedgerStep
#print axioms Tri.singleComp_sum_expand
#print axioms Tri.creationG_xyToX
#print axioms Tri.creationG_step
#print axioms Tri.creationG_iter_le
#print axioms Tri.creationG_markov

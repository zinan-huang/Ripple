/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# UniformRoleSplitMilestoneInstance — concrete `UniformRoleSplitMilestone`

Packages the scattered scalar ingredients in the codebase into a concrete
`UniformRoleSplitMilestone` instance.

## The construction

The `MilestonePhase` inside the bundle uses:
  * **milestones**: the `phase0Milestone` family from `Analysis/Phase0Convergence.lean`
    (the `n−1` mcrCount-threshold decrements of Stage 1);
  * **rates**: `floorRate n 1 (n − i)` — the floor-driven rates from
    `RoleSplitConcentration` with floor parameter `a₀ = 1`.  These are valid
    LOWER bounds on the true progress `phase0MilestoneProb n i = M(M−1)/(n(n−1))`
    since `M·1 ≤ M(M−1)` for `M ≥ 2`;
  * **progress**: weakened from `phase0MilestonePhase.progress` via the rate
    domination above.

The resulting `pMin · meanTime = ∑ 2/(n−i) = 2·(H_n − 1) ≥ log n` for `n ≥ 8`,
giving the `O(1/n²)` Janson tail.

## The `post_sound` bridge

`phase0MilestonePhase.Post` gives `mcrCount ≤ 1`, NOT `RoleSplitGood` (which
additionally requires `roleMCRCount = 0` AND the count windows).  The
`post_sound` field is therefore supplied as a carried hypothesis
`PostSoundBridge`.  This is the precise irreducible gap between the Janson
hitting-time engine and the full `RoleSplitGood` postcondition.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.UniformRoleSplitMilestone
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Phase0Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase2TimeConvergence

namespace ExactMajority
namespace RoleSplitConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Step 1: the floor-driven `MilestonePhase` on plain `Config`.

Same milestones as `phase0MilestonePhase`, but with the weaker floor rates
`floorRate n 1 (n − i)` that give the `Θ(log n)` potential. -/

/-- Floor-driven milestone phase: `phase0MilestonePhase` milestones with the
floor-driven rates `floorRate n 1 (n − i)`.  The rates are valid lower bounds
on the true progress because `M ≥ 2` implies `M·1 ≤ M·(M−1)`. -/
noncomputable def floorDrivenMilestonePhase (n : ℕ) (hn2 : 2 ≤ n) :
    MilestonePhase (NonuniformMajority L K) where
  k := n - 1
  milestone i := ExactMajority.phase0Milestone n ⟨i.val, by omega⟩
  p i := floorRate n 1 (n - i.val)
  hp_pos i := by
    have hM : 2 ≤ n - i.val := by have := i.isLt; omega
    exact floorRate_pos (n := n) (a₀ := 1) (M := n - i.val) hn2 (by omega) (by omega)
  hp_le_one i := by
    have hM : n - i.val ≤ n := by omega
    exact floorRate_le_one (n := n) (a₀ := 1) (M := n - i.val) hn2 hM (by omega)
  milestone_monotone i c c' hmono hsupp :=
    (phase0MilestonePhase (L := L) (K := K) n hn2).milestone_monotone i c c' hmono hsupp
  progress i c hprev hnot := by
    -- The true progress rate is `phase0MilestoneProb n i = M(M-1)/(n(n-1))`
    -- where M = n - i.val.  `floorRate n 1 M = M/(n(n-1)) ≤ M(M-1)/(n(n-1))`.
    have htrue := (phase0MilestonePhase (L := L) (K := K) n hn2).progress i c hprev hnot
    -- htrue : ... ≥ ENNReal.ofReal (phase0MilestoneProb n i)
    -- goal  : ... ≥ ENNReal.ofReal (floorRate n 1 (n - i.val))
    refine le_trans ?_ htrue
    apply ENNReal.ofReal_le_ofReal
    -- floorRate n 1 (n - i.val) ≤ phase0MilestoneProb n i
    -- i.e., M·1/(n(n-1)) ≤ M(M-1)/(n(n-1)) where M = n - i.val ≥ 2
    have hilt : i.val < n - 1 := i.isLt
    have hMge2 : 2 ≤ n - i.val := by omega
    -- phase0MilestonePhase.p i = phase0MilestoneProb n i (by rfl), and
    -- our rate = floorRate n 1 (n - i.val).
    -- Both are of the form _/(n*(n-1)), so we compare numerators.
    unfold floorRate
    show (((n - i.val) * 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤
      ExactMajority.phase0MilestoneProb n i
    unfold ExactMajority.phase0MilestoneProb
    simp only [Nat.mul_one]
    have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      nlinarith
    apply div_le_div_of_nonneg_right _ (le_of_lt hden_pos)
    -- ((n - i.val : ℕ) : ℝ) ≤ (n-1-i.val+1) * ((n-1-i.val+1)-1) = M*(M-1)
    set M := (n - 1 - i.val + 1 : ℕ) with hM_def
    have hMeq : (n - i.val : ℕ) = M := by omega
    rw [show ((n - i.val : ℕ) : ℝ) = (M : ℝ) from by rw [hMeq]]
    have hMge2' : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 2 ≤ M by omega)
    have hMm1 : (1 : ℝ) ≤ ((M : ℝ) - 1) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hMm1 (by linarith : (0 : ℝ) ≤ (M : ℝ))]

/-! ## Step 2: the `(k, p)` values match `roleSplitKernelMilestone` with `a₀ = 1`.

This means `pMin` and `meanTime` are identical, so all the scalar proofs
transfer. -/

theorem floorDrivenMilestonePhase_k (n : ℕ) (hn2 : 2 ≤ n) :
    (floorDrivenMilestonePhase (L := L) (K := K) n hn2).k = n - 1 := rfl

theorem floorDrivenMilestonePhase_p (n : ℕ) (hn2 : 2 ≤ n) (i : Fin (n - 1)) :
    (floorDrivenMilestonePhase (L := L) (K := K) n hn2).p i =
      floorRate n 1 (n - i.val) := rfl

/-- `pMin` of the floor-driven milestone phase equals `floorRate n 1 2 = 2/(n(n−1))`,
identical to `roleSplitKernelMilestone_pMin_eq` with `a₀ = 1`. -/
theorem floorDrivenMilestonePhase_pMin (n : ℕ) (hn2 : 2 ≤ n) :
    (floorDrivenMilestonePhase (L := L) (K := K) n hn2).pMin =
      floorRate n 1 2 := by
  set mp := floorDrivenMilestonePhase (L := L) (K := K) n hn2
  have hk : mp.k = n - 1 := rfl
  have hlt : n - 2 < n - 1 := by omega
  set i₀ : Fin mp.k := ⟨n - 2, by rw [hk]; exact hlt⟩
  haveI : Nonempty (Fin mp.k) := ⟨i₀⟩
  refine le_antisymm ?_ ?_
  · -- pMin ≤ p i₀ = floorRate n 1 2
    have hpi₀ : mp.p i₀ = floorRate n 1 2 := by
      show floorRate n 1 (n - i₀.val) = floorRate n 1 2
      simp only [i₀]
      congr 1; omega
    rw [← hpi₀]
    exact ciInf_le ⟨0, fun _ ⟨j, hj⟩ => hj ▸ le_of_lt (mp.hp_pos j)⟩ i₀
  · -- pMin ≥ floorRate n 1 2: every p i ≥ floorRate n 1 2
    unfold MilestonePhase.pMin
    apply le_ciInf
    intro i
    show floorRate n 1 2 ≤ floorRate n 1 (n - i.val)
    have hMge2 : 2 ≤ n - i.val := by have := i.isLt; omega
    exact floorRate_mono hn2 hMge2

/-- `pMin · meanTime` of the floor-driven phase = `∑ 2/(n−i)`, the same closed
form as `roleSplitKernelMilestone_pMin_meanTime` with `a₀ = 1`. -/
theorem floorDrivenMilestonePhase_pMin_meanTime (n : ℕ) (hn2 : 2 ≤ n) :
    (floorDrivenMilestonePhase (L := L) (K := K) n hn2).pMin *
      (floorDrivenMilestonePhase (L := L) (K := K) n hn2).meanTime =
      ∑ i : Fin (n - 1), (2 : ℝ) / ((n : ℝ) - (i.val : ℝ)) := by
  rw [floorDrivenMilestonePhase_pMin]
  unfold MilestonePhase.meanTime
  rw [Finset.mul_sum]
  have hdenpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    nlinarith
  apply Finset.sum_congr rfl
  intro i _
  have hile : i.val < n - 1 := i.isLt
  have hMge2 : 2 ≤ n - i.val := by omega
  have hMreal : ((n - i.val : ℕ) : ℝ) = (n : ℝ) - (i.val : ℝ) := by
    push_cast [Nat.cast_sub (by omega : i.val ≤ n)]; ring
  show floorRate n 1 2 * (floorRate n 1 (n - i.val))⁻¹ = 2 / ((n : ℝ) - (i.val : ℝ))
  have hMrpos : (0 : ℝ) < (n : ℝ) - (i.val : ℝ) := by rw [← hMreal]; positivity
  have hnum2 : (((2 * 1 : ℕ)) : ℝ) = 2 := by push_cast; ring
  have hnumM : (((n - i.val) * 1 : ℕ) : ℝ) = ((n : ℝ) - (i.val : ℝ)) := by
    rw [Nat.mul_one, hMreal]
  have hfr2 : floorRate n 1 2 = 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    unfold floorRate; rw [hnum2]
  have hfrM : floorRate n 1 (n - i.val) =
      ((n : ℝ) - (i.val : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    unfold floorRate; rw [hnumM]
  rw [hfr2, hfrM, inv_div, div_mul_div_comm]
  rw [div_eq_div_iff (by positivity) (ne_of_gt hMrpos)]
  ring

/-! ## Step 3: the potential `log n ≤ pMin · meanTime`.

From `Phase2Time.log_le_sum_inv`: `log(M+1) ≤ ∑_{m=0}^{M-1} 1/(m+1)`.
We show `log n ≤ 2·∑_{m=2}^{n} 1/m = pMin · meanTime` for `n ≥ 8`. -/

/-- `log n ≤ pMin · meanTime` for the floor-driven phase, valid for `n ≥ 8`.

The bound is: `log n ≤ 2·(H_n − 1) = pMin · meanTime`. -/
theorem floorDrivenMilestonePhase_potential (n : ℕ) (hn8 : 8 ≤ n) :
    Real.log (n : ℝ) ≤
      (floorDrivenMilestonePhase (L := L) (K := K) n (by omega)).pMin *
        (floorDrivenMilestonePhase (L := L) (K := K) n (by omega)).meanTime := by
  rw [floorDrivenMilestonePhase_pMin_meanTime]
  -- pMin · meanTime = ∑_{i:Fin(n-1)} 2/(n-i)
  -- ∑ 2/(n-i) = 2 · ∑ 1/(n-i) = 2 · ∑_{M=2}^{n} 1/M = 2·(H_n - 1)
  -- We need log n ≤ 2·(H_n - 1).
  -- From `log_le_sum_inv (n-1)`: log n ≤ H_{n-1} = ∑_{m=1}^{n-1} 1/m.
  -- Since H_{n-1} ≤ H_n = 1 + ∑_{m=2}^{n} 1/m and log n ≥ 2 for n ≥ 8:
  -- 2·(H_n - 1) = 2·∑_{m=2}^{n} 1/m ≥ 2·(H_{n-1} - 1) ≥ 2·(log n - 1) = 2·log n - 2 ≥ log n.
  --
  -- Strategy: convert the Fin sum to 2 times a Finset.range sum, then use
  -- `log_le_sum_inv`.
  --
  -- We work through the chain of inequalities directly.
  have hlog_le_harmonic := Phase2Time.log_le_sum_inv (n - 1)
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; ring
  rw [hcast] at hlog_le_harmonic
  -- hlog_le_harmonic : log n ≤ ∑_{m∈range(n-1)} 1/(m+1)
  -- For n ≥ 8, log n ≥ 2, so log n ≤ 2·log n − 2 ≤ 2·(H_{n-1} − 1)
  -- ≤ 2·∑_{m=1}^{n-1} 1/m − 2.
  -- But we need ≤ ∑ 2/(n-i).
  -- Direct: each term 2/(n-i) for i=0..n-2 corresponds to 2/M for M=2..n.
  -- ∑ 2/M = 2·∑_{M=2}^{n} 1/M ≥ 2·∑_{m=2}^{n-1} 1/m = 2·(H_{n-1} - 1).
  -- So ∑ 2/(n-i) ≥ 2·(H_{n-1} - 1) ≥ 2·(log n - 1) = 2·log n - 2 ≥ log n.
  -- (Last: log n ≥ 2.)
  have hlog8 : (2 : ℝ) ≤ Real.log (n : ℝ) := by
    have h8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
    -- exp 2 < 8 (since e ≈ 2.718, e² ≈ 7.389 < 8), so log 8 > 2.
    have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hexp2_eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    -- exp 2 < 8: numerically true (e² ≈ 7.389 < 8).
    -- Equivalent to 2 < 3·log 2, i.e., log 2 > 2/3.
    -- Proved via repeated application of `one_sub_inv_le_log`:
    -- log 2 = log(3/2) + log(4/3) ≥ (1 - 2/3) + (1 - 3/4) = 1/3 + 1/4 = 7/12 < 2/3.
    -- Need one more split:
    -- log 2 = log(3/2) + log(4/3) ≥ 1/3 + 1/4 = 7/12.
    -- Not enough.  Use integral lower bound on individual pieces:
    -- log(3/2) ≥ ∫₁^{3/2} dt/t ≥ (1/2)·(2/3) = 1/3  (rectangle at right endpoint).
    -- Actually `one_sub_inv_le_log` at x = 3/2 gives 1/3 ≤ log(3/2), and at x = 4/3
    -- gives 1/4 ≤ log(4/3).  So log 2 ≥ 7/12.
    -- To get log 2 > 2/3: use three splits.
    -- log 2 = log(9/8) + log(8/7) + log(7/6) + log(6/5) + log(5/4) + log(4/3) + log(3/2)
    -- ≥ 1/9 + 1/8 + 1/7 + 1/6 + 1/5 + 1/4 + 1/3
    -- = (280 + 315 + 360 + 420 + 504 + 630 + 840) / 2520
    -- = 3349/2520 ≈ 1.329.
    -- Wait, that can't be right — log 2 < 1.
    -- ERROR: log 2 ≠ ∑ log(k/(k-1)) for k = 2..9.  That sum = log 9.
    -- Correct: log 2 = log(3/2) + log(4/3) = log 2.  ✓ (only TWO terms, 3/2 · 4/3 = 2).
    -- For more terms: 2 = (3/2)·(4/3) or 2 = (5/4)·(8/5) etc.
    -- 2 = (3/2)·(4/3) gives log 2 = log(3/2) + log(4/3) ≥ 1/3 + 1/4 = 7/12.
    -- Not enough.  Try: 2 = (4/3)·(3/2) with inner split:
    -- log(3/2) = log(7/6) + log(9/7) ≥ 1/7 + 2/9.  Hmm, 9/7 · 7/6 ≠ 3/2.
    -- Actually 3/2 = (3/2), log(3/2) = integral.
    -- Direct numerical sorry (will discharge with Mathlib `norm_num` or decide later).
    have hexp2_le : Real.exp 2 ≤ 8 := by
      -- exp 2 = (exp 1)² < 2.7182818286² < 7.39... < 8
      have hexp2_eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have h_e1_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h_sq_lt : (2.7182818286 : ℝ) * 2.7182818286 < 8 := by norm_num
      linarith [mul_le_mul h_e1_lt.le h_e1_lt.le (Real.exp_pos 1).le (by positivity : (0:ℝ) ≤ 2.7182818286)]
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log (n : ℝ) := by
          exact Real.log_le_log (Real.exp_pos 2) (le_trans hexp2_le h8)
  -- Lower bound: ∑_{i:Fin(n-1)} 2/(n - i) ≥ 2·(H_{n-1} - 1)
  -- H_{n-1} = ∑_{m∈range(n-1)} 1/(m+1)
  --         = 1 + ∑_{m∈range(n-2)} 1/(m+2)
  -- ∑_{i:Fin(n-1)} 1/(n-i) = ∑_{M=2}^{n} 1/M (by reflection M = n - i)
  --                         ≥ ∑_{m=2}^{n-1} 1/m = H_{n-1} - 1
  -- So ∑ 2/(n-i) ≥ 2·(H_{n-1} - 1) ≥ 2·(log n - 1) ≥ log n.
  suffices h : Real.log (n : ℝ) ≤ 2 * (∑ m ∈ Finset.range (n - 1), (1 : ℝ) / (↑m + 1) - 1) from by
    calc Real.log (n : ℝ)
        ≤ 2 * (∑ m ∈ Finset.range (n - 1), (1 : ℝ) / (↑m + 1) - 1) := h
      _ ≤ ∑ i : Fin (n - 1), (2 : ℝ) / ((n : ℝ) - (i.val : ℝ)) := by
          -- Strategy: rewrite both sides to range sums in a common form, then
          -- compare by peeling off the extra term.
          --
          -- Step A: Convert the Fin sum to a Finset.range sum.
          have hRHS : ∑ i : Fin (n - 1), (2 : ℝ) / ((n : ℝ) - (i.val : ℝ)) =
              ∑ j ∈ Finset.range (n - 1), (2 : ℝ) / ((n : ℝ) - (j : ℝ)) :=
            Fin.sum_univ_eq_sum_range (fun j => (2 : ℝ) / ((n : ℝ) - (j : ℝ))) (n - 1)
          rw [hRHS]
          -- Step B: Reflect: ∑_{i∈range(n-1)} 2/(n-i) = ∑_{j∈range(n-1)} 2/(j+2).
          have hrefl : ∑ j ∈ Finset.range (n - 1), (2 : ℝ) / ((n : ℝ) - (j : ℝ)) =
              ∑ j ∈ Finset.range (n - 1), (2 : ℝ) / ((j : ℝ) + 2) := by
            rw [← Finset.sum_range_reflect (fun j => (2 : ℝ) / ((j : ℝ) + 2))]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mem_range] at hj
            congr 1
            have hle : j ≤ n - 2 := by omega
            have hcalc : (((n - 1 - 1 - j : ℕ)) : ℝ) = (n : ℝ) - 2 - (j : ℝ) := by
              rw [show n - 1 - 1 - j = n - 2 - j from by omega]
              push_cast [Nat.cast_sub hle, Nat.cast_sub (show 2 ≤ n from by omega)]
              ring
            linarith
          rw [hrefl]
          -- Step C: Split H_{n-1} and simplify LHS.
          -- H_{n-1} = ∑_{m∈range(n-1)} 1/(m+1) = 1/(0+1) + ∑_{m∈range(n-2)} 1/(m+2)
          --         = 1 + ∑_{m∈range(n-2)} 1/(m+2)
          -- So 2*(H_{n-1} - 1) = 2*∑_{m∈range(n-2)} 1/(m+2) = ∑_{m∈range(n-2)} 2/(m+2).
          have hLHS : 2 * (∑ m ∈ Finset.range (n - 1), (1 : ℝ) / (↑m + 1) - 1) =
              ∑ m ∈ Finset.range (n - 2), (2 : ℝ) / ((m : ℝ) + 2) := by
            have hsplit : ∑ m ∈ Finset.range (n - 1), (1 : ℝ) / (↑m + 1) =
                1 + ∑ m ∈ Finset.range (n - 2), (1 : ℝ) / ((m : ℝ) + 2) := by
              conv_lhs =>
                rw [show n - 1 = (n - 2) + 1 from by omega]
                rw [Finset.sum_range_succ']
              -- LHS = 1/(↑0+1) + ∑_{k∈range(n-2)} 1/(↑(k+1)+1)
              -- RHS = 1 + ∑_{m∈range(n-2)} 1/(↑m+2)
              -- Rewrite the sum terms to match.
              have hterm : ∀ k ∈ Finset.range (n - 2),
                  (1 : ℝ) / (↑(k + 1) + 1) = 1 / ((k : ℝ) + 2) := by
                intro k _
                push_cast; ring
              rw [Finset.sum_congr rfl hterm]
              -- 1/(↑0+1) + ∑... = 1 + ∑...
              simp [add_comm]
            rw [hsplit]
            -- 2 * (1 + ∑... - 1) = 2 * ∑... = ∑ 2*...
            have : 1 + ∑ m ∈ Finset.range (n - 2), (1 : ℝ) / ((m : ℝ) + 2) - 1 =
                ∑ m ∈ Finset.range (n - 2), (1 : ℝ) / ((m : ℝ) + 2) := by ring
            rw [this, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _
            ring
          rw [hLHS]
          -- Step D: ∑_{m∈range(n-2)} 2/(m+2) ≤ ∑_{j∈range(n-1)} 2/(j+2)
          rw [show n - 1 = (n - 2) + 1 from by omega, Finset.sum_range_succ]
          linarith [show (0 : ℝ) ≤ 2 / (((n - 2 : ℕ) : ℝ) + 2) from by positivity]
  linarith

/-- `pMin · meanTime ≥ 0` (trivially, since both factors are positive). -/
theorem floorDrivenMilestonePhase_potential_nonneg (n : ℕ) (hn2 : 2 ≤ n) :
    0 ≤ (floorDrivenMilestonePhase (L := L) (K := K) n hn2).pMin *
      (floorDrivenMilestonePhase (L := L) (K := K) n hn2).meanTime := by
  apply mul_nonneg
  · rw [floorDrivenMilestonePhase_pMin]
    exact le_of_lt (floorRate_pos hn2 (by omega : 1 ≤ 2) (by omega : 1 ≤ 1))
  · unfold MilestonePhase.meanTime
    apply Finset.sum_nonneg
    intro i _
    exact le_of_lt (inv_pos_of_pos
      ((floorDrivenMilestonePhase (L := L) (K := K) n hn2).hp_pos i))

/-! ## Step 4: `pre_unhit` — Phase0Initial starts below all milestones. -/

/-- From `Phase0Initial`, no floor-driven milestone has been reached (all agents
are MCR, so `mcrCount = n > threshold` for every `i`). -/
theorem floorDrivenMilestonePhase_pre_unhit (n : ℕ) (hn2 : 2 ≤ n)
    (c₀ : Config (AgentState L K))
    (hinit : Phase0Initial (L := L) (K := K) n c₀) :
    ∀ i : Fin (floorDrivenMilestonePhase (L := L) (K := K) n hn2).k,
      ¬ (floorDrivenMilestonePhase (L := L) (K := K) n hn2).milestone i c₀ := by
  intro i
  -- The milestones are `phase0Milestone n ⟨i.val, ...⟩`, same as phase0MilestonePhase.
  change ¬ ExactMajority.phase0Milestone n ⟨i.val, by
    have := i.isLt; change i.val < n - 1 at this; omega⟩ c₀
  obtain ⟨hcard, hall⟩ := hinit
  have hmcr_eq : ExactMajority.mcrCount (L := L) (K := K) c₀ = n := by
    unfold ExactMajority.mcrCount
    rw [Multiset.filter_eq_self.mpr (fun a ha => (hall a ha).2)]
    exact hcard
  unfold ExactMajority.phase0Milestone
  simp only [not_or, not_exists, not_and, not_not, not_le, ne_eq]
  refine ⟨?_, hcard, ?_⟩
  · -- mcrCount = n > mcrThreshold n i
    have hilt : i.val < n - 1 := i.isLt
    have hthr : ExactMajority.mcrThreshold n ⟨i.val, by omega⟩ = n - 1 - i.val := rfl
    rw [hthr, hmcr_eq]; omega
  · intro a ha _
    have := (hall a ha).1
    simpa using congrArg Fin.val this

/-! ## Step 5: the `post_sound` bridge and the concrete instance.

The `post_sound` field bridges `phase0MilestonePhase.Post → RoleSplitGood`.
This is NOT derivable from the Janson milestone engine alone — it requires
the additional Chernoff count-window concentration (Lemma 5.2's full
role-split content).  We carry it as a hypothesis. -/

/-- The `post_sound` bridge: `floorDrivenMilestonePhase.Post c → RoleSplitGood η n c`.
This is the irreducible gap between the Janson hitting-time tail and the full
`RoleSplitGood` postcondition.  It comprises:
  * `mcrCount ≤ 1` (from `phase0MilestonePhase.Post`) to `roleMCRCount = 0`
    (the terminal MCR elimination);
  * the count windows `RoleSplitWindows η n c`.
-/
structure PostSoundBridge (η : ℝ) (n : ℕ) (hn2 : 2 ≤ n) : Prop where
  bridge :
    ∀ c : Config (AgentState L K),
      (floorDrivenMilestonePhase (L := L) (K := K) n hn2).Post c →
        RoleSplitGood (L := L) (K := K) η n c

/-- **Concrete `UniformRoleSplitMilestone`**, conditional on the `PostSoundBridge`.

Parameters:
  * `n ≥ 8` — population size (for the potential `log n ≤ pMin · meanTime`);
  * `η` — the role-split slack;
  * `PostSoundBridge η n` — the irreducible `Post → RoleSplitGood` hypothesis.
-/
noncomputable def uniformRoleSplitMilestoneInstance
    (η : ℝ) (n : ℕ) (hn8 : 8 ≤ n)
    (hps : PostSoundBridge (L := L) (K := K) η n (by omega)) :
    UniformRoleSplitMilestone (L := L) (K := K) η n where
  mp := floorDrivenMilestonePhase (L := L) (K := K) n (by omega)
  tRole := ⌈5 * (floorDrivenMilestonePhase (L := L) (K := K) n (by omega)).meanTime⌉₊
  post_sound := hps.bridge
  pre_unhit c₀ hinit :=
    floorDrivenMilestonePhase_pre_unhit (L := L) (K := K) n (by omega) c₀ hinit
  potential :=
    floorDrivenMilestonePhase_potential (L := L) (K := K) n hn8
  potential_nonneg :=
    floorDrivenMilestonePhase_potential_nonneg (L := L) (K := K) n (by omega)
  horizon := Nat.le_ceil _

end

#print axioms floorDrivenMilestonePhase
#print axioms floorDrivenMilestonePhase_pMin
#print axioms floorDrivenMilestonePhase_pMin_meanTime
#print axioms floorDrivenMilestonePhase_potential
#print axioms floorDrivenMilestonePhase_potential_nonneg
#print axioms floorDrivenMilestonePhase_pre_unhit
#print axioms uniformRoleSplitMilestoneInstance

end RoleSplitConcentration
end ExactMajority

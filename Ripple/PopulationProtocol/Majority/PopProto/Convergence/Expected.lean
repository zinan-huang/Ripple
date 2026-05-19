/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Expected Value Bridge

Connects the integer weighted drift (from Drift.lean) to the Bochner
integral over the step distribution PMF. This is the key lemma that
bridges the algebraic drift analysis to the probabilistic statement
needed for the multiplicative drift theorem.

## Main results

- `integral_stepDist_eq_sum`: The integral over `stepDist` equals a weighted
  sum over `State × State`, where the weights are the PMF probabilities.

- `interactionPMF_toReal`: PMF values in ℝ equal `count / totalPairs`.

## Dependencies

Requires `Mathlib.Probability.ProbabilityMassFunction.Integrals` for
`PMF.integral_eq_sum` (finite type expected value formula).
-/

import Ripple.PopulationProtocol.Majority.PopProto.Convergence.Drift
import Ripple.PopulationProtocol.Majority.PopProto.Probability.StepDist
import Ripple.PopulationProtocol.Majority.PopProto.Probability.MarkovChain
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace PopProto

open State MeasureTheory

/-! ### Measurable space instances for State

State is a finite type with 3 elements. We equip it with the discrete
σ-algebra so that all functions from State are measurable. -/

noncomputable instance instMeasurableSpaceState : MeasurableSpace State := ⊤

instance instDiscreteMeasurableSpaceState : DiscreteMeasurableSpace State where
  forall_measurableSet _ := trivial

namespace Config

variable {n : ℕ}

/-! ### Measurability helpers

With discrete σ-algebras on State and Config, all functions are measurable. -/

private theorem measurable_from_state {β : Type*} [MeasurableSpace β]
    (f : State × State → β) : Measurable f :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

private theorem measurable_from_config {β : Type*} [MeasurableSpace β]
    (f : Config n → β) : Measurable f :=
  fun _ _ => instDiscreteMeasurableSpaceConfig.forall_measurableSet _

/-! ### Integral over stepDist = sum over interactions -/

/-- The integral over `stepDist` equals a sum over interactions weighted by
    the interaction PMF. -/
theorem integral_stepDist_eq_sum (c : Config n) (hn : n ≥ 2) (f : Config n → ℝ) :
    ∫ c', f c' ∂(c.stepDist hn).toMeasure =
    ∑ p : State × State,
      ((c.interactionPMF hn) p).toReal • f (c.stepOrSelf p.1 p.2) := by
  unfold stepDist
  set g : State × State → Config n := fun p => c.stepOrSelf p.1 p.2
  -- (PMF.map g p).toMeasure = Measure.map g p.toMeasure
  rw [← PMF.toMeasure_map g _ (measurable_from_state g)]
  -- ∫ f d(map g μ) = ∫ (f ∘ g) dμ  [change of variables]
  rw [integral_map (measurable_from_state g).aemeasurable
      (measurable_from_config f).aestronglyMeasurable]
  -- ∫ (f ∘ g) d(pmf.toMeasure) = ∑ p, pmf(p).toReal • f(g(p))
  exact PMF.integral_eq_sum _ _

/-! ### PMF values as real rationals -/

/-- The `interactionPMF` value at `(s₁, s₂)` in `ℝ` is
    `interactionCount s₁ s₂ / totalPairs n`. -/
theorem interactionPMF_toReal (c : Config n) (hn : n ≥ 2) (s₁ s₂ : State) :
    ((c.interactionPMF hn) (s₁, s₂)).toReal =
    (c.interactionCount s₁ s₂ : ℝ) / (totalPairs n : ℝ) := by
  change (c.interactionProb hn s₁ s₂).toReal = _
  unfold interactionProb
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-! ### Factoring out 1/totalPairs

The PMF integral equals a weighted sum divided by `totalPairs n`. -/

/-- The integral over `stepDist` equals the weighted sum of `f` over
    interactions, divided by `totalPairs`. -/
theorem integral_stepDist_eq_weighted_div (c : Config n) (hn : n ≥ 2) (f : Config n → ℝ) :
    ∫ c', f c' ∂(c.stepDist hn).toMeasure =
    (∑ p : State × State,
      (c.interactionCount p.1 p.2 : ℝ) * f (c.stepOrSelf p.1 p.2)) /
    (totalPairs n : ℝ) := by
  rw [integral_stepDist_eq_sum]
  simp_rw [interactionPMF_toReal c hn, smul_eq_mul, div_mul_eq_mul_div]
  exact (Finset.sum_div _ _ _).symm

/-! ### Expected change = ℤ drift / totalPairs

We show E[ΔΦ] = (weighted_drift_ℤ : ℝ) / totalPairs, connecting the
Bochner integral to the integer algebra from Drift.lean. -/

/-- The ℝ sum of `count * (Φ(step) - Φ(c))` equals the ℤ weighted drift cast to ℝ. -/
private theorem real_drift_eq_int_cast (c : Config n) (Φ : Config n → ℕ) :
    (∑ p : State × State,
      (c.interactionCount p.1 p.2 : ℝ) *
      ((Φ (c.stepOrSelf p.1 p.2) : ℝ) - (Φ c : ℝ))) =
    ((∑ s₁ : State, ∑ s₂ : State,
      (c.interactionCount s₁ s₂ : ℤ) *
      ((Φ (c.stepOrSelf s₁ s₂) : ℤ) - (Φ c : ℤ))) : ℝ) := by
  push_cast
  rw [show (Finset.univ : Finset (State × State)) = Finset.univ ×ˢ Finset.univ
    from (Finset.univ_product_univ).symm]
  rw [Finset.sum_product]

/-- The weighted sum of `count * Φ(step)` splits into drift + totalPairs * Φ(c). -/
private theorem weighted_sum_split (c : Config n) (Φ : Config n → ℕ) :
    (∑ p : State × State,
      (c.interactionCount p.1 p.2 : ℝ) * (Φ (c.stepOrSelf p.1 p.2) : ℝ)) =
    (∑ p : State × State,
      (c.interactionCount p.1 p.2 : ℝ) *
      ((Φ (c.stepOrSelf p.1 p.2) : ℝ) - (Φ c : ℝ))) +
    (totalPairs n : ℝ) * (Φ c : ℝ) := by
  have hsum : (∑ p : State × State, (c.interactionCount p.1 p.2 : ℝ)) =
      (totalPairs n : ℝ) := by
    rw [show (Finset.univ : Finset (State × State)) = Finset.univ ×ˢ Finset.univ
      from (Finset.univ_product_univ).symm, Finset.sum_product]
    exact_mod_cast sum_interactionCount c
  -- Rewrite each term: count * Φ(step) = count * (Φ(step) - Φ(c)) + count * Φ(c)
  conv_lhs =>
    arg 2; ext p
    rw [show (c.interactionCount p.1 p.2 : ℝ) * (Φ (c.stepOrSelf p.1 p.2) : ℝ) =
        (c.interactionCount p.1 p.2 : ℝ) *
        ((Φ (c.stepOrSelf p.1 p.2) : ℝ) - (Φ c : ℝ)) +
        (c.interactionCount p.1 p.2 : ℝ) * (Φ c : ℝ) from by ring]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum]

/-- **Expected value bridge**: The integral of `Φ` under `stepDist` equals
    `(ℤ weighted drift) / totalPairs + Φ(c)`. -/
theorem integral_eq_drift_div_total_add (c : Config n) (hn : n ≥ 2) (Φ : Config n → ℕ) :
    ∫ c', (Φ c' : ℝ) ∂(c.stepDist hn).toMeasure =
    ((∑ s₁ : State, ∑ s₂ : State,
      (c.interactionCount s₁ s₂ : ℤ) *
      ((Φ (c.stepOrSelf s₁ s₂) : ℤ) - (Φ c : ℤ))) : ℝ) /
    (totalPairs n : ℝ) + (Φ c : ℝ) := by
  have htotal_ne : (totalPairs n : ℝ) ≠ 0 := by
    exact_mod_cast (totalPairs_pos hn).ne'
  rw [integral_stepDist_eq_weighted_div, weighted_sum_split, add_div,
      mul_div_cancel_left₀ _ htotal_ne, real_drift_eq_int_cast]

/-! ### Multiplicative drift in ℝ (large-x region)

Combining `integral_eq_drift_div_total_add` with `expected_decrease_potentialLargeX`
to obtain `E[Φ(C')] ≤ (1 - 13/(64(n-1))) · Φ(C)` in ℝ. -/

/-- **Multiplicative drift (large-x, ℝ version)**:
    `E[potentialLargeX(C')] ≤ (1 - 13/(64(n-1))) · potentialLargeX(C)`.

    This is the formal statement of the multiplicative drift condition
    (Lemma 7) for the large-x region. By the multiplicative drift theorem,
    the expected exit time from this region is O(n log n). -/
theorem expected_potentialLargeX_le (c : Config n) (hx : c.inLargeX) (hn : n ≥ 2)
    (hby : c.b_count + c.y_count ≥ 1) :
    ∫ c', (c'.potentialLargeX : ℝ) ∂(c.stepDist hn).toMeasure ≤
    (1 - 13 / (64 * ((n : ℝ) - 1))) * (c.potentialLargeX : ℝ) := by
  -- Step 1-2: integral = (drift + T*Φ) / T
  rw [integral_stepDist_eq_weighted_div, weighted_sum_split]
  have hT_ne : (totalPairs n : ℝ) ≠ 0 :=
    ne_of_gt (show (0 : ℝ) < _ from by exact_mod_cast totalPairs_pos hn)
  -- Step 3: simplify to drift/T + Φ
  rw [add_div, mul_div_cancel_left₀ _ hT_ne]
  -- Positivity facts
  have hT_pos : (0 : ℝ) < (totalPairs n : ℝ) := by exact_mod_cast totalPairs_pos hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hT_eq : (totalPairs n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    unfold totalPairs
    rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  -- Step 4: Bound the ℝ drift sum ≤ -13nΦ/64
  -- (Proved in a subgoal so casts don't leak into the main goal)
  have hD_le : (∑ p : State × State,
      (c.interactionCount p.1 p.2 : ℝ) *
      (((c.stepOrSelf p.1 p.2).potentialLargeX : ℝ) -
       (c.potentialLargeX : ℝ))) ≤
      -(13 * (n : ℝ) * (c.potentialLargeX : ℝ)) / 64 := by
    rw [real_drift_eq_int_cast c Config.potentialLargeX]
    rw [le_div_iff₀ (show (0 : ℝ) < 64 from by norm_num)]
    have hbound := expected_decrease_potentialLargeX c hx hn hby
    have hz : (∑ s₁ : State, ∑ s₂ : State,
        (c.interactionCount s₁ s₂ : ℤ) *
        (↑(c.stepOrSelf s₁ s₂).potentialLargeX -
         ↑c.potentialLargeX)) * 64 ≤
        -(13 * (n : ℤ) * ↑c.potentialLargeX) := by linarith
    exact_mod_cast hz
  -- Step 5: Abstract the ℝ drift sum
  set D := ∑ p : State × State, (c.interactionCount p.1 p.2 : ℝ) *
    (((c.stepOrSelf p.1 p.2).potentialLargeX : ℝ) -
     (c.potentialLargeX : ℝ))
  -- Step 6: Suffices D/T ≤ -(13/(64(n-1)))·Φ
  suffices hsuff : D / (totalPairs n : ℝ) ≤
      -(13 / (64 * ((n : ℝ) - 1))) * (c.potentialLargeX : ℝ) by
    have : (1 - 13 / (64 * ((n : ℝ) - 1))) * (c.potentialLargeX : ℝ) =
        (c.potentialLargeX : ℝ) -
        13 / (64 * ((n : ℝ) - 1)) * (c.potentialLargeX : ℝ) := by ring
    linarith
  -- Step 7: Clear fraction and simplify
  rw [div_le_iff₀ hT_pos]
  calc D ≤ -(13 * (n : ℝ) * (c.potentialLargeX : ℝ)) / 64 := hD_le
    _ = -(13 / (64 * ((n : ℝ) - 1))) * (c.potentialLargeX : ℝ) *
        (totalPairs n : ℝ) := by rw [hT_eq]; field_simp

/-! ### Multiplicative drift in ℝ (large-y region)

Symmetric version for `potentialLargeY = 3x + b + 1`. -/

/-- **Multiplicative drift (large-y, ℝ version)**:
    `E[potentialLargeY(C')] ≤ (1 - 13/(64(n-1))) · potentialLargeY(C)`. -/
theorem expected_potentialLargeY_le (c : Config n) (hy : c.inLargeY) (hn : n ≥ 2)
    (hbx : c.b_count + c.x_count ≥ 1) :
    ∫ c', (c'.potentialLargeY : ℝ) ∂(c.stepDist hn).toMeasure ≤
    (1 - 13 / (64 * ((n : ℝ) - 1))) * (c.potentialLargeY : ℝ) := by
  rw [integral_stepDist_eq_weighted_div, weighted_sum_split]
  have hT_ne : (totalPairs n : ℝ) ≠ 0 :=
    ne_of_gt (show (0 : ℝ) < _ from by exact_mod_cast totalPairs_pos hn)
  rw [add_div, mul_div_cancel_left₀ _ hT_ne]
  have hT_pos : (0 : ℝ) < (totalPairs n : ℝ) := by exact_mod_cast totalPairs_pos hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hT_eq : (totalPairs n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    unfold totalPairs
    rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  have hD_le : (∑ p : State × State,
      (c.interactionCount p.1 p.2 : ℝ) *
      (((c.stepOrSelf p.1 p.2).potentialLargeY : ℝ) -
       (c.potentialLargeY : ℝ))) ≤
      -(13 * (n : ℝ) * (c.potentialLargeY : ℝ)) / 64 := by
    rw [real_drift_eq_int_cast c Config.potentialLargeY]
    rw [le_div_iff₀ (show (0 : ℝ) < 64 from by norm_num)]
    have hbound := expected_decrease_potentialLargeY c hy hn hbx
    have hz : (∑ s₁ : State, ∑ s₂ : State,
        (c.interactionCount s₁ s₂ : ℤ) *
        (↑(c.stepOrSelf s₁ s₂).potentialLargeY -
         ↑c.potentialLargeY)) * 64 ≤
        -(13 * (n : ℤ) * ↑c.potentialLargeY) := by linarith
    exact_mod_cast hz
  set D := ∑ p : State × State, (c.interactionCount p.1 p.2 : ℝ) *
    (((c.stepOrSelf p.1 p.2).potentialLargeY : ℝ) -
     (c.potentialLargeY : ℝ))
  suffices hsuff : D / (totalPairs n : ℝ) ≤
      -(13 / (64 * ((n : ℝ) - 1))) * (c.potentialLargeY : ℝ) by
    have : (1 - 13 / (64 * ((n : ℝ) - 1))) * (c.potentialLargeY : ℝ) =
        (c.potentialLargeY : ℝ) -
        13 / (64 * ((n : ℝ) - 1)) * (c.potentialLargeY : ℝ) := by ring
    linarith
  rw [div_le_iff₀ hT_pos]
  calc D ≤ -(13 * (n : ℝ) * (c.potentialLargeY : ℝ)) / 64 := hD_le
    _ = -(13 / (64 * ((n : ℝ) - 1))) * (c.potentialLargeY : ℝ) *
        (totalPairs n : ℝ) := by rw [hT_eq]; field_simp

/-! ### Expected increase of v in large-b region

In the large-b region, v = x + y increases. The drift bound is
`16·Δv ≥ 13n·v`, giving `E[v'] ≥ (1 + 13/(16(n-1)))·v`. -/

/-- **Expected v increase (large-b, ℝ version)**:
    `E[v(C')] ≥ (1 + 13/(16(n-1))) · v(C)`.

    This is the formal drift condition for the large-b region.
    Since v increases (rather than a potential decreasing), we use
    `1/v` as the potential, which gives multiplicative drift. -/
theorem expected_v_ge (c : Config n) (hb : c.inLargeB) (hn : n ≥ 2) :
    ∫ c', (Config.v c' : ℝ) ∂(c.stepDist hn).toMeasure ≥
    (1 + 13 / (16 * ((n : ℝ) - 1))) * (c.v : ℝ) := by
  rw [integral_stepDist_eq_weighted_div, weighted_sum_split]
  have hT_ne : (totalPairs n : ℝ) ≠ 0 :=
    ne_of_gt (show (0 : ℝ) < _ from by exact_mod_cast totalPairs_pos hn)
  rw [add_div, mul_div_cancel_left₀ _ hT_ne]
  have hT_pos : (0 : ℝ) < (totalPairs n : ℝ) := by exact_mod_cast totalPairs_pos hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hT_eq : (totalPairs n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    unfold totalPairs
    rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  have hD_ge : (∑ p : State × State,
      (c.interactionCount p.1 p.2 : ℝ) *
      ((Config.v (c.stepOrSelf p.1 p.2) : ℝ) - (c.v : ℝ))) ≥
      (13 * (n : ℝ) * (c.v : ℝ)) / 16 := by
    rw [real_drift_eq_int_cast c Config.v, ge_iff_le,
        div_le_iff₀ (show (0 : ℝ) < 16 from by norm_num)]
    have hbound := expected_increase_v c hb hn
    have hz : 13 * (n : ℤ) * ↑c.v ≤
        (∑ s₁ : State, ∑ s₂ : State,
        (c.interactionCount s₁ s₂ : ℤ) *
        (↑(c.stepOrSelf s₁ s₂).v - ↑c.v)) * 16 := by linarith
    exact_mod_cast hz
  set D := ∑ p : State × State, (c.interactionCount p.1 p.2 : ℝ) *
    ((Config.v (c.stepOrSelf p.1 p.2) : ℝ) - (c.v : ℝ))
  suffices hsuff : D / (totalPairs n : ℝ) ≥
      (13 / (16 * ((n : ℝ) - 1))) * (c.v : ℝ) by
    have : (1 + 13 / (16 * ((n : ℝ) - 1))) * (c.v : ℝ) =
        (c.v : ℝ) + 13 / (16 * ((n : ℝ) - 1)) * (c.v : ℝ) := by ring
    linarith
  rw [ge_iff_le, le_div_iff₀ hT_pos]
  rw [ge_iff_le] at hD_ge
  calc (13 / (16 * ((n : ℝ) - 1))) * (c.v : ℝ) *
      (totalPairs n : ℝ) = (13 * (n : ℝ) * (c.v : ℝ)) / 16 := by
        rw [hT_eq]; field_simp
    _ ≤ D := hD_ge

end Config
end PopProto

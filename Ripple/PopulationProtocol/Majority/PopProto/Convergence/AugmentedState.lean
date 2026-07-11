/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Augmented State for Central Region Supermartingale

The central region (no count ≥ 7n/8) cannot use the direct multiplicative
drift E[1/f'] ≤ (1-δ)/f (counterexample: n=4, x=1, b=0, y=3), even with
truncation to activeCentral (verified computationally for n=4 to n=50).

Instead, the proof of Lemma 4 from Angluin-Aspnes-Eisenstat 2008 uses an
exponential supermartingale on an augmented state that tracks cumulative
interaction counts:

  M(c, s_vb, s_xy) = α_vb^{s_vb} · α_xy^{s_xy} / f(c)

where α_vb = (16n+7)/(16n), α_xy = (16n-5)/(16n).

## Definitions

- `AugConfig n` : augmented state = Config n × ℕ × ℕ
- `augStepDist` : one-step distribution on augmented state
- `augTransitionKernel` : Markov kernel on augmented state
- `absorbedAugKernel` : absorbed kernel (absorbs outside activeCentral)
- `supermartingaleM` : the function M on augmented state

## Main results

- `supermartingaleM_per_step` : ∫⁻ M d(absorbedAugKernel a) ≤ M a
- `supermartingaleM_iteration` : ∫⁻ M d(absorbedAugKernel^t a) ≤ M a
- `svb_tail_bound` : P[S^vb ≥ k] ≤ (n²+2n)/f₀ · ((16n)/(16n+7))^k

## Proof structure

The per-step condition reduces to the algebraic inequality
`supermartingale_per_step` (CentralSupermartingale.lean), which is already
fully proven. The iteration uses `lintegral_geometric_decay` with r = 1.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Convergence.CentralSupermartingale
import Ripple.PopulationProtocol.Majority.PopProto.Convergence.ConvergenceTime
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential

namespace PopProto

open State MeasureTheory ProbabilityTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace Config

variable {n : ℕ}

/-! ### Augmented state space -/

/-- The augmented state: configuration plus cumulative vb and xy counts. -/
abbrev AugConfig (n : ℕ) := Config n × ℕ × ℕ

/-- Discrete measurable space on the augmented state. -/
noncomputable instance instMeasurableSpaceAugConfig :
    MeasurableSpace (AugConfig n) := ⊤

instance instDiscreteMeasurableSpaceAugConfig :
    DiscreteMeasurableSpace (AugConfig n) where
  forall_measurableSet _ := trivial

/-! ### Augmented step distribution

The augmented step distribution maps (c, s_vb, s_xy) to a distribution
over (c', s_vb', s_xy') where:
- c' is drawn from the original step distribution
- s_vb' = s_vb + 1 if the interaction was vb, else s_vb
- s_xy' = s_xy + 1 if the interaction was xy, else s_xy
-/

/-- The augmented step function: maps (config, counters) and interaction type
    to the new augmented state. -/
def augStep (c : Config n) (s_vb s_xy : ℕ) (i r : State) : AugConfig n :=
  (c.stepOrSelf i r,
   s_vb + if isVB i r then 1 else 0,
   s_xy + if isXY i r then 1 else 0)

/-- The augmented one-step distribution: samples an interaction from the
    scheduler PMF and applies augStep. -/
noncomputable def augStepDist (a : AugConfig n) (hn : n ≥ 2) :
    PMF (AugConfig n) :=
  PMF.map (fun p => augStep a.1 a.2.1 a.2.2 p.1 p.2)
          (a.1.interactionPMF hn)

/-! ### Augmented transition kernel -/

/-- The Markov transition kernel on the augmented state. -/
noncomputable def augTransitionKernel (hn : n ≥ 2) :
    Kernel (AugConfig n) (AugConfig n) where
  toFun a := (augStepDist a hn).toMeasure
  measurable' := Measurable.of_discrete

instance instIsMarkovAugKernel (hn : n ≥ 2) :
    IsMarkovKernel (augTransitionKernel hn) where
  isProbabilityMeasure a := by
    change IsProbabilityMeasure ((augStepDist a hn).toMeasure)
    infer_instance

/-! ### Absorbed augmented kernel

Absorbs (identity) when the config component is outside activeCentral. -/

/-- The active central set lifted to the augmented state. -/
def augActiveCentral : Set (AugConfig n) :=
  {a | a.1 ∈ activeCentral}

private theorem augActiveCentral_measurableSet :
    MeasurableSet (augActiveCentral : Set (AugConfig n)) :=
  instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _

/-- Absorbed augmented kernel: transitions normally in activeCentral,
    absorbs outside. -/
noncomputable def absorbedAugKernel (hn : n ≥ 2) :
    Kernel (AugConfig n) (AugConfig n) :=
  Kernel.piecewise augActiveCentral_measurableSet
    (augTransitionKernel hn) Kernel.id

instance instIsMarkovAbsorbedAugKernel (hn : n ≥ 2) :
    IsMarkovKernel (absorbedAugKernel hn) := by
  unfold absorbedAugKernel
  have := instIsMarkovAugKernel hn
  infer_instance

/-! ### The supermartingale function M

M(c, s_vb, s_xy) = α_vb^{s_vb} · α_xy^{s_xy} / f(c)

where α_vb = (16n+7)/(16n) and α_xy = (16n-5)/(16n).

We work in ℝ≥0∞ to avoid sign issues. The key identity:

  M = (16n+7)^{s_vb} · (16n-5)^{s_xy} / ((16n)^{s_vb+s_xy} · f)
-/

/-- The supermartingale M on the augmented state, in ℝ≥0∞.

    M(c, s_vb, s_xy) = (16n+7)^{s_vb} · (16n-5)^{s_xy} / ((16n)^{s_vb+s_xy} · f(c))

    This equals α_vb^{s_vb} · α_xy^{s_xy} / f(c) where
    α_vb = (16n+7)/(16n) > 1 and α_xy = (16n-5)/(16n) < 1. -/
noncomputable def supermartingaleM (a : AugConfig n) : ℝ≥0∞ :=
  (((16 * n + 7 : ℕ) : ℝ≥0∞) ^ a.2.1 *
   ((16 * n - 5 : ℕ) : ℝ≥0∞) ^ a.2.2) /
  (((16 * n : ℕ) : ℝ≥0∞) ^ (a.2.1 + a.2.2) *
   ((a.1.potential : ℕ) : ℝ≥0∞))

private theorem supermartingaleM_measurable :
    Measurable (supermartingaleM : AugConfig n → ℝ≥0∞) :=
  fun _ _ => instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _

/-! ### Projection lemma

The first component of the augmented kernel projects to the
original transition kernel (or absorbed kernel). This is needed
to connect augmented-state bounds to the original chain. -/

/-- The marginal of the augmented step distribution on Config n equals
    the original step distribution. -/
theorem augStepDist_proj_eq_stepDist (a : AugConfig n) (hn : n ≥ 2) :
    (augStepDist a hn).map Prod.fst = a.1.stepDist hn := by
  -- augStepDist = PMF.map augStep interactionPMF
  -- stepDist = PMF.map stepOrSelf interactionPMF
  -- map fst ∘ map augStep = map (fst ∘ augStep) = map stepOrSelf
  simp only [augStepDist, stepDist, PMF.map_comp, Function.comp_def, augStep]

/-! ### Per-step supermartingale condition

The key property: E[M'] ≤ M at each step of the absorbed augmented kernel.

For a ∈ augActiveCentral (c ∈ activeCentral, v ≥ 1):
  ∫⁻ M d(augKernel a) = Σ_{(i,j)} P(i,j) · M(augStep a i j)

  The sum splits into vb, xy, and other contributions:
  = α_vb^{s_vb} · α_xy^{s_xy} · (1/T) ·
    [Σ_{vb} count · α_vb / f' + Σ_{xy} count · α_xy / f' + Σ_{other} count / f]

  The bracketed sum is ≤ T/f by supermartingale_per_step.
  So the integral ≤ α_vb^{s_vb} · α_xy^{s_xy} / f = M(a). -/

/-- The lintegral of any function over the augmented step distribution equals
    a finite sum over interaction types. -/
private theorem lintegral_augStepDist (a : AugConfig n) (hn : n ≥ 2)
    (φ : AugConfig n → ℝ≥0∞) :
    ∫⁻ a', φ a' ∂(augStepDist a hn).toMeasure =
    ∑ q : State × State,
      φ (augStep a.1 a.2.1 a.2.2 q.1 q.2) *
      (a.1.interactionPMF hn q) := by
  have hg : Measurable (fun (p : State × State) =>
      augStep a.1 a.2.1 a.2.2 p.1 p.2) := Measurable.of_discrete
  -- Step 1: Unfold augStepDist and rewrite measure using PMF.toMeasure_map
  have hmeas : (augStepDist a hn).toMeasure =
      (a.1.interactionPMF hn).toMeasure.map
        (fun p => augStep a.1 a.2.1 a.2.2 p.1 p.2) :=
    (@PMF.toMeasure_map (State × State) (AugConfig n)
      (fun p => augStep a.1 a.2.1 a.2.2 p.1 p.2) _ _
      (a.1.interactionPMF hn) hg).symm
  -- Step 2: Change variables and express as finite sum
  rw [hmeas, lintegral_map Measurable.of_discrete hg,
      lintegral_fintype]
  congr 1; ext q; congr 1
  exact PMF.toMeasure_apply_singleton
    (a.1.interactionPMF hn) (q : State × State)
    (measurableSet_singleton q)

/-- Extract v > 0 from membership in augActiveCentral. -/
private theorem augActiveCentral_mem_v_pos {a : AugConfig n}
    (ha : a ∈ augActiveCentral) : 0 < a.1.v := by
  exact ha.2

/-! ### Helper lemmas for per-step inequality

stepOrSelf returns c unchanged for the 5 "non-state-changing" interactions. -/

private theorem stepOrSelf_xx (c : Config n) : c.stepOrSelf x x = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_bb (c : Config n) : c.stepOrSelf b b = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_yy (c : Config n) : c.stepOrSelf y y = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_bx (c : Config n) : c.stepOrSelf b x = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_by' (c : Config n) : c.stepOrSelf b y = c := by
  unfold stepOrSelf step; split_ifs <;> simp

/-- augStep gives back `(c, s_vb, s_xy)` for the 5 "other" interactions. -/
private theorem augStep_other (c : Config n) (svb sxy : ℕ) (i r : State)
    (hvb : ¬isVB i r) (hxy : ¬isXY i r) (hstep : c.stepOrSelf i r = c) :
    augStep c svb sxy i r = (c, svb, sxy) := by
  simp only [augStep, hstep, hvb, hxy, ite_false, Nat.add_zero]

/-- Expand a sum over `State` into three explicit terms. -/
private lemma sum_state_expand {α : Type*} [AddCommMonoid α] (f : State → α) :
    Finset.univ.sum f = f .x + f .b + f .y := by
  rw [show (Finset.univ : Finset State) = {.x, .b, .y} from by
    ext s; simp [Finset.mem_univ]; cases s <;> simp]
  rw [Finset.sum_insert (show State.x ∉ ({.b, .y} : Finset State) from by decide),
      Finset.sum_insert (show State.b ∉ ({.y} : Finset State) from by decide),
      Finset.sum_singleton]; abel

/-- augStep for the 5 "other" interactions returns (c, svb, sxy). -/
private theorem augStep_xx (c : Config n) (svb sxy : ℕ) :
    augStep c svb sxy x x = (c, svb, sxy) := by
  simp [augStep, isVB, isXY, stepOrSelf_xx]
private theorem augStep_bb (c : Config n) (svb sxy : ℕ) :
    augStep c svb sxy b b = (c, svb, sxy) := by
  simp [augStep, isVB, isXY, stepOrSelf_bb]
private theorem augStep_yy (c : Config n) (svb sxy : ℕ) :
    augStep c svb sxy y y = (c, svb, sxy) := by
  simp [augStep, isVB, isXY, stepOrSelf_yy]
private theorem augStep_bx (c : Config n) (svb sxy : ℕ) :
    augStep c svb sxy b x = (c, svb, sxy) := by
  simp [augStep, isVB, isXY, stepOrSelf_bx]
private theorem augStep_by'' (c : Config n) (svb sxy : ℕ) :
    augStep c svb sxy b y = (c, svb, sxy) := by
  simp [augStep, isVB, isXY, stepOrSelf_by']

/-- augStep for VB interactions increments s_vb. -/
private theorem augStep_xb (c : Config n) (svb sxy : ℕ) :
    augStep c svb sxy x b = (c.stepOrSelf x b, svb + 1, sxy) := by
  simp [augStep, isVB, isXY]
private theorem augStep_yb (c : Config n) (svb sxy : ℕ) :
    augStep c svb sxy y b = (c.stepOrSelf y b, svb + 1, sxy) := by
  simp [augStep, isVB, isXY]

/-- augStep for XY interactions increments s_xy. -/
private theorem augStep_xy (c : Config n) (svb sxy : ℕ) :
    augStep c svb sxy x y = (c.stepOrSelf x y, svb, sxy + 1) := by
  simp [augStep, isVB, isXY]
private theorem augStep_yx (c : Config n) (svb sxy : ℕ) :
    augStep c svb sxy y x = (c.stepOrSelf y x, svb, sxy + 1) := by
  simp [augStep, isVB, isXY]

set_option maxHeartbeats 1600000 in
/-- **ℝ≥0∞ algebraic core**: The finite sum over interaction types satisfies
    the supermartingale condition. This bridges `supermartingale_per_step`
    (integer cross-multiplied form) to the ℝ≥0∞ sum form.

    ## Proof strategy (K-cancel in ℝ, then field_simp + nlinarith)

    1. Convert to ℝ via toReal, expand to 9 terms, simplify augStep
    2. Factor `K = (16n+7)^svb * (16n-5)^sxy / (16n)^{svb+sxy}` from both sides
    3. Cancel K (positive in ℝ) → eliminates all variable exponents
    4. `field_simp` clears remaining denominators (f, f', T, 16n)
    5. `nlinarith` closes using `supermartingale_per_step` cast to ℝ -/
private theorem supermartingaleM_per_step_ennreal (a : AugConfig n) (hn : n ≥ 2)
    (hv : 0 < a.1.v) :
    ∑ q : State × State,
      supermartingaleM (augStep a.1 a.2.1 a.2.2 q.1 q.2) *
      (a.1.interactionPMF hn q) ≤ supermartingaleM a := by
  obtain ⟨c, svb, sxy⟩ := a
  -- The ℤ cross-multiplied inequality (already proved):
  have h_int := supermartingale_per_step c (show n ≥ 1 by omega) hv
  -- Step 1: Finiteness — all M values and PMF values are < ⊤
  have hM_ne : ∀ (a' : AugConfig n), supermartingaleM a' ≠ ⊤ := fun a' => by
    simp only [supermartingaleM]
    exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
                          (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
      (mul_ne_zero
        (pow_ne_zero _ (by exact_mod_cast (show (16 * n : ℕ) ≠ 0 from by omega)))
        (by exact_mod_cast (potential_pos a'.1 (show n ≥ 1 by omega)).ne'))
  have hP_ne : ∀ q : State × State, c.interactionPMF hn q ≠ ⊤ :=
    fun q => (PMF.apply_lt_top _ _).ne
  have hterm_ne : ∀ q ∈ (Finset.univ : Finset (State × State)),
      supermartingaleM (augStep c svb sxy q.1 q.2) *
      (c.interactionPMF hn q) ≠ ⊤ := fun q _ =>
    ENNReal.mul_ne_top (hM_ne _) (hP_ne q)
  have hsum_ne : (∑ q : State × State,
      supermartingaleM (augStep c svb sxy q.1 q.2) *
      (c.interactionPMF hn q)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr hterm_ne
  -- Step 2: Convert to ℝ via toReal
  rw [← ENNReal.toReal_le_toReal hsum_ne (hM_ne _)]
  rw [ENNReal.toReal_sum hterm_ne]
  simp_rw [ENNReal.toReal_mul]
  -- Step 3: Unfold M and PMF to ℝ expressions
  simp only [supermartingaleM, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_natCast]
  simp_rw [interactionPMF_toReal c hn]
  -- Step 4: Expand to 9 terms and simplify augStep
  rw [show (Finset.univ : Finset (State × State)) = Finset.univ ×ˢ Finset.univ
      from Finset.univ_product_univ.symm, Finset.sum_product]
  simp only [sum_state_expand]
  simp only [augStep_xx c svb sxy, augStep_xb c svb sxy, augStep_xy c svb sxy,
    augStep_bx c svb sxy, augStep_bb c svb sxy, augStep_by'' c svb sxy,
    augStep_yx c svb sxy, augStep_yb c svb sxy, augStep_yy c svb sxy]
  -- Step 5: Rewrite pow_succ to expose K as common factor
  rw [show svb + 1 + sxy = (svb + sxy) + 1 from by omega,
      show svb + (sxy + 1) = (svb + sxy) + 1 from by omega]
  simp only [pow_succ']
  -- Step 6: Case split on whether all three counts ≥ 1
  -- When all positive, all steps succeed and potentials are known.
  -- When some is zero, many terms vanish.
  by_cases h_bxy : c.b_count ≥ 1 ∧ c.x_count ≥ 1 ∧ c.y_count ≥ 1
  · -- **Main case**: b ≥ 1, x ≥ 1, y ≥ 1 — all 4 active steps succeed
    obtain ⟨hb1, hx1, hy1⟩ := h_bxy
    -- Compute stepped potentials using delta_f lemmas
    have hpot_xb : (((c.stepOrSelf x b).potential : ℕ) : ℝ) =
        ((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1 := by
      have hstep : c.step x b = some ⟨c.x_count + 1, c.b_count - 1, c.y_count,
          by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos ⟨hx1, hb1⟩
      simp only [stepOrSelf, hstep, Option.getD_some]
      exact_mod_cast (show (_ : ℤ) = _ from by linarith [delta_f_xb c _ hstep])
    have hpot_yb : (((c.stepOrSelf y b).potential : ℕ) : ℝ) =
        ((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1 := by
      have hstep : c.step y b = some ⟨c.x_count, c.b_count - 1, c.y_count + 1,
          by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos ⟨hy1, hb1⟩
      simp only [stepOrSelf, hstep, Option.getD_some]
      exact_mod_cast (show (_ : ℤ) = _ from by linarith [delta_f_yb c _ hstep])
    have hpot_xy : (((c.stepOrSelf x y).potential : ℕ) : ℝ) =
        ((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1 := by
      have hstep : c.step x y = some ⟨c.x_count, c.b_count + 1, c.y_count - 1,
          by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos ⟨hx1, hy1⟩
      simp only [stepOrSelf, hstep, Option.getD_some]
      exact_mod_cast (show (_ : ℤ) = _ from by linarith [delta_f_xy c _ hstep])
    have hpot_yx : (((c.stepOrSelf y x).potential : ℕ) : ℝ) =
        ((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1 := by
      have hstep : c.step y x = some ⟨c.x_count - 1, c.b_count + 1, c.y_count,
          by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos ⟨hy1, hx1⟩
      simp only [stepOrSelf, hstep, Option.getD_some]
      exact_mod_cast (show (_ : ℤ) = _ from by linarith [delta_f_yx c _ hstep])
    -- Substitute stepped potentials → eliminates stepOrSelf from goal
    rw [hpot_xb, hpot_yb, hpot_xy, hpot_yx]
    -- Positivity facts for all denominators
    have hαvb_pos : (0 : ℝ) < ((16 * n + 7 : ℕ) : ℝ) := by positivity
    have hαxy_pos : (0 : ℝ) < ((16 * n - 5 : ℕ) : ℝ) := by
      exact_mod_cast (show (0 : ℕ) < 16 * n - 5 from by omega)
    have hP_pos : (0 : ℝ) < ((16 * n : ℕ) : ℝ) := by positivity
    have hf_pos : (0 : ℝ) < ((c.potential : ℕ) : ℝ) := by
      exact_mod_cast potential_pos c (show n ≥ 1 by omega)
    have hT_pos : (0 : ℝ) < ((totalPairs n : ℕ) : ℝ) := by
      exact_mod_cast totalPairs_pos hn
    -- a = (u+1)²+2n > 0 and b = (u-1)²+2n > 0
    have ha_pos : (0 : ℝ) < ((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1 := by
      have : (0 : ℤ) < ↑c.potential + 2 * c.u + 1 := by
        have : (c.potential : ℤ) = c.u ^ 2 + 2 * ↑n := by simp [potential]
        nlinarith [sq_nonneg (c.u + 1 : ℤ)]
      exact_mod_cast this
    have hb'_pos : (0 : ℝ) < ((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1 := by
      have : (0 : ℤ) < ↑c.potential - 2 * c.u + 1 := by
        have : (c.potential : ℤ) = c.u ^ 2 + 2 * ↑n := by simp [potential]
        nlinarith [sq_nonneg (c.u - 1 : ℤ)]
      exact_mod_cast this
    -- K-cancellation: divide by K = αvb^svb * αxy^sxy / P^(svb+sxy)
    have hK_pos : (0 : ℝ) < ((16 * n + 7 : ℕ) : ℝ) ^ svb * ((16 * n - 5 : ℕ) : ℝ) ^ sxy /
        ((16 * n : ℕ) : ℝ) ^ (svb + sxy) :=
      div_pos (mul_pos (pow_pos hαvb_pos _) (pow_pos hαxy_pos _)) (pow_pos hP_pos _)
    rw [(div_le_div_iff_of_pos_right hK_pos).symm]
    simp only [add_div]
    -- field_simp cancels variable exponents αvb^svb, αxy^sxy, P^(svb+sxy)
    -- and clears remaining denominators (f, f±2u+1, T, P)
    field_simp [hαvb_pos.ne', hαxy_pos.ne', hP_pos.ne', hf_pos.ne', hT_pos.ne',
      ha_pos.ne', hb'_pos.ne',
      pow_ne_zero _ hαvb_pos.ne', pow_ne_zero _ hαxy_pos.ne', pow_ne_zero _ hP_pos.ne']
    -- Unfold interactionCount and handle ℕ→ℝ casts
    simp only [interactionCount, countOf, totalPairs,
      show ¬(State.x = State.b) from by decide, show ¬(State.x = State.y) from by decide,
      show ¬(State.b = State.x) from by decide, show ¬(State.b = State.y) from by decide,
      show ¬(State.y = State.x) from by decide, show ¬(State.y = State.b) from by decide,
      ite_true, ite_false]
    push_cast [Nat.cast_sub hx1, Nat.cast_sub hb1, Nat.cast_sub hy1,
               Nat.cast_sub (show 1 ≤ n from by omega),
               Nat.cast_sub (show 5 ≤ 16 * n from by omega)]
    -- Bridge the ℤ cross-multiplied inequality to ℝ
    have h_int_R : (c.b_count : ℝ) *
        ((16 * (n : ℝ) + 7) * ((c.u : ℝ) ^ 2 + 2 * ↑n) *
         ((c.v : ℝ) * ((c.u : ℝ) ^ 2 + 2 * ↑n + 1) - 2 * (c.u : ℝ) ^ 2)) +
        2 * (c.x_count : ℝ) * (c.y_count : ℝ) *
        ((16 * (n : ℝ) - 5) * ((c.u : ℝ) ^ 2 + 2 * ↑n) *
         ((c.u : ℝ) ^ 2 + 2 * ↑n + 1)) ≤
        ((c.b_count : ℝ) * (c.v : ℝ) + 2 * (c.x_count : ℝ) * (c.y_count : ℝ)) *
        (16 * (n : ℝ) * (((c.u : ℝ) ^ 2 + 2 * ↑n + 1) ^ 2 - 4 * (c.u : ℝ) ^ 2)) := by
      exact_mod_cast h_int
    have hf_eq : ((c.potential : ℕ) : ℝ) = ((c.u : ℤ) : ℝ) ^ 2 + 2 * (n : ℝ) := by
      exact_mod_cast (show (c.potential : ℤ) = c.u ^ 2 + 2 * ↑n from by simp [potential])
    have hv_eq : (c.v : ℝ) = (c.x_count : ℝ) + (c.y_count : ℝ) := by
      exact_mod_cast (show (c.v : ℕ) = c.x_count + c.y_count from rfl)
    have h_sum : (n : ℝ) = (c.x_count : ℝ) + (c.b_count : ℝ) + (c.y_count : ℝ) := by
      exact_mod_cast c.sum_eq.symm
    -- *** Key decomposition ***
    -- Goal after field_simp: P·a·b'·other + f·αvb·(xb·b'+yb·a) + f·αxy·(xy·b'+yx·a) ≤ P·T·a·b'
    -- where other = xx+bx+bb+by+yy (5 terms with M unchanged).
    -- Strategy: bound active terms via h_int_R, then use count identity.
    --
    -- Active bound: after factoring xb·b'+yb·a = b·(v(f+1)-2u²) and
    -- xy·b'+yx·a = 2xy(f+1), the active terms ≤ (bv+2xy)·P·a·b' by h_int_R.
    have h_act :
        ((c.potential : ℕ) : ℝ) * (16 * (n : ℝ) + 7) *
          ((c.x_count : ℝ) * ↑c.b_count *
            (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) +
           (c.y_count : ℝ) * ↑c.b_count *
            (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1)) +
        ((c.potential : ℕ) : ℝ) * (16 * (n : ℝ) - 5) *
          ((c.x_count : ℝ) * ↑c.y_count *
            (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) +
           (c.y_count : ℝ) * ↑c.x_count *
            (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1)) ≤
        ((c.b_count : ℝ) * ((c.x_count : ℝ) + ↑c.y_count) +
         2 * (c.x_count : ℝ) * ↑c.y_count) *
        (16 * (n : ℝ)) *
        (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1) *
        (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) := by
      -- Bridge h_int_R to the goal by substituting potential↔u²+2n, v↔x+y, u↔x-y
      have h_key := h_int_R
      rw [← hf_eq, hv_eq] at h_key
      have hu_eq : ((c.u : ℤ) : ℝ) = (c.x_count : ℝ) - (c.y_count : ℝ) := by
        exact_mod_cast (show (c.u : ℤ) = ↑c.x_count - ↑c.y_count from rfl)
      rw [hu_eq] at h_key ⊢
      ring_nf at h_key ⊢
      linarith [h_key]
    -- P·a·b' ≥ 0 (needed for multiplying the count identity)
    have hPab : (0 : ℝ) ≤ 16 * (n : ℝ) *
        (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1) *
        (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n from by omega)
      exact le_of_lt (mul_pos (mul_pos (by linarith) ha_pos) hb'_pos)
    -- Count identity: other_count + bv + 2xy = totalPairs
    have h_cnt : (c.x_count : ℝ) * ((c.x_count : ℝ) - 1) +
        ↑c.b_count * ↑c.x_count +
        ↑c.b_count * ((c.b_count : ℝ) - 1) +
        ↑c.b_count * ↑c.y_count +
        ↑c.y_count * ((c.y_count : ℝ) - 1) +
        ((c.b_count : ℝ) * ((c.x_count : ℝ) + ↑c.y_count) +
         2 * (c.x_count : ℝ) * ↑c.y_count) =
        (n : ℝ) * ((n : ℝ) - 1) := by nlinarith [h_sum]
    -- Close: LHS = P·a·b'·other + active ≤ P·a·b'·(other+bv+2xy) = P·T·a·b' = RHS
    nlinarith [h_act, hPab, h_cnt]
  · -- **Degenerate case**: at least one of b, x, y = 0
    -- When a count is 0, corresponding PMF weights are 0 and those terms vanish.
    -- Helper: step returns none when count conditions fail
    have step_xb_none : ¬(c.x_count ≥ 1 ∧ c.b_count ≥ 1) → c.stepOrSelf x b = c := by
      intro h; simp only [stepOrSelf, step, dif_neg h]; rfl
    have step_yb_none : ¬(c.y_count ≥ 1 ∧ c.b_count ≥ 1) → c.stepOrSelf y b = c := by
      intro h; simp only [stepOrSelf, step, dif_neg h]; rfl
    have step_xy_none : ¬(c.x_count ≥ 1 ∧ c.y_count ≥ 1) → c.stepOrSelf x y = c := by
      intro h; simp only [stepOrSelf, step, dif_neg h]; rfl
    have step_yx_none : ¬(c.y_count ≥ 1 ∧ c.x_count ≥ 1) → c.stepOrSelf y x = c := by
      intro h; simp only [stepOrSelf, step, dif_neg h]; rfl
    -- Common positivity facts
    have hαvb_pos : (0 : ℝ) < ((16 * n + 7 : ℕ) : ℝ) := by positivity
    have hαxy_pos : (0 : ℝ) < ((16 * n - 5 : ℕ) : ℝ) := by
      exact_mod_cast (show (0 : ℕ) < 16 * n - 5 from by omega)
    have hP_pos : (0 : ℝ) < ((16 * n : ℕ) : ℝ) := by positivity
    have hf_pos : (0 : ℝ) < ((c.potential : ℕ) : ℝ) := by
      exact_mod_cast potential_pos c (show n ≥ 1 by omega)
    have hT_pos : (0 : ℝ) < ((totalPairs n : ℕ) : ℝ) := by
      exact_mod_cast totalPairs_pos hn
    have ha_pos : (0 : ℝ) < ((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1 := by
      have : (0 : ℤ) < ↑c.potential + 2 * c.u + 1 := by
        have : (c.potential : ℤ) = c.u ^ 2 + 2 * ↑n := by simp [potential]
        nlinarith [sq_nonneg (c.u + 1 : ℤ)]
      exact_mod_cast this
    have hb'_pos : (0 : ℝ) < ((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1 := by
      have : (0 : ℤ) < ↑c.potential - 2 * c.u + 1 := by
        have : (c.potential : ℤ) = c.u ^ 2 + 2 * ↑n := by simp [potential]
        nlinarith [sq_nonneg (c.u - 1 : ℤ)]
      exact_mod_cast this
    -- The ℤ cross-multiplied inequality (holds for ALL configs with v > 0)
    have h_int := supermartingale_per_step c (show n ≥ 1 by omega) hv
    have h_int_R : (c.b_count : ℝ) *
        ((16 * (n : ℝ) + 7) * ((c.u : ℝ) ^ 2 + 2 * ↑n) *
         ((c.v : ℝ) * ((c.u : ℝ) ^ 2 + 2 * ↑n + 1) - 2 * (c.u : ℝ) ^ 2)) +
        2 * (c.x_count : ℝ) * (c.y_count : ℝ) *
        ((16 * (n : ℝ) - 5) * ((c.u : ℝ) ^ 2 + 2 * ↑n) *
         ((c.u : ℝ) ^ 2 + 2 * ↑n + 1)) ≤
        ((c.b_count : ℝ) * (c.v : ℝ) + 2 * (c.x_count : ℝ) * (c.y_count : ℝ)) *
        (16 * (n : ℝ) * (((c.u : ℝ) ^ 2 + 2 * ↑n + 1) ^ 2 - 4 * (c.u : ℝ) ^ 2)) := by
      exact_mod_cast h_int
    -- h_bxy : ¬(b ≥ 1 ∧ x ≥ 1 ∧ y ≥ 1), so at least one count = 0
    have hs := c.sum_eq  -- x + b + y = n, needed for omega throughout
    have hv' : 0 < c.x_count + c.y_count := by unfold v at hv; exact hv
    have h_cases : c.b_count = 0 ∨ c.x_count = 0 ∨ c.y_count = 0 := by
      by_contra hall; push_neg at hall; exact h_bxy ⟨by omega, by omega, by omega⟩
    rcases h_cases with hb | hx | hy
    · -- **b = 0**: vb interactions have zero weight
      have hb0 : c.b_count = 0 := hb
      simp only [step_xb_none (by omega), step_yb_none (by omega)]
      by_cases hx1 : c.x_count ≥ 1
      · by_cases hy1 : c.y_count ≥ 1
        · -- b=0, x≥1, y≥1: xy/yx succeed
          have hpot_xy : (((c.stepOrSelf x y).potential : ℕ) : ℝ) =
              ((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1 := by
            have hstep : c.step x y = some ⟨c.x_count, c.b_count + 1, c.y_count - 1,
                by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos ⟨hx1, hy1⟩
            simp only [stepOrSelf, hstep, Option.getD_some]
            exact_mod_cast (show (_ : ℤ) = _ from by linarith [delta_f_xy c _ hstep])
          have hpot_yx : (((c.stepOrSelf y x).potential : ℕ) : ℝ) =
              ((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1 := by
            have hstep : c.step y x = some ⟨c.x_count - 1, c.b_count + 1, c.y_count,
                by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos ⟨hy1, hx1⟩
            simp only [stepOrSelf, hstep, Option.getD_some]
            exact_mod_cast (show (_ : ℤ) = _ from by linarith [delta_f_yx c _ hstep])
          rw [hpot_xy, hpot_yx]
          -- Same algebraic closure as main case but with b = 0
          have hK_pos : (0 : ℝ) < ((16 * n + 7 : ℕ) : ℝ) ^ svb *
              ((16 * n - 5 : ℕ) : ℝ) ^ sxy /
              ((16 * n : ℕ) : ℝ) ^ (svb + sxy) :=
            div_pos (mul_pos (pow_pos hαvb_pos _) (pow_pos hαxy_pos _))
              (pow_pos hP_pos _)
          rw [(div_le_div_iff_of_pos_right hK_pos).symm]
          simp only [add_div]
          field_simp [hαvb_pos.ne', hαxy_pos.ne', hP_pos.ne', hf_pos.ne', hT_pos.ne',
            ha_pos.ne', hb'_pos.ne',
            pow_ne_zero _ hαvb_pos.ne', pow_ne_zero _ hαxy_pos.ne',
            pow_ne_zero _ hP_pos.ne']
          simp only [interactionCount, countOf, totalPairs,
            show ¬(State.x = State.b) from by decide,
            show ¬(State.x = State.y) from by decide,
            show ¬(State.b = State.x) from by decide,
            show ¬(State.b = State.y) from by decide,
            show ¬(State.y = State.x) from by decide,
            show ¬(State.y = State.b) from by decide,
            ite_true, ite_false]
          -- Substitute b = 0 in ℕ before push_cast
          simp only [show c.b_count = 0 from hb0, Nat.zero_mul, Nat.mul_zero,
            Nat.zero_sub, Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
          push_cast [Nat.cast_sub hx1, Nat.cast_sub hy1,
                     Nat.cast_sub (show 1 ≤ n from by omega),
                     Nat.cast_sub (show 5 ≤ 16 * n from by omega)]
          have hf_eq : ((c.potential : ℕ) : ℝ) = ((c.u : ℤ) : ℝ) ^ 2 + 2 * (n : ℝ) := by
            exact_mod_cast (show (c.potential : ℤ) = c.u ^ 2 + 2 * ↑n from by
              simp [potential])
          have hv_eq : (c.v : ℝ) = (c.x_count : ℝ) + (c.y_count : ℝ) := by
            exact_mod_cast (show (c.v : ℕ) = c.x_count + c.y_count from rfl)
          have h_sum : (n : ℝ) = (c.x_count : ℝ) + (c.y_count : ℝ) := by
            exact_mod_cast (show n = c.x_count + c.y_count from by omega)
          -- h_int_R with b=0: vb term vanishes, only xy bound remains
          simp only [show (c.b_count : ℝ) = 0 from by exact_mod_cast hb0,
            zero_mul, zero_add, mul_zero] at h_int_R
          have h_act :
              ((c.potential : ℕ) : ℝ) * (16 * (n : ℝ) - 5) *
                ((c.x_count : ℝ) * ↑c.y_count *
                  (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) +
                 (c.y_count : ℝ) * ↑c.x_count *
                  (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1)) ≤
              2 * (c.x_count : ℝ) * ↑c.y_count *
              (16 * (n : ℝ)) *
              (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1) *
              (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) := by
            have h_key := h_int_R
            rw [← hf_eq] at h_key
            -- Bridge: rewrite LHS and RHS to match h_key's form
            have heq_lhs : ((c.potential : ℕ) : ℝ) * (16 * (n : ℝ) - 5) *
                ((c.x_count : ℝ) * ↑c.y_count *
                  (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) +
                 (c.y_count : ℝ) * ↑c.x_count *
                  (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1)) =
                2 * (c.x_count : ℝ) * ↑c.y_count *
                  ((16 * (n : ℝ) - 5) * ((c.potential : ℕ) : ℝ) *
                    (((c.potential : ℕ) : ℝ) + 1)) := by ring
            have heq_rhs : 2 * (c.x_count : ℝ) * ↑c.y_count *
                (16 * (n : ℝ)) *
                (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1) *
                (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) =
                2 * (c.x_count : ℝ) * ↑c.y_count *
                  (16 * (n : ℝ) * ((((c.potential : ℕ) : ℝ) + 1) ^ 2 -
                    4 * ((c.u : ℤ) : ℝ) ^ 2)) := by ring
            rw [heq_lhs, heq_rhs]
            exact h_key
          have hPab : (0 : ℝ) ≤ 16 * (n : ℝ) *
              (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1) *
              (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) := by
            have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n from by omega)
            exact le_of_lt (mul_pos (mul_pos (by linarith) ha_pos) hb'_pos)
          have h_cnt : (c.x_count : ℝ) * ((c.x_count : ℝ) - 1) +
              ↑c.y_count * ((c.y_count : ℝ) - 1) +
              2 * (c.x_count : ℝ) * ↑c.y_count =
              (n : ℝ) * ((n : ℝ) - 1) := by nlinarith [h_sum]
          nlinarith [h_act, hPab, h_cnt]
        · -- b=0, x≥1, y=0: xy/yx fail, only xx survives
          have hy0 : c.y_count = 0 := by omega
          simp only [step_xy_none (by omega), step_yx_none (by omega)]
          -- All M values use c.potential. Sum = M * x(x-1)/T = M (since x=n)
          have hK_pos : (0 : ℝ) < ((16 * n + 7 : ℕ) : ℝ) ^ svb *
              ((16 * n - 5 : ℕ) : ℝ) ^ sxy /
              ((16 * n : ℕ) : ℝ) ^ (svb + sxy) :=
            div_pos (mul_pos (pow_pos hαvb_pos _) (pow_pos hαxy_pos _))
              (pow_pos hP_pos _)
          rw [(div_le_div_iff_of_pos_right hK_pos).symm]
          simp only [add_div]
          field_simp [hαvb_pos.ne', hαxy_pos.ne', hP_pos.ne', hf_pos.ne', hT_pos.ne',
            pow_ne_zero _ hαvb_pos.ne', pow_ne_zero _ hαxy_pos.ne',
            pow_ne_zero _ hP_pos.ne']
          simp only [interactionCount, countOf, totalPairs,
            show ¬(State.x = State.b) from by decide,
            show ¬(State.x = State.y) from by decide,
            show ¬(State.b = State.x) from by decide,
            show ¬(State.b = State.y) from by decide,
            show ¬(State.y = State.x) from by decide,
            show ¬(State.y = State.b) from by decide,
            ite_true, ite_false]
          simp only [show c.b_count = 0 from hb0, show c.y_count = 0 from hy0,
            Nat.zero_mul, Nat.mul_zero, Nat.zero_sub,
            Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
          push_cast [Nat.cast_sub hx1,
                     Nat.cast_sub (show 1 ≤ n from by omega),
                     Nat.cast_sub (show 5 ≤ 16 * n from by omega)]
          -- With b=0, y=0: x=n, so x*(x-1) = n*(n-1) and sum = M
          have hxn : (c.x_count : ℝ) = (n : ℝ) := by exact_mod_cast (show c.x_count = n from by omega)
          simp only [hxn]; linarith
      · -- b=0, x=0: only yy survives
        have hx0 : c.x_count = 0 := by omega
        simp only [step_xy_none (by omega), step_yx_none (by omega)]
        have hK_pos : (0 : ℝ) < ((16 * n + 7 : ℕ) : ℝ) ^ svb *
            ((16 * n - 5 : ℕ) : ℝ) ^ sxy /
            ((16 * n : ℕ) : ℝ) ^ (svb + sxy) :=
          div_pos (mul_pos (pow_pos hαvb_pos _) (pow_pos hαxy_pos _))
            (pow_pos hP_pos _)
        rw [(div_le_div_iff_of_pos_right hK_pos).symm]
        simp only [add_div]
        field_simp [hαvb_pos.ne', hαxy_pos.ne', hP_pos.ne', hf_pos.ne', hT_pos.ne',
          pow_ne_zero _ hαvb_pos.ne', pow_ne_zero _ hαxy_pos.ne',
          pow_ne_zero _ hP_pos.ne']
        simp only [interactionCount, countOf, totalPairs,
          show ¬(State.x = State.b) from by decide,
          show ¬(State.x = State.y) from by decide,
          show ¬(State.b = State.x) from by decide,
          show ¬(State.b = State.y) from by decide,
          show ¬(State.y = State.x) from by decide,
          show ¬(State.y = State.b) from by decide,
          ite_true, ite_false]
        simp only [show c.b_count = 0 from hb0, show c.x_count = 0 from hx0,
          Nat.zero_mul, Nat.mul_zero, Nat.zero_sub,
          Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
        have hy1 : c.y_count ≥ 1 := by omega
        push_cast [Nat.cast_sub hy1,
                   Nat.cast_sub (show 1 ≤ n from by omega),
                   Nat.cast_sub (show 5 ≤ 16 * n from by omega)]
        have hyn : (c.y_count : ℝ) = (n : ℝ) := by exact_mod_cast (show c.y_count = n from by omega)
        simp only [hyn]; linarith
    · -- **x = 0**: xb, xy, yx interactions have zero weight
      have hx0 : c.x_count = 0 := by omega
      simp only [step_xb_none (by omega), step_xy_none (by omega),
        step_yx_none (by omega)]
      by_cases hb1 : c.b_count ≥ 1
      · by_cases hy1 : c.y_count ≥ 1
        · -- x=0, b≥1, y≥1: yb succeeds
          have hpot_yb : (((c.stepOrSelf y b).potential : ℕ) : ℝ) =
              ((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1 := by
            have hstep : c.step y b = some ⟨c.x_count, c.b_count - 1, c.y_count + 1,
                by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos ⟨hy1, hb1⟩
            simp only [stepOrSelf, hstep, Option.getD_some]
            exact_mod_cast (show (_ : ℤ) = _ from by linarith [delta_f_yb c _ hstep])
          rw [hpot_yb]
          have hK_pos : (0 : ℝ) < ((16 * n + 7 : ℕ) : ℝ) ^ svb *
              ((16 * n - 5 : ℕ) : ℝ) ^ sxy /
              ((16 * n : ℕ) : ℝ) ^ (svb + sxy) :=
            div_pos (mul_pos (pow_pos hαvb_pos _) (pow_pos hαxy_pos _))
              (pow_pos hP_pos _)
          rw [(div_le_div_iff_of_pos_right hK_pos).symm]
          simp only [add_div]
          field_simp [hαvb_pos.ne', hαxy_pos.ne', hP_pos.ne', hf_pos.ne', hT_pos.ne',
            hb'_pos.ne',
            pow_ne_zero _ hαvb_pos.ne', pow_ne_zero _ hαxy_pos.ne',
            pow_ne_zero _ hP_pos.ne']
          simp only [interactionCount, countOf, totalPairs,
            show ¬(State.x = State.b) from by decide,
            show ¬(State.x = State.y) from by decide,
            show ¬(State.b = State.x) from by decide,
            show ¬(State.b = State.y) from by decide,
            show ¬(State.y = State.x) from by decide,
            show ¬(State.y = State.b) from by decide,
            ite_true, ite_false]
          simp only [show c.x_count = 0 from hx0, Nat.zero_mul, Nat.mul_zero,
            Nat.zero_sub, Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
          push_cast [Nat.cast_sub hb1, Nat.cast_sub hy1,
                     Nat.cast_sub (show 1 ≤ n from by omega),
                     Nat.cast_sub (show 5 ≤ 16 * n from by omega)]
          have hf_eq : ((c.potential : ℕ) : ℝ) = ((c.u : ℤ) : ℝ) ^ 2 + 2 * (n : ℝ) := by
            exact_mod_cast (show (c.potential : ℤ) = c.u ^ 2 + 2 * ↑n from by
              simp [potential])
          have h_sum : (n : ℝ) = (c.b_count : ℝ) + (c.y_count : ℝ) := by
            exact_mod_cast (show n = c.b_count + c.y_count from by omega)
          -- h_int_R with x=0: xy term vanishes, only vb bound remains
          simp only [show (c.x_count : ℝ) = 0 from by exact_mod_cast hx0,
            zero_mul, mul_zero, add_zero] at h_int_R
          have hv_eq : (c.v : ℝ) = (c.y_count : ℝ) := by
            exact_mod_cast (show (c.v : ℕ) = c.y_count from by unfold v; omega)
          have h_act :
              ((c.potential : ℕ) : ℝ) * (16 * (n : ℝ) + 7) *
                (c.y_count : ℝ) * ↑c.b_count *
                (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1) ≤
              (c.b_count : ℝ) * (c.y_count : ℝ) *
              (16 * (n : ℝ)) *
              (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1) *
              (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) := by
            have h_key := h_int_R
            rw [← hf_eq, hv_eq] at h_key
            have hu_eq : ((c.u : ℤ) : ℝ) = -(c.y_count : ℝ) := by
              have : (c.u : ℤ) = -(c.y_count : ℤ) := by
                simp only [u, Config.gap]
                rw [show (c.x_count : ℤ) = 0 from by exact_mod_cast hx0]; ring
              exact_mod_cast this
            rw [hu_eq] at h_key ⊢
            nlinarith [h_key, sq_nonneg (c.y_count : ℝ), sq_nonneg (c.b_count : ℝ),
              sq_nonneg ((c.potential : ℕ) : ℝ)]
          have hPab : (0 : ℝ) ≤ 16 * (n : ℝ) *
              (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1) *
              (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) := by
            have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n from by omega)
            exact le_of_lt (mul_pos (mul_pos (by linarith) ha_pos) hb'_pos)
          have h_cnt : ↑c.b_count * ((c.b_count : ℝ) - 1) +
              ↑c.b_count * ↑c.y_count +
              ↑c.y_count * ((c.y_count : ℝ) - 1) +
              (c.b_count : ℝ) * (c.y_count : ℝ) =
              (n : ℝ) * ((n : ℝ) - 1) := by nlinarith [h_sum]
          nlinarith [h_act, hPab, h_cnt]
        · -- x=0, b≥1, y=0: impossible (v > 0 requires x+y > 0)
          exfalso; omega
      · -- x=0, b=0: only yy survives
        have hb0 : c.b_count = 0 := by omega
        simp only [step_yb_none (by omega)]
        have hK_pos : (0 : ℝ) < ((16 * n + 7 : ℕ) : ℝ) ^ svb *
            ((16 * n - 5 : ℕ) : ℝ) ^ sxy /
            ((16 * n : ℕ) : ℝ) ^ (svb + sxy) :=
          div_pos (mul_pos (pow_pos hαvb_pos _) (pow_pos hαxy_pos _))
            (pow_pos hP_pos _)
        rw [(div_le_div_iff_of_pos_right hK_pos).symm]
        simp only [add_div]
        field_simp [hαvb_pos.ne', hαxy_pos.ne', hP_pos.ne', hf_pos.ne', hT_pos.ne',
          pow_ne_zero _ hαvb_pos.ne', pow_ne_zero _ hαxy_pos.ne',
          pow_ne_zero _ hP_pos.ne']
        simp only [interactionCount, countOf, totalPairs,
          show ¬(State.x = State.b) from by decide,
          show ¬(State.x = State.y) from by decide,
          show ¬(State.b = State.x) from by decide,
          show ¬(State.b = State.y) from by decide,
          show ¬(State.y = State.x) from by decide,
          show ¬(State.y = State.b) from by decide,
          ite_true, ite_false]
        simp only [show c.x_count = 0 from hx0, show c.b_count = 0 from hb0,
          Nat.zero_mul, Nat.mul_zero, Nat.zero_sub,
          Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
        have hy1 : c.y_count ≥ 1 := by omega
        push_cast [Nat.cast_sub hy1,
                   Nat.cast_sub (show 1 ≤ n from by omega),
                   Nat.cast_sub (show 5 ≤ 16 * n from by omega)]
        have hyn : (c.y_count : ℝ) = (n : ℝ) := by exact_mod_cast (show c.y_count = n from by omega)
        simp only [hyn]; linarith
    · -- **y = 0**: yb, xy, yx interactions have zero weight (symmetric to x=0)
      have hy0 : c.y_count = 0 := by omega
      simp only [step_yb_none (by omega), step_xy_none (by omega),
        step_yx_none (by omega)]
      by_cases hb1 : c.b_count ≥ 1
      · by_cases hx1 : c.x_count ≥ 1
        · -- y=0, b≥1, x≥1: xb succeeds
          have hpot_xb : (((c.stepOrSelf x b).potential : ℕ) : ℝ) =
              ((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1 := by
            have hstep : c.step x b = some ⟨c.x_count + 1, c.b_count - 1, c.y_count,
                by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos ⟨hx1, hb1⟩
            simp only [stepOrSelf, hstep, Option.getD_some]
            exact_mod_cast (show (_ : ℤ) = _ from by linarith [delta_f_xb c _ hstep])
          rw [hpot_xb]
          have hK_pos : (0 : ℝ) < ((16 * n + 7 : ℕ) : ℝ) ^ svb *
              ((16 * n - 5 : ℕ) : ℝ) ^ sxy /
              ((16 * n : ℕ) : ℝ) ^ (svb + sxy) :=
            div_pos (mul_pos (pow_pos hαvb_pos _) (pow_pos hαxy_pos _))
              (pow_pos hP_pos _)
          rw [(div_le_div_iff_of_pos_right hK_pos).symm]
          simp only [add_div]
          field_simp [hαvb_pos.ne', hαxy_pos.ne', hP_pos.ne', hf_pos.ne', hT_pos.ne',
            ha_pos.ne',
            pow_ne_zero _ hαvb_pos.ne', pow_ne_zero _ hαxy_pos.ne',
            pow_ne_zero _ hP_pos.ne']
          simp only [interactionCount, countOf, totalPairs,
            show ¬(State.x = State.b) from by decide,
            show ¬(State.x = State.y) from by decide,
            show ¬(State.b = State.x) from by decide,
            show ¬(State.b = State.y) from by decide,
            show ¬(State.y = State.x) from by decide,
            show ¬(State.y = State.b) from by decide,
            ite_true, ite_false]
          simp only [show c.y_count = 0 from hy0, Nat.zero_mul, Nat.mul_zero,
            Nat.zero_sub, Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
          push_cast [Nat.cast_sub hb1, Nat.cast_sub hx1,
                     Nat.cast_sub (show 1 ≤ n from by omega),
                     Nat.cast_sub (show 5 ≤ 16 * n from by omega)]
          have hf_eq : ((c.potential : ℕ) : ℝ) = ((c.u : ℤ) : ℝ) ^ 2 + 2 * (n : ℝ) := by
            exact_mod_cast (show (c.potential : ℤ) = c.u ^ 2 + 2 * ↑n from by
              simp [potential])
          have h_sum : (n : ℝ) = (c.x_count : ℝ) + (c.b_count : ℝ) := by
            exact_mod_cast (show n = c.x_count + c.b_count from by omega)
          -- h_int_R with y=0: xy term vanishes, only vb bound remains
          simp only [show (c.y_count : ℝ) = 0 from by exact_mod_cast hy0,
            zero_mul, mul_zero, add_zero] at h_int_R
          have hv_eq : (c.v : ℝ) = (c.x_count : ℝ) := by
            exact_mod_cast (show (c.v : ℕ) = c.x_count from by unfold v; omega)
          have h_act :
              ((c.potential : ℕ) : ℝ) * (16 * (n : ℝ) + 7) *
                (c.x_count : ℝ) * ↑c.b_count *
                (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) ≤
              (c.b_count : ℝ) * (c.x_count : ℝ) *
              (16 * (n : ℝ)) *
              (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1) *
              (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) := by
            have h_key := h_int_R
            rw [← hf_eq, hv_eq] at h_key
            have hu_eq : ((c.u : ℤ) : ℝ) = (c.x_count : ℝ) := by
              have : (c.u : ℤ) = (c.x_count : ℤ) := by
                simp only [u, Config.gap]
                rw [show (c.y_count : ℤ) = 0 from by exact_mod_cast hy0]; ring
              exact_mod_cast this
            rw [hu_eq] at h_key ⊢
            nlinarith [h_key, sq_nonneg (c.x_count : ℝ), sq_nonneg (c.b_count : ℝ),
              sq_nonneg ((c.potential : ℕ) : ℝ)]
          have hPab : (0 : ℝ) ≤ 16 * (n : ℝ) *
              (((c.potential : ℕ) : ℝ) + 2 * ((c.u : ℤ) : ℝ) + 1) *
              (((c.potential : ℕ) : ℝ) - 2 * ((c.u : ℤ) : ℝ) + 1) := by
            have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n from by omega)
            exact le_of_lt (mul_pos (mul_pos (by linarith) ha_pos) hb'_pos)
          have h_cnt : (c.x_count : ℝ) * ((c.x_count : ℝ) - 1) +
              ↑c.b_count * ↑c.x_count +
              ↑c.b_count * ((c.b_count : ℝ) - 1) +
              (c.b_count : ℝ) * (c.x_count : ℝ) =
              (n : ℝ) * ((n : ℝ) - 1) := by nlinarith [h_sum]
          nlinarith [h_act, hPab, h_cnt]
        · -- y=0, b≥1, x=0: impossible (v > 0)
          exfalso; omega
      · -- y=0, b=0: only xx survives
        have hb0 : c.b_count = 0 := by omega
        simp only [step_xb_none (by omega)]
        have hK_pos : (0 : ℝ) < ((16 * n + 7 : ℕ) : ℝ) ^ svb *
            ((16 * n - 5 : ℕ) : ℝ) ^ sxy /
            ((16 * n : ℕ) : ℝ) ^ (svb + sxy) :=
          div_pos (mul_pos (pow_pos hαvb_pos _) (pow_pos hαxy_pos _))
            (pow_pos hP_pos _)
        rw [(div_le_div_iff_of_pos_right hK_pos).symm]
        simp only [add_div]
        field_simp [hαvb_pos.ne', hαxy_pos.ne', hP_pos.ne', hf_pos.ne', hT_pos.ne',
          pow_ne_zero _ hαvb_pos.ne', pow_ne_zero _ hαxy_pos.ne',
          pow_ne_zero _ hP_pos.ne']
        simp only [interactionCount, countOf, totalPairs,
          show ¬(State.x = State.b) from by decide,
          show ¬(State.x = State.y) from by decide,
          show ¬(State.b = State.x) from by decide,
          show ¬(State.b = State.y) from by decide,
          show ¬(State.y = State.x) from by decide,
          show ¬(State.y = State.b) from by decide,
          ite_true, ite_false]
        simp only [show c.y_count = 0 from hy0, show c.b_count = 0 from hb0,
          Nat.zero_mul, Nat.mul_zero, Nat.zero_sub,
          Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
        have hx1 : c.x_count ≥ 1 := by omega
        push_cast [Nat.cast_sub hx1,
                   Nat.cast_sub (show 1 ≤ n from by omega),
                   Nat.cast_sub (show 5 ≤ 16 * n from by omega)]
        have hxn : (c.x_count : ℝ) = (n : ℝ) := by exact_mod_cast (show c.x_count = n from by omega)
        simp only [hxn]; linarith

/-- **Per-step supermartingale condition**: the expected value of M under
    one step of the absorbed augmented kernel is ≤ M. -/
theorem supermartingaleM_per_step (hn : n ≥ 2) (a : AugConfig n) :
    ∫⁻ a', supermartingaleM a' ∂(absorbedAugKernel hn a) ≤
    supermartingaleM a := by
  unfold absorbedAugKernel
  rw [Kernel.lintegral_piecewise]
  by_cases ha : a ∈ augActiveCentral
  · -- Active case: a.1 ∈ activeCentral
    rw [if_pos ha]
    -- The augmented transition kernel at a is (augStepDist a hn).toMeasure
    change ∫⁻ a', supermartingaleM a' ∂(augStepDist a hn).toMeasure ≤ _
    -- Express as a finite sum over interactions
    rw [lintegral_augStepDist a hn]
    -- Goal: ∑ q, M(augStep q) * pmf(q) ≤ M(a)
    -- This follows from `supermartingale_per_step` (CentralSupermartingale.lean)
    -- via the following chain in ℝ≥0∞:
    --
    -- 1. For "other" interactions (¬isVB ∧ ¬isXY): M(augStep) = M(a)
    --    because stepOrSelf preserves u (hence potential), and counters unchanged.
    -- 2. Factor out K = (16n+7)^s_vb · (16n-5)^s_xy / (16n)^(s_vb+s_xy)
    --    which is common to all terms and to M(a).
    -- 3. After factoring K, need:
    --    ∑_{other} count/f + (16n+7)/(16n)·(xb/f'_xb+yb/f'_yb)
    --      + (16n-5)/(16n)·(xy/f'_xy+yx/f'_yx) ≤ T/f
    -- 4. Cross-multiply by 16n·ab·f (all positive) to get:
    --    (16n+7)·f·b·(v(f+1)-2u²) + (16n-5)·f·2xy·(f+1) ≤ (bv+2xy)·16n·ab
    --    which is exactly `supermartingale_per_step`.
    exact supermartingaleM_per_step_ennreal a hn
        (augActiveCentral_mem_v_pos ha)
  · -- Absorbed case: identity kernel → integral = M(a)
    rw [if_neg ha, Kernel.id_apply, lintegral_dirac' a supermartingaleM_measurable]

/-! ### Iteration: E[M_t] ≤ M_0

By `lintegral_geometric_decay` with r = 1 and the per-step condition,
the expected value of M at time t is bounded by M at time 0.

This is the measure-theoretic content of Corollary 2 from the paper. -/

/-- **Supermartingale iteration**: E[M_t] ≤ M_0 for all t. -/
theorem supermartingaleM_iteration (hn : n ≥ 2)
    (a₀ : AugConfig n) (t : ℕ) :
    ∫⁻ a, supermartingaleM a ∂((absorbedAugKernel hn ^ t) a₀) ≤
    supermartingaleM a₀ := by
  have h := lintegral_geometric_decay
    (absorbedAugKernel hn) supermartingaleM supermartingaleM_measurable
    1 (fun a => by simpa using supermartingaleM_per_step hn a)
    t a₀
  simpa using h

/-! ### Projection to Config n: relating augmented and original chains

The probability that the original absorbed chain is still in activeCentral
equals the probability that the augmented chain's config component is in
activeCentral. -/

/-- One step of the absorbed augmented kernel projects to the absorbed
    central kernel: for any measurable set S of configs,
    augK(a)(Prod.fst⁻¹' S) = K_C(a.1)(S). -/
private theorem absorbedAugKernel_proj_step (hn : n ≥ 2) (a : AugConfig n)
    (S : Set (Config n)) (hS : MeasurableSet S) :
    (absorbedAugKernel hn a) {a' : AugConfig n | a'.1 ∈ S} =
    (absorbedKernelCentral hn a.1) S := by
  -- Both are piecewise kernels with the same condition
  unfold absorbedAugKernel absorbedKernelCentral
  simp only [Kernel.piecewise_apply', augActiveCentral, Set.mem_setOf_eq]
  by_cases ha : a.1 ∈ activeCentral
  · -- Active case: chain Measure.map_apply ← PMF.toMeasure_map ← proj
    rw [if_pos ha, if_pos ha]
    change (augStepDist a hn).toMeasure {a' | a'.1 ∈ S} =
         (a.1.stepDist hn).toMeasure S
    have hfst : Measurable (Prod.fst : AugConfig n → Config n) :=
      Measurable.of_discrete
    -- {a' | a'.1 ∈ S} = Prod.fst ⁻¹' S
    have hset : {a' : AugConfig n | a'.1 ∈ S} = Prod.fst ⁻¹' S :=
      Set.ext (fun _ => Iff.rfl)
    rw [hset, ← Measure.map_apply hfst hS]
    -- Goal: (augStepDist a hn).toMeasure.map Prod.fst S = stepDist.toMeasure S
    have h_map_eq : (augStepDist a hn).toMeasure.map Prod.fst =
        ((augStepDist a hn).map Prod.fst).toMeasure :=
      @PMF.toMeasure_map (AugConfig n) (Config n) Prod.fst _ _
          (augStepDist a hn) hfst
    rw [h_map_eq, augStepDist_proj_eq_stepDist]
  · -- Absorbed case: both are Dirac at respective states
    rw [if_neg ha, if_neg ha, Kernel.id_apply, Kernel.id_apply]
    rw [Measure.dirac_apply' a
          (instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _),
        Measure.dirac_apply' a.1 hS]
    simp [Set.indicator]

/-- **Projection lemma (general)**: The absorbed augmented kernel's measure
    of `Prod.fst ⁻¹' S` equals the original absorbed central kernel's
    measure of `S`, for all measurable S and all starting states. -/
private theorem augKernel_proj_forall (hn : n ≥ 2) (a₀ : AugConfig n) (t : ℕ)
    (S : Set (Config n)) (hS : MeasurableSet S) :
    ((absorbedAugKernel hn ^ t) a₀) (Prod.fst ⁻¹' S) =
    ((absorbedKernelCentral hn ^ t) a₀.1) S := by
  induction t generalizing S with
  | zero =>
    simp only [pow_zero]
    change Kernel.id a₀ _ = Kernel.id a₀.1 _
    rw [Kernel.id_apply, Kernel.id_apply,
        Measure.dirac_apply' a₀
          (instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _),
        Measure.dirac_apply' a₀.1 hS]
    simp only [Set.indicator, Set.mem_preimage]
    split <;> rfl
  | succ t ih =>
    rw [Kernel.pow_succ_apply_eq_lintegral _ _ _
          (instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _),
        Kernel.pow_succ_apply_eq_lintegral _ _ _ hS]
    -- Step 1: Rewrite integrand using one-step projection
    have h_proj : ∀ a : AugConfig n,
        (absorbedAugKernel hn a) (Prod.fst ⁻¹' S) =
        (absorbedKernelCentral hn a.1) S := fun a =>
      absorbedAugKernel_proj_step hn a S hS
    simp_rw [h_proj]
    -- Goal: ∫ g(a.1) d(K_aug^t a₀) = ∫ g(c) d(K_C^t a₀.1)
    -- Step 2: Change of variables via Prod.fst
    rw [← lintegral_map (Kernel.measurable_coe _ hS) Measurable.of_discrete]
    -- Step 3: The pushed-forward measure equals the config kernel by IH
    congr 1
    exact Measure.ext (fun S' hS' => by
      rw [Measure.map_apply Measurable.of_discrete hS']
      exact ih S' hS')

/-- The absorbed augmented kernel's projection to Config n matches the
    original absorbed kernel for central. -/
theorem augKernel_proj_eq_absorbedCentral (hn : n ≥ 2)
    (c₀ : Config n) (t : ℕ) :
    ((absorbedAugKernel hn ^ t) (c₀, 0, 0))
      {a : AugConfig n | a.1 ∈ activeCentral} =
    ((absorbedKernelCentral hn ^ t) c₀) activeCentral :=
  augKernel_proj_forall hn (c₀, 0, 0) t activeCentral
    (instDiscreteMeasurableSpaceConfig.forall_measurableSet _)

/-! ### Bounds from the M supermartingale (Corollary 2 from the paper)

From E[M_t] ≤ M_0 and f ≤ n²+2n, we extract:
  E[α_vb^{S^vb} · α_xy^{S^xy}] ≤ (n²+2n) / f₀

This is the correct form of Corollary 2: the paper bounds the COMBINED
product α_vb^{S^vb}·α_xy^{S^xy} = M·f, not α_vb^{S^vb} alone.

Combined with the structural bound S^xy ≤ S^vb + n (blank conservation)
and Markov's inequality, this gives tail bounds on S^vb. -/

/-- **Product bound**: The numerator of M (= α_vb^{s_vb}·α_xy^{s_xy})
    satisfies E[product] ≤ (n²+2n)/f₀.

    Proof: M = product/f, so product = M·f ≤ M·(n²+2n), and
    E[M] ≤ 1/f₀ by supermartingaleM_iteration. -/
theorem expected_product_bound (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    ∫⁻ a, (((16 * n + 7 : ℕ) : ℝ≥0∞) ^ a.2.1 *
           ((16 * n - 5 : ℕ) : ℝ≥0∞) ^ a.2.2) /
          ((16 * n : ℕ) : ℝ≥0∞) ^ (a.2.1 + a.2.2)
    ∂((absorbedAugKernel hn ^ t) (c₀, 0, 0)) ≤
    ((n ^ 2 + 2 * n : ℕ) : ℝ≥0∞) / ((c₀.potential : ℕ) : ℝ≥0∞) := by
  -- Strategy: integrand(a) ≤ (n²+2n) · supermartingaleM(a),
  -- integrate, apply supermartingaleM_iteration, simplify M₀ = 1/f₀.
  set P : ℝ≥0∞ := ↑(n ^ 2 + 2 * n : ℕ) with hP_def
  set μ := (absorbedAugKernel hn ^ t) (c₀, 0, 0) with hμ_def
  -- Pointwise bound: integrand ≤ P * M
  have hpw : ∀ a : AugConfig n,
      (((16 * n + 7 : ℕ) : ℝ≥0∞) ^ a.2.1 *
       ((16 * n - 5 : ℕ) : ℝ≥0∞) ^ a.2.2) /
      ((16 * n : ℕ) : ℝ≥0∞) ^ (a.2.1 + a.2.2) ≤
      P * supermartingaleM a := by
    intro a
    simp only [supermartingaleM]
    -- Goal: N / D ≤ P * (N / (D * F))
    set N := ((16 * n + 7 : ℕ) : ℝ≥0∞) ^ a.2.1 *
             ((16 * n - 5 : ℕ) : ℝ≥0∞) ^ a.2.2
    set D := ((16 * n : ℕ) : ℝ≥0∞) ^ (a.2.1 + a.2.2)
    set F := ((a.1.potential : ℕ) : ℝ≥0∞)
    have hD_ne : D ≠ 0 := by
      apply pow_ne_zero; exact_mod_cast (by omega : 16 * n ≠ 0)
    have hD_top : D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    have hF_ne : F ≠ 0 := by
      simp only [F, ne_eq, Nat.cast_eq_zero]
      exact (potential_pos a.1 (by omega : n ≥ 1)).ne'
    have hF_top : F ≠ ⊤ := ENNReal.natCast_ne_top _
    have hDF_ne : D * F ≠ 0 := mul_ne_zero hD_ne hF_ne
    have hDF_top : D * F ≠ ⊤ := ENNReal.mul_ne_top hD_top hF_top
    have hFP : F ≤ P := by
      simp only [F, P]; exact_mod_cast potential_le a.1
    -- Strategy: N/D ≤ N/D * (P/F) = P * (N/(D*F))
    -- since 1 ≤ P/F (from F ≤ P).
    have hPF : (1 : ℝ≥0∞) ≤ P / F := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hF_ne) (Or.inl hF_top)]
      simpa using hFP
    have hfact : N / D * (P / F) = P * (N / (D * F)) := by
      simp only [div_eq_mul_inv]
      rw [ENNReal.mul_inv (Or.inl hD_ne) (Or.inl hD_top)]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    calc N / D ≤ N / D * (P / F) :=
          le_mul_of_one_le_right (zero_le') hPF
      _ = P * (N / (D * F)) := hfact
  -- Main calc chain
  calc ∫⁻ a, (((16 * n + 7 : ℕ) : ℝ≥0∞) ^ a.2.1 *
             ((16 * n - 5 : ℕ) : ℝ≥0∞) ^ a.2.2) /
            ((16 * n : ℕ) : ℝ≥0∞) ^ (a.2.1 + a.2.2) ∂μ
      ≤ ∫⁻ a, P * supermartingaleM a ∂μ := lintegral_mono hpw
    _ = P * ∫⁻ a, supermartingaleM a ∂μ :=
        lintegral_const_mul P supermartingaleM_measurable
    _ ≤ P * supermartingaleM (c₀, 0, 0) := by
        apply mul_le_mul_left'
        exact supermartingaleM_iteration hn (c₀, 0, 0) t
    _ = P / ((c₀.potential : ℕ) : ℝ≥0∞) := by
        unfold supermartingaleM
        simp [P, div_eq_mul_inv]

/-! ### Exponential bounds for the counting supermartingale

The counting supermartingale per-step condition requires bounding exp(1/n)
from above and exp(-k/n) from below. We use:

1. **Padé upper bound**: exp(x)·(2-x) ≤ 2+x for x ≥ 0.
   Equivalently, exp(x) ≤ (2+x)/(2-x) for 0 ≤ x < 2.
   Proof: g(x) = (2+x) - (2-x)·exp(x) satisfies g(0) = 0 and
   g'(x) = 1 - (1-x)·exp(x) ≥ 0 (from `add_one_le_exp`), so g ≥ 0.

2. **Reciprocal bound**: exp(-x) ≤ 1/(1+x) for x ≥ 0.
   From add_one_le_exp: 1+x ≤ exp(x), so exp(-x) ≤ 1/(1+x). -/

/-- (1-x)·exp(x) ≤ 1 for all x. Key step for Padé bound.
    When x ≤ 1: from `add_one_le_exp(-x)`, 1-x ≤ exp(-x), so (1-x)·exp(x) ≤ 1.
    When x > 1: (1-x) < 0, so (1-x)·exp(x) < 0 < 1. -/
private theorem one_sub_mul_exp_le_one (x : ℝ) : (1 - x) * Real.exp x ≤ 1 := by
  by_cases hx : x ≤ 1
  · -- 1-x ≥ 0 and 1-x ≤ exp(-x), so (1-x)*exp(x) ≤ exp(-x)*exp(x) = 1
    have h1 := Real.add_one_le_exp (-x)  -- -x + 1 ≤ exp(-x)
    have h2 : (1 - x) ≤ Real.exp (-x) := by linarith
    have h3 : 0 ≤ Real.exp x := Real.exp_nonneg x
    calc (1 - x) * Real.exp x
        ≤ Real.exp (-x) * Real.exp x := by exact mul_le_mul_of_nonneg_right h2 h3
      _ = Real.exp ((-x) + x) := by rw [← Real.exp_add]
      _ = Real.exp 0 := by ring_nf
      _ = 1 := Real.exp_zero
  · -- 1-x < 0
    have : 1 - x < 0 := by linarith
    calc (1 - x) * Real.exp x
        ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt this) (Real.exp_nonneg x)
      _ ≤ 1 := zero_le_one

/-- **Padé upper bound**: (2-x)·exp(x) ≤ 2+x for x ≥ 0.
    Proof: g(x) = (2+x) - (2-x)·exp(x) is monotone nondecreasing
    (since g'(x) = 1-(1-x)·exp(x) ≥ 0) and g(0) = 0, so g ≥ 0. -/
theorem exp_mul_two_sub_le (x : ℝ) (hx : 0 ≤ x) :
    (2 - x) * Real.exp x ≤ 2 + x := by
  suffices h : 0 ≤ (2 + x) - (2 - x) * Real.exp x by linarith
  -- Define g(t) = (2+t) - (2-t)·exp(t). Show g(x) ≥ 0.
  set g : ℝ → ℝ := fun t => (2 + t) - (2 - t) * Real.exp t with hg_def
  show 0 ≤ g x
  have hg0 : g 0 = 0 := by simp [hg_def, Real.exp_zero]
  -- g has derivative 1 - (1-t)·exp(t) at every point
  have hg_hd : ∀ t, HasDerivAt g (1 - (1 - t) * Real.exp t) t := by
    intro t
    have hd1 : HasDerivAt (fun t => (2 : ℝ) + t) 1 t :=
      (hasDerivAt_id t).const_add 2
    have hd2 : HasDerivAt (fun t => (2 : ℝ) - t) (-1) t :=
      (hasDerivAt_id t).const_sub 2
    have hd3 : HasDerivAt (fun t => (2 - t) * Real.exp t)
      ((-1) * Real.exp t + (2 - t) * Real.exp t) t :=
      hd2.mul (Real.hasDerivAt_exp t)
    have hd := hd1.sub hd3
    convert hd using 1; ring
  -- g is monotone: derivative ≥ 0 (from one_sub_mul_exp_le_one)
  have hg_mono : Monotone g :=
    monotone_of_deriv_nonneg (fun t => (hg_hd t).differentiableAt) fun t => by
      rw [(hg_hd t).deriv]; linarith [one_sub_mul_exp_le_one t]
  -- g(0) = 0 and g monotone → g(x) ≥ 0 for x ≥ 0
  linarith [hg_mono hx]

/-- exp(-x) ≤ 1/(1+x) for x ≥ 0. From add_one_le_exp: 1+x ≤ exp(x). -/
theorem exp_neg_le_inv_one_add {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 / (1 + x) := by
  have hpos : (0 : ℝ) < 1 + x := by linarith
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hpos (by linarith [Real.add_one_le_exp x])

/-! ### Counting supermartingale (Lemma 5)

The counting supermartingale C_t = exp((S^c_t - 130·S^vb_t - 258·S^xy_t)/n)
satisfies E[C_{τ∧t}] ≤ 1, where τ is the exit time from central.

The per-step condition: while in central, for each interaction type:
  - Other (neither vb nor xy): Δ(S^c - 130·S^vb - 258·S^xy) = +1
  - VB: Δ(...) = 1 - 130 = -129
  - XY: Δ(...) = 1 - 258 = -257

The weighted average of exp(Δ/n) must be ≤ 1:
  (T - bv - 2xy)·exp(1/n) + bv·exp(-129/n) + 2xy·exp(-257/n) ≤ T

This holds in the central region because bv + 2xy ≥ Ω(n²) while
T = n(n-1)/2. The constants 130 and 258 are chosen so that the
exponential factors compensate the "other" interactions. -/

-- Helper: In the central region, 64·(bv + 2xy) ≥ (7n-1)(n+1).
-- Here bv + 2xy = x(n-x) + y(n-y) (the "self-interaction complement").
private lemma central_bvxy_lower_bound (x y n : ℤ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hn0 : 0 ≤ n)
    (hx7 : 8 * x ≤ 7 * n - 1) (hy7 : 8 * y ≤ 7 * n - 1)
    (hv8 : n + 1 ≤ 8 * (x + y)) :
    (7 * n - 1) * (n + 1) ≤
      64 * (x * (n - x) + y * (n - y)) := by
  by_cases hs : 8 * (x + y) ≤ 7 * n - 1
  · -- Case: 8(x+y) ≤ 7n-1  →  both slacks for v and b are non-negative.
    -- Product: (8v-(n+1))(7n-1-8v) ≥ 0  →  64·v(n-v) ≥ (7n-1)(n+1).
    -- Then x²+y² ≤ (x+y)² from xy ≥ 0, so x(n-x)+y(n-y) ≥ v(n-v).
    have hxy : 0 ≤ x * y := mul_nonneg hx0 hy0
    have hslack : 0 ≤ (8 * (x + y) - (n + 1)) * (7 * n - 1 - 8 * (x + y)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg (x - y)]
  · -- Case: 8(x+y) > 7n-1  →  the "other" term (n+1)(8v-7n+1) is non-negative.
    -- Identity: 64f - (7n-1)(n+1) = 8x(7n-1-8x) + 8y(7n-1-8y) + (n+1)(8v-7n+1).
    push_neg at hs
    have h1 : 0 ≤ x * (7 * n - 1 - 8 * x) := mul_nonneg hx0 (by linarith)
    have h2 : 0 ≤ y * (7 * n - 1 - 8 * y) := mul_nonneg hy0 (by linarith)
    have h3 : 0 ≤ (n + 1) * (8 * (x + y) - 7 * n + 1) :=
      mul_nonneg (by linarith) (by omega)
    nlinarith

-- Helper: The cubic bound (7n-1)(n+1)(260n+129) ≥ 128n(n-1)(n+129) for n ≥ 9.
-- Polynomial division: LHS - RHS = (n-9)(1692n²+1307n+28789) + 258972 ≥ 0.
private lemma cubic_bound (n : ℤ) (hn : 9 ≤ n) :
    128 * n * (n - 1) * (n + 129) ≤
      (7 * n - 1) * (n + 1) * (260 * n + 129) := by
  have h1 : 0 ≤ (n - 9) * (1692 * n ^ 2 + 1307 * n + 28789) :=
    mul_nonneg (by linarith) (by nlinarith [sq_nonneg n])
  nlinarith [sq_nonneg n]

-- The polynomial inequality underlying the counting supermartingale.
-- Split into small n (interval_cases) and large n (helper lemma chain).
set_option maxHeartbeats 6400000 in
private theorem counting_poly_core (x b y n : ℤ)
    (hn : 2 ≤ n) (hsum : x + b + y = n)
    (hx0 : 0 ≤ x) (hb0 : 0 ≤ b) (hy0 : 0 ≤ y)
    (hx7 : 8 * x ≤ 7 * n - 1) (hb7 : 8 * b ≤ 7 * n - 1) (hy7 : 8 * y ≤ 7 * n - 1)
    (hv : 1 ≤ x + y) :
    2 * n * (n - 1) * (n + 129) * (n + 257) ≤
    b * (x + y) * (n + 257) * (260 * n + 129) +
    2 * x * y * (n + 129) * (516 * n + 257) := by
  by_cases hn8 : n ≤ 8
  · -- Small n (2 ≤ n ≤ 8): substitute b, enumerate all integer points.
    have hb_eq : b = n - x - y := by linarith
    subst hb_eq
    have hxn : x ≤ n := by linarith
    have hyn : y ≤ n := by linarith
    interval_cases n <;> interval_cases x <;> interval_cases y <;> omega
  · -- Large n (n ≥ 9): chain helper lemmas.
    push_neg at hn8
    -- Identity: bv + 2xy = x(n-x) + y(n-y) (used to bridge between the two forms)
    have hid : b * (x + y) + 2 * x * y = x * (n - x) + y * (n - y) := by
      have : b = n - x - y := by linarith
      nlinarith
    -- Central slack: 8(x+y) ≥ n+1 (from 8b ≤ 7n-1 and b = n-x-y)
    have hv8 : n + 1 ≤ 8 * (x + y) := by linarith
    -- Step 1: 64·(bv+2xy) ≥ (7n-1)(n+1)
    have hbvxy := central_bvxy_lower_bound x y n hx0 hy0 (by linarith) hx7 hy7 hv8
    -- Step 2: (7n-1)(n+1)(260n+129) ≥ 128n(n-1)(n+129)
    have hcub := cubic_bound n (show 9 ≤ n by linarith)
    -- Step 3: Weight inequality  (n+129)(516n+257) ≥ (n+257)(260n+129) for n ≥ 1
    -- Difference = 128n(2n-1) ≥ 0, so 2xy·(excess) ≥ 0.
    have hxy_excess : 0 ≤ x * y * (128 * n * (2 * n - 1)) :=
      mul_nonneg (mul_nonneg hx0 hy0) (by nlinarith)
    -- Step 4: Multiply hbvxy by W = (n+257)(260n+129) ≥ 0
    have hn257 : (0 : ℤ) ≤ n + 257 := by linarith
    have h260 : (0 : ℤ) ≤ 260 * n + 129 := by nlinarith
    have hW : (0 : ℤ) ≤ (n + 257) * (260 * n + 129) := mul_nonneg hn257 h260
    have hS_bound :
        (7 * n - 1) * (n + 1) * ((n + 257) * (260 * n + 129)) ≤
        64 * (x * (n - x) + y * (n - y)) * ((n + 257) * (260 * n + 129)) :=
      mul_le_mul_of_nonneg_right hbvxy hW
    -- Step 5: Regroup hcub to match hS_bound's LHS parenthesization
    have hcub_ext :
        128 * n * (n - 1) * (n + 129) * (n + 257) ≤
        (7 * n - 1) * (n + 1) * ((n + 257) * (260 * n + 129)) := by
      nlinarith [hcub]
    -- Step 6: Chain: 64·LHS ≤ P·W ≤ 64·S·W, so LHS ≤ S·W
    have h_chain := le_trans hcub_ext hS_bound
    -- h_chain: 128n(n-1)(n+129)(n+257) ≤ 64·S·W
    -- Divide both sides by 64 (linarith handles integer scaling):
    have h_SW : 2 * n * (n - 1) * (n + 129) * (n + 257) ≤
        (x * (n - x) + y * (n - y)) * ((n + 257) * (260 * n + 129)) := by
      linarith
    -- Step 7: Express b·v in terms of S: b(x+y) = S - 2xy
    have hb_sub : b * (x + y) = (x * (n - x) + y * (n - y)) - 2 * x * y := by
      linarith [hid]
    -- Step 8: RHS = b(x+y)·W + 2xy·W₂ = (S-2xy)·W + 2xy·W₂ = S·W + 2xy·(W₂-W)
    -- Weight excess: W₂ - W = (n+129)(516n+257) - (n+257)(260n+129) = 128n(2n-1)
    -- So 2xy·(W₂-W) = 2xy·128n(2n-1) ≥ 0, meaning RHS ≥ S·W ≥ LHS.
    nlinarith [hb_sub, h_SW, hxy_excess]

/-- bv + 2xy ≤ totalPairs n: VB and XY interactions are a subset of all. -/
private theorem bv_xy2_le_totalPairs (c : Config n) :
    c.b_count * c.v + 2 * c.x_count * c.y_count ≤ totalPairs n := by
  -- T - bv - 2xy = x(x-1) + y(y-1) + b(b-1) + xb + by ≥ 0
  unfold v totalPairs
  have h := c.sum_eq
  -- Cast to ℤ: ↑(a ≤ b) ↔ (↑a : ℤ) ≤ ↑b
  rw [← Nat.cast_le (α := ℤ)]
  push_cast
  -- Goal: ↑b*(↑x+↑y) + 2*↑x*↑y ≤ ↑n * ↑(n-1 : ℕ)
  have hh : (c.x_count : ℤ) + ↑c.b_count + ↑c.y_count = ↑n := by exact_mod_cast h
  -- Five non-negative deficiency components: n(n-1) - bv - 2xy = Σ these
  have h1 : 0 ≤ (c.x_count : ℤ) * ↑c.b_count :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h2 : 0 ≤ (c.b_count : ℤ) * ↑c.y_count :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h3 : 0 ≤ (c.x_count : ℤ) * (↑c.x_count - 1) := by
    rcases Nat.eq_zero_or_pos c.x_count with heq | hpos
    · simp [heq]
    · exact mul_nonneg (by omega) (by omega)
  have h4 : 0 ≤ (c.b_count : ℤ) * (↑c.b_count - 1) := by
    rcases Nat.eq_zero_or_pos c.b_count with heq | hpos
    · simp [heq]
    · exact mul_nonneg (by omega) (by omega)
  have h5 : 0 ≤ (c.y_count : ℤ) * (↑c.y_count - 1) := by
    rcases Nat.eq_zero_or_pos c.y_count with heq | hpos
    · simp [heq]
    · exact mul_nonneg (by omega) (by omega)
  -- Main inequality: eliminate ↑n via hh, then nlinarith uses the deficiency
  have h_main : (c.b_count : ℤ) * (↑c.x_count + ↑c.y_count) +
      2 * ↑c.x_count * ↑c.y_count ≤ ↑n * (↑n - 1) := by
    rw [show (↑n : ℤ) = ↑c.x_count + ↑c.b_count + ↑c.y_count from by linarith]
    nlinarith [h1, h2, h3, h4, h5]
  -- Step 2: Bridge ℕ cast gap: ↑(n-1:ℕ) ≥ ↑n - 1, so ↑n*↑(n-1:ℕ) ≥ ↑n*(↑n-1)
  have h_cast : (↑n : ℤ) * (↑n - 1) ≤ ↑n * ↑(n - 1 : ℕ) :=
    mul_le_mul_of_nonneg_left (by omega) (Nat.cast_nonneg _)
  linarith

set_option maxHeartbeats 800000 in
theorem counting_supermartingale_per_step (c : Config n) (hn : n ≥ 2)
    (hc : c.inCentral) (hv : 0 < c.v) :
    ((totalPairs n - c.b_count * c.v - 2 * c.x_count * c.y_count : ℕ) : ℝ) *
      Real.exp (1 / (n : ℝ)) +
    (c.b_count * c.v : ℕ) * Real.exp (-129 / (n : ℝ)) +
    (2 * c.x_count * c.y_count : ℕ) * Real.exp (-257 / (n : ℝ)) ≤
    (totalPairs n : ℝ) := by
  set T := totalPairs n; set bv := c.b_count * c.v
  set xy2 := 2 * c.x_count * c.y_count
  have hTge : bv + xy2 ≤ T := bv_xy2_le_totalPairs c
  -- ℝ casts
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- exp(1/n) · (2n-1) ≤ 2n+1  [Padé]
  have hexp1 : Real.exp (1 / (n : ℝ)) * (2 * ↑n - 1) ≤ 2 * ↑n + 1 := by
    have h := exp_mul_two_sub_le (1 / (n : ℝ)) (by positivity)
    have h' := mul_le_mul_of_nonneg_right h (le_of_lt hn_pos)
    have hL : (2 - 1 / (n : ℝ)) * ↑n = 2 * ↑n - 1 := by
      rw [sub_mul, one_div, inv_mul_cancel₀ hne]
    have hR : (2 + 1 / (n : ℝ)) * ↑n = 2 * ↑n + 1 := by
      rw [add_mul, one_div, inv_mul_cancel₀ hne]
    nlinarith [Real.exp_pos (1 / (↑n : ℝ))]
  -- exp(-129/n) · (n+129) ≤ n  [reciprocal]
  have hexp129 : Real.exp (-(129 : ℝ) / ↑n) * (↑n + 129) ≤ ↑n := by
    have h := exp_neg_le_inv_one_add (show (0 : ℝ) ≤ 129 / ↑n by positivity)
    simp only [neg_div] -- normalize -129/n to -(129/n) in goal to match h
    have hd : (0 : ℝ) < 1 + 129 / ↑n := by positivity
    have h1 : Real.exp (-(129 / ↑n)) * (1 + 129 / ↑n) ≤ 1 := by
      calc Real.exp (-(129 / ↑n)) * (1 + 129 / ↑n)
          ≤ 1 / (1 + 129 / ↑n) * (1 + 129 / ↑n) :=
            mul_le_mul_of_nonneg_right h (le_of_lt hd)
        _ = 1 := by rw [one_div, inv_mul_cancel₀ (ne_of_gt hd)]
    have h2 : (1 + 129 / (n : ℝ)) * ↑n = ↑n + 129 := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hne]
    nlinarith [Real.exp_pos (-(129 / (↑n : ℝ)))]
  -- exp(-257/n) · (n+257) ≤ n  [reciprocal]
  have hexp257 : Real.exp (-(257 : ℝ) / ↑n) * (↑n + 257) ≤ ↑n := by
    have h := exp_neg_le_inv_one_add (show (0 : ℝ) ≤ 257 / ↑n by positivity)
    simp only [neg_div]
    have hd : (0 : ℝ) < 1 + 257 / ↑n := by positivity
    have h1 : Real.exp (-(257 / ↑n)) * (1 + 257 / ↑n) ≤ 1 := by
      calc Real.exp (-(257 / ↑n)) * (1 + 257 / ↑n)
          ≤ 1 / (1 + 257 / ↑n) * (1 + 257 / ↑n) :=
            mul_le_mul_of_nonneg_right h (le_of_lt hd)
        _ = 1 := by rw [one_div, inv_mul_cancel₀ (ne_of_gt hd)]
    have h2 : (1 + 257 / (n : ℝ)) * ↑n = ↑n + 257 := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hne]
    nlinarith [Real.exp_pos (-(257 / (↑n : ℝ)))]
  -- Polynomial inequality from central region
  have hcb : 8 * c.b_count < 7 * n := by
    unfold inCentral inLargeB at hc; push_neg at hc; exact hc.1
  have hcxy := c.central_xy_upper hc
  have hpoly := counting_poly_core (↑c.x_count) (↑c.b_count) (↑c.y_count) (↑n)
    (by exact_mod_cast hn) (by exact_mod_cast c.sum_eq)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by clear_value T bv xy2; have := hcxy.1; omega)
    (by clear_value T bv xy2; have := hcb; omega)
    (by clear_value T bv xy2; have := hcxy.2; omega)
    (by exact_mod_cast hv)
  -- Cast to ℝ
  have hpR : (2 : ℝ) * ↑n * (↑n - 1) * (↑n + 129) * (↑n + 257) ≤
      ↑c.b_count * (↑c.x_count + ↑c.y_count) * (↑n + 257) * (260 * ↑n + 129) +
      2 * ↑c.x_count * ↑c.y_count * (↑n + 129) * (516 * ↑n + 257) := by
    exact_mod_cast hpoly
  -- Express quantities in ℝ
  have hoR : (↑(T - bv - xy2) : ℝ) = ↑T - ↑bv - ↑xy2 := by
    have h1 : bv ≤ T := by omega
    have h2 : xy2 ≤ T - bv := by omega
    simp only [Nat.cast_sub h2, Nat.cast_sub h1]
  have hTR : (↑T : ℝ) = ↑n * (↑n - 1) := by
    show (totalPairs n : ℝ) = _
    unfold totalPairs; push_cast [Nat.cast_sub (show 1 ≤ n by omega)]; ring
  -- Positivity of denominators
  have h2n1_pos : (0 : ℝ) < 2 * ↑n - 1 := by nlinarith
  have hn129_pos : (0 : ℝ) < ↑n + 129 := by nlinarith
  have hn257_pos : (0 : ℝ) < ↑n + 257 := by nlinarith
  -- Convert exp bounds to division form
  have he1 : Real.exp (1 / ↑n) ≤ (2 * ↑n + 1) / (2 * ↑n - 1) := by
    rw [le_div_iff₀ h2n1_pos]; exact hexp1
  have he129 : Real.exp (-(129 : ℝ) / ↑n) ≤ ↑n / (↑n + 129) := by
    rw [le_div_iff₀ hn129_pos]; exact hexp129
  have he257 : Real.exp (-(257 : ℝ) / ↑n) ≤ ↑n / (↑n + 257) := by
    rw [le_div_iff₀ hn257_pos]; exact hexp257
  -- Upper bound by fractions
  have hfrac :
      (↑(T - bv - xy2) : ℝ) * Real.exp (1 / ↑n) +
      ↑bv * Real.exp (-(129 : ℝ) / ↑n) +
      ↑xy2 * Real.exp (-(257 : ℝ) / ↑n) ≤
      (↑(T - bv - xy2) : ℝ) * ((2 * ↑n + 1) / (2 * ↑n - 1)) +
      (↑bv : ℝ) * (↑n / (↑n + 129)) +
      (↑xy2 : ℝ) * (↑n / (↑n + 257)) :=
    add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left he1 (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left he129 (Nat.cast_nonneg _)))
      (mul_le_mul_of_nonneg_left he257 (Nat.cast_nonneg _))
  -- Suffices: the fraction bound ≤ T
  suffices hsuff :
      (↑(T - bv - xy2) : ℝ) * ((2 * ↑n + 1) / (2 * ↑n - 1)) +
      (↑bv : ℝ) * (↑n / (↑n + 129)) +
      (↑xy2 : ℝ) * (↑n / (↑n + 257)) ≤ (↑T : ℝ) by linarith
  -- Clear denominators
  have hne1 : (2 * (↑n : ℝ) - 1) ≠ 0 := ne_of_gt h2n1_pos
  have hne2 : ((↑n : ℝ) + 129) ≠ 0 := ne_of_gt hn129_pos
  have hne3 : ((↑n : ℝ) + 257) ≠ 0 := ne_of_gt hn257_pos
  -- Rewrite a*(b/c) to (a*b)/c for div_add_div
  simp only [← mul_div_assoc]
  rw [div_add_div _ _ hne1 hne2, div_add_div _ _ (mul_ne_zero hne1 hne2) hne3,
      div_le_iff₀ (mul_pos (mul_pos h2n1_pos hn129_pos) hn257_pos)]
  -- ℕ→ℝ cast equalities for products
  have hbvR : (↑bv : ℝ) = ↑c.b_count * (↑c.x_count + ↑c.y_count) := by
    show (↑(c.b_count * c.v) : ℝ) = _; simp only [v]; push_cast; ring
  have hxy2R : (↑xy2 : ℝ) = 2 * ↑c.x_count * ↑c.y_count := by
    show (↑(2 * c.x_count * c.y_count) : ℝ) = _; push_cast; ring
  -- Substitute ℕ→ℝ equalities to reduce to basic variables, then nlinarith
  rw [hoR, hTR, hbvR, hxy2R]
  nlinarith [hpR, Nat.cast_nonneg (α := ℝ) c.b_count,
             Nat.cast_nonneg (α := ℝ) c.x_count, Nat.cast_nonneg (α := ℝ) c.y_count]

/-! ### Counting Z supermartingale (contractive form)

Define W(a) = exp((-130·s_vb - 258·s_xy)/n). This is the "time-removed"
counting supermartingale. Under the absorbed augmented kernel:
- Active case: E[W'] ≤ exp(-1/n)·W  (contraction from counting_supermartingale_per_step)
- Absorbed case: E[W'] = W ≤ 1·W

So W is a supermartingale (r=1) and E[W_t] ≤ 1. -/

/-- The counting function W on augmented state (time-removed form). -/
noncomputable def countingW (a : AugConfig n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((-130 * (a.2.1 : ℝ) - 258 * (a.2.2 : ℝ)) / (n : ℝ)))

private theorem countingW_measurable :
    Measurable (countingW : AugConfig n → ℝ≥0∞) :=
  fun _ _ => instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _

/-- **Counting W per-step**: E[W'] ≤ W under the absorbed augmented kernel.
    Follows from counting_supermartingale_per_step after converting to ENNReal. -/
theorem countingW_per_step (hn : n ≥ 2) (a : AugConfig n) :
    ∫⁻ a', countingW a' ∂(absorbedAugKernel hn a) ≤ countingW a := by
  unfold absorbedAugKernel
  rw [Kernel.lintegral_piecewise]
  by_cases ha : a ∈ augActiveCentral
  · -- Active case: augmented transition preserves or decreases W
    rw [if_pos ha]
    change ∫⁻ a', countingW a' ∂(augStepDist a hn).toMeasure ≤ _
    rw [lintegral_augStepDist a hn]
    obtain ⟨c, svb, sxy⟩ := a
    -- Key fact: augStep only increments counters → countingW can only decrease
    have hle : ∀ q : State × State,
        countingW (augStep c svb sxy q.1 q.2) ≤ countingW (c, svb, sxy) := by
      intro ⟨i, r⟩
      simp only [countingW, augStep]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg' n)
      simp only [Nat.cast_add, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one]
      have h1 : (0 : ℝ) ≤ if isVB i r then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      have h2 : (0 : ℝ) ≤ if isXY i r then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      linarith
    calc ∑ q, countingW (augStep c svb sxy q.1 q.2) * (c.interactionPMF hn q)
        ≤ ∑ q, countingW (c, svb, sxy) * (c.interactionPMF hn q) :=
          Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_right (hle q) (zero_le'))
      _ = countingW (c, svb, sxy) * ∑ q, (c.interactionPMF hn q) := by
          rw [← Finset.mul_sum]
      _ ≤ countingW (c, svb, sxy) := by
          apply mul_le_of_le_one_right (zero_le')
          calc ∑ q : State × State, (c.interactionPMF hn q)
              ≤ ∑' q, (c.interactionPMF hn q) := ENNReal.sum_le_tsum _
            _ = 1 := (c.interactionPMF hn).tsum_coe
  · -- Absorbed case: identity kernel → integral = W(a)
    rw [if_neg ha, Kernel.id_apply, lintegral_dirac' a countingW_measurable]

/-- **Counting W iteration**: E[W_t] ≤ 1 for initial state (c₀, 0, 0). -/
theorem countingW_iteration (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    ∫⁻ a, countingW a ∂((absorbedAugKernel hn ^ t) (c₀, 0, 0)) ≤ 1 := by
  have h := lintegral_geometric_decay
    (absorbedAugKernel hn) countingW countingW_measurable
    1 (fun a => by simpa using countingW_per_step hn a) t (c₀, 0, 0)
  simp only [one_mul, pow_one] at h ⊢
  calc ∫⁻ a, countingW a ∂((absorbedAugKernel hn ^ t) (c₀, 0, 0))
      ≤ 1 ^ t * countingW (c₀, 0, 0) := h
    _ = countingW (c₀, 0, 0) := by simp
    _ = 1 := by simp [countingW, Real.exp_zero]

/-! ### Blank conservation

The augmented kernel preserves the invariant b + s_vb = b₀ + s_xy,
equivalently s_xy ≤ s_vb + b₀ ≤ s_vb + n.

This is because:
- VB: b decreases by 1, s_vb increases by 1 (net change: 0)
- XY: b increases by 1, s_xy increases by 1 (net change: 0)
- Other: no change
- Absorbed: no change

The invariant holds on the support of the kernel (infeasible interactions
have probability 0 in the PMF). -/

/-- **Blank conservation**: s_xy ≤ s_vb + n almost surely under the
    absorbed augmented kernel starting from (c₀, 0, 0).

    Proof: the invariant v(c) - s_vb + s_xy = v(c₀) is preserved at
    each augmented step (for all feasible interactions). Since v ≤ n,
    s_xy = s_vb + v - v₀ ≤ s_vb + n. -/
theorem blank_conservation (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    ∀ᵐ a ∂((absorbedAugKernel hn ^ t) (c₀, 0, 0)),
    a.2.2 ≤ a.2.1 + n := by
  -- Prove stronger equality invariant: s_xy + b₀ = s_vb + b (a.s.)
  suffices heq : ∀ᵐ a ∂((absorbedAugKernel hn ^ t) (c₀, 0, 0)),
      a.2.2 + c₀.b_count = a.2.1 + a.1.b_count by
    filter_upwards [heq] with a ha
    have := b_count_le a.1
    omega
  -- Helper: one step of the kernel preserves the equality invariant.
  -- If a satisfies s_xy + b₀ = s_vb + b, then K(a)-a.e. a' also satisfies it.
  have step_pres : ∀ (c : Config n) (svb sxy : ℕ),
      sxy + c₀.b_count = svb + c.b_count →
      (absorbedAugKernel hn (c, svb, sxy))
        {a' : AugConfig n | ¬(a'.2.2 + c₀.b_count = a'.2.1 + a'.1.b_count)} = 0 := by
    intro c svb sxy heq_a
    have hbad_meas : MeasurableSet
        ({a' : AugConfig n | ¬(a'.2.2 + c₀.b_count = a'.2.1 + a'.1.b_count)}) :=
      instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _
    unfold absorbedAugKernel
    rw [Kernel.piecewise_apply]
    by_cases hact : (c, svb, sxy) ∈ augActiveCentral
    · -- Active case: show sum over interaction types is 0
      rw [if_pos hact]
      change (augStepDist (c, svb, sxy) hn).toMeasure
        {a' | ¬(a'.2.2 + c₀.b_count = a'.2.1 + a'.1.b_count)} = 0
      rw [← lintegral_indicator_one hbad_meas,
          lintegral_augStepDist (c, svb, sxy) hn]
      apply Finset.sum_eq_zero
      intro ⟨i, r⟩ _
      -- For each (i, r): either augStep preserves invariant or PMF = 0
      suffices (augStep c svb sxy i r).2.2 + c₀.b_count =
                 (augStep c svb sxy i r).2.1 + (augStep c svb sxy i r).1.b_count ∨
               c.interactionPMF hn (i, r) = 0 by
        rcases this with h | h
        · simp only [Set.indicator_apply, Set.mem_setOf_eq, h, not_true_eq_false,
            ite_false, zero_mul]
        · rw [h, mul_zero]
      rcases i with _ | _ | _ <;> rcases r with _ | _ | _
      -- (x,x): no change
      · left; rw [augStep_xx]; exact heq_a
      -- (x,b): VB — split on feasibility
      · by_cases hf : c.x_count ≥ 1 ∧ c.b_count ≥ 1
        · left; rw [augStep_xb]
          show sxy + c₀.b_count = (svb + 1) + (c.stepOrSelf x b).b_count
          have hb' : (c.stepOrSelf x b).b_count = c.b_count - 1 := by
            have hstep : c.step x b = some ⟨c.x_count + 1, c.b_count - 1, c.y_count,
                by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos hf
            simp [stepOrSelf, hstep]
          rw [hb']; omega
        · right
          show c.interactionProb hn x b = 0
          unfold interactionProb interactionCount
          simp only [show (State.x : State) ≠ State.b from by decide, ite_false, countOf]
          have : c.x_count * c.b_count = 0 := by
            rw [Nat.mul_eq_zero]
            by_contra hall; push_neg at hall; exact hf ⟨by omega, by omega⟩
          simp [this]
      -- (x,y): XY — split on feasibility
      · by_cases hf : c.x_count ≥ 1 ∧ c.y_count ≥ 1
        · left; rw [augStep_xy]
          show (sxy + 1) + c₀.b_count = svb + (c.stepOrSelf x y).b_count
          have hb' : (c.stepOrSelf x y).b_count = c.b_count + 1 := by
            have hstep : c.step x y = some ⟨c.x_count, c.b_count + 1, c.y_count - 1,
                by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos hf
            simp [stepOrSelf, hstep]
          rw [hb']; omega
        · right
          show c.interactionProb hn x y = 0
          unfold interactionProb interactionCount
          simp only [show (State.x : State) ≠ State.y from by decide, ite_false, countOf]
          have : c.x_count * c.y_count = 0 := by
            rw [Nat.mul_eq_zero]
            by_contra hall; push_neg at hall; exact hf ⟨by omega, by omega⟩
          simp [this]
      -- (b,x): no change
      · left; rw [augStep_bx]; exact heq_a
      -- (b,b): no change
      · left; rw [augStep_bb]; exact heq_a
      -- (b,y): no change
      · left; rw [augStep_by'']; exact heq_a
      -- (y,x): XY — split on feasibility
      · by_cases hf : c.y_count ≥ 1 ∧ c.x_count ≥ 1
        · left; rw [augStep_yx]
          show (sxy + 1) + c₀.b_count = svb + (c.stepOrSelf y x).b_count
          have hb' : (c.stepOrSelf y x).b_count = c.b_count + 1 := by
            have hstep : c.step y x = some ⟨c.x_count - 1, c.b_count + 1, c.y_count,
                by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos hf
            simp [stepOrSelf, hstep]
          rw [hb']; omega
        · right
          show c.interactionProb hn y x = 0
          unfold interactionProb interactionCount
          simp only [show (State.y : State) ≠ State.x from by decide, ite_false, countOf]
          have : c.y_count * c.x_count = 0 := by
            rw [Nat.mul_eq_zero]
            by_contra hall; push_neg at hall; exact hf ⟨by omega, by omega⟩
          simp [this]
      -- (y,b): VB — split on feasibility
      · by_cases hf : c.y_count ≥ 1 ∧ c.b_count ≥ 1
        · left; rw [augStep_yb]
          show sxy + c₀.b_count = (svb + 1) + (c.stepOrSelf y b).b_count
          have hb' : (c.stepOrSelf y b).b_count = c.b_count - 1 := by
            have hstep : c.step y b = some ⟨c.x_count, c.b_count - 1, c.y_count + 1,
                by have := c.sum_eq; omega⟩ := by unfold step; exact dif_pos hf
            simp [stepOrSelf, hstep]
          rw [hb']; omega
        · right
          show c.interactionProb hn y b = 0
          unfold interactionProb interactionCount
          simp only [show (State.y : State) ≠ State.b from by decide, ite_false, countOf]
          have : c.y_count * c.b_count = 0 := by
            rw [Nat.mul_eq_zero]
            by_contra hall; push_neg at hall; exact hf ⟨by omega, by omega⟩
          simp [this]
      -- (y,y): no change
      · left; rw [augStep_yy]; exact heq_a
    · -- Absorbed case: K(a) = dirac(a), and a is in the good set
      rw [if_neg hact, Kernel.id_apply, Measure.dirac_apply' _ hbad_meas]
      simp only [Set.indicator_apply, Set.mem_setOf_eq, heq_a, not_true_eq_false, ite_false]
  -- Main induction on t
  induction t with
  | zero =>
    simp only [pow_zero]
    change ∀ᵐ a ∂(Kernel.id (c₀, 0, 0)), _
    rw [Kernel.id_apply, MeasureTheory.ae_dirac_iff
      (instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _)]
    -- Goal: 0 + c₀.b_count = 0 + c₀.b_count
  | succ t ih =>
    rw [MeasureTheory.ae_iff]
    have hbad_meas : MeasurableSet
        {a : AugConfig n | ¬(a.2.2 + c₀.b_count = a.2.1 + a.1.b_count)} :=
      instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _
    rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hbad_meas,
        MeasureTheory.lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad_meas)]
    filter_upwards [ih] with ⟨c, svb, sxy⟩ hb
    exact step_pres c svb sxy hb

/-! ### Indicator-weighted counting supermartingale (active contraction)

The counting supermartingale `W = exp((-130·svb - 258·sxy)/n)` has a
STRONGER contraction on active states: `E[W'] ≤ exp(-1/n)·W`.

This follows from `counting_supermartingale_per_step`, which shows:
  (T-bv-xy2)·exp(1/n) + bv·exp(-129/n) + xy2·exp(-257/n) ≤ T

Factoring out exp(1/n):
  exp(1/n) · E[exp((-130·Δsvb - 258·Δsxy)/n)] ≤ 1
  ⟹  E[exp((-130·Δsvb - 258·Δsxy)/n)] ≤ exp(-1/n)
  ⟹  E[W(augStep)] ≤ exp(-1/n) · W(a)

Define `countingWActive a = if a ∈ augActiveCentral then countingW a else 0`.
This has per-step contraction `exp(-1/n)` under the absorbed augmented kernel:
- Active a: E[Ψ'] ≤ E[W'] ≤ exp(-1/n)·W = exp(-1/n)·Ψ  (dropping indicator)
- Absorbed a: Ψ = 0, E[Ψ'] = 0 ≤ exp(-1/n)·0 = 0 -/

/-- Indicator-weighted counting function: W on active states, 0 elsewhere. -/
noncomputable def countingWActive (a : AugConfig n) : ℝ≥0∞ :=
  if a ∈ augActiveCentral then countingW a else 0

private theorem countingWActive_measurable :
    Measurable (countingWActive : AugConfig n → ℝ≥0∞) :=
  fun _ _ => instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _

set_option maxHeartbeats 1600000 in
/-- **Active contraction**: E[W(augStep)] ≤ exp(-1/n)·W for active central configs.
    Converts `counting_supermartingale_per_step` (ℝ algebraic bound)
    to an ENNReal lintegral bound over the augmented step distribution. -/
theorem countingW_active_contraction (hn : n ≥ 2) (c : Config n)
    (hc : c.inCentral) (hv : 0 < c.v) (svb sxy : ℕ) :
    ∫⁻ a', countingW a' ∂(augStepDist (c, svb, sxy) hn).toMeasure ≤
    ENNReal.ofReal (Real.exp (-(1 : ℝ) / (n : ℝ))) * countingW (c, svb, sxy) := by
  -- Work with a := (c, svb, sxy) to manage projections
  have h_a : augStepDist (c, svb, sxy) hn = augStepDist (c, svb, sxy) hn := rfl
  rw [lintegral_augStepDist _ hn, show (c, svb, sxy).1 = c from rfl,
      show (c, svb, sxy).2.1 = svb from rfl, show (c, svb, sxy).2.2 = sxy from rfl]
  -- Step 1: Finiteness
  have hW_ne : ∀ a' : AugConfig n, countingW a' ≠ ⊤ := fun _ =>
    ENNReal.ofReal_ne_top
  have hP_ne : ∀ q, (c.interactionPMF hn q) ≠ ⊤ := fun q => (PMF.apply_lt_top _ _).ne
  have hterm_ne : ∀ q ∈ (Finset.univ : Finset (State × State)),
      countingW (augStep c svb sxy q.1 q.2) * (c.interactionPMF hn q) ≠ ⊤ :=
    fun q _ => ENNReal.mul_ne_top (hW_ne _) (hP_ne q)
  have hsum_ne := ENNReal.sum_ne_top.mpr hterm_ne
  have hRHS_ne : ENNReal.ofReal (Real.exp (-(1:ℝ) / ↑n)) *
      countingW (c, svb, sxy) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- Step 2: Convert to ℝ
  rw [← ENNReal.toReal_le_toReal hsum_ne hRHS_ne]
  rw [ENNReal.toReal_sum hterm_ne]
  simp_rw [ENNReal.toReal_mul]
  simp only [countingW, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
  simp_rw [interactionPMF_toReal c hn]
  -- Step 3: Expand to 9 terms
  rw [show (Finset.univ : Finset (State × State)) = Finset.univ ×ˢ Finset.univ
      from Finset.univ_product_univ.symm, Finset.sum_product]
  simp only [sum_state_expand]
  simp only [augStep_xx c svb sxy, augStep_xb c svb sxy, augStep_xy c svb sxy,
    augStep_bx c svb sxy, augStep_bb c svb sxy, augStep_by'' c svb sxy,
    augStep_yx c svb sxy, augStep_yb c svb sxy, augStep_yy c svb sxy]
  -- Prod projections already reduced by augStep lemmas
  -- Step 5: Apply counting_supermartingale_per_step after algebra
  have hW_pos : (0 : ℝ) < Real.exp ((-130 * ↑svb - 258 * ↑sxy) / ↑n) := Real.exp_pos _
  have hT_pos : (0 : ℝ) < (totalPairs n : ℝ) := by exact_mod_cast totalPairs_pos hn
  have h_csps := counting_supermartingale_per_step c hn hc hv
  -- Step 6: Factor VB/XY exponents using exp_add
  have hvb : Real.exp ((-130 * ↑(svb + 1) - 258 * ↑sxy) / ↑n) =
      Real.exp ((-130 * ↑svb - 258 * ↑sxy) / ↑n) * Real.exp (-130 / ↑n) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  have hxy_eq : Real.exp ((-130 * ↑svb - 258 * ↑(sxy + 1)) / ↑n) =
      Real.exp ((-130 * ↑svb - 258 * ↑sxy) / ↑n) * Real.exp (-258 / ↑n) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [hvb, hxy_eq]
  -- Step 7: Unfold interactionCount to explicit products
  simp only [interactionCount, countOf,
    show ¬(State.x = State.b) from by decide, show ¬(State.x = State.y) from by decide,
    show ¬(State.b = State.x) from by decide, show ¬(State.b = State.y) from by decide,
    show ¬(State.y = State.x) from by decide, show ¬(State.y = State.b) from by decide,
    ite_true, ite_false]
  -- Step 8: Clear totalPairs denominator with field_simp
  have hT_ne : (↑(totalPairs n) : ℝ) ≠ 0 := by exact_mod_cast (totalPairs_pos hn).ne'
  field_simp [hT_ne]
  -- Normalize -(k/n) → -k/n so set commands match the goal
  simp only [← neg_div]
  -- Step 9: Name exp constants
  set e130 := Real.exp (-130 / (↑n : ℝ))
  set e258 := Real.exp (-258 / (↑n : ℝ))
  set e1 := Real.exp (-1 / (↑n : ℝ))
  have he1_pos : (0 : ℝ) < e1 := Real.exp_pos _
  -- Step 10: Multiply h_csps by e1 to get the contraction bound
  -- exp(1/n)*e1 = 1, exp(-129/n)*e1 = e130, exp(-257/n)*e1 = e258
  have h_exp1_e1 : Real.exp (1 / (↑n : ℝ)) * e1 = 1 := by
    simp only [e1, ← Real.exp_add]; convert Real.exp_zero using 1; ring
  have h_129_e1 : Real.exp (-129 / (↑n : ℝ)) * e1 = e130 := by
    simp only [e130, e1, ← Real.exp_add]; congr 1; ring
  have h_257_e1 : Real.exp (-257 / (↑n : ℝ)) * e1 = e258 := by
    simp only [e258, e1, ← Real.exp_add]; congr 1; ring
  have h_bound : (↑(totalPairs n - c.b_count * c.v - 2 * c.x_count * c.y_count : ℕ) : ℝ) +
      ↑(c.b_count * c.v : ℕ) * e130 + ↑(2 * c.x_count * c.y_count : ℕ) * e258 ≤
      ↑(totalPairs n) * e1 := by
    have step1 := mul_le_mul_of_nonneg_right h_csps he1_pos.le
    have step2 : (↑(totalPairs n - c.b_count * c.v - 2 * c.x_count * c.y_count : ℕ) : ℝ) +
        ↑(c.b_count * c.v : ℕ) * e130 + ↑(2 * c.x_count * c.y_count : ℕ) * e258 =
        (↑(totalPairs n - c.b_count * c.v - 2 * c.x_count * c.y_count : ℕ) *
           Real.exp (1 / ↑n) +
         ↑(c.b_count * c.v : ℕ) * Real.exp (-129 / ↑n) +
         ↑(2 * c.x_count * c.y_count : ℕ) * Real.exp (-257 / ↑n)) * e1 := by
      simp only [add_mul, mul_assoc, h_exp1_e1, h_129_e1, h_257_e1, mul_one]
    linarith
  -- Step 11: Counting identities (ℕ)
  have hVB_eq : c.x_count * c.b_count + c.y_count * c.b_count = c.b_count * c.v := by
    unfold Config.v; ring
  have hXY_eq : c.x_count * c.y_count + c.y_count * c.x_count = 2 * c.x_count * c.y_count := by
    ring
  have hsum_eq : c.x_count * (c.x_count - 1) + c.x_count * c.b_count +
      c.x_count * c.y_count + c.b_count * c.x_count + c.b_count * (c.b_count - 1) +
      c.b_count * c.y_count + c.y_count * c.x_count + c.y_count * c.b_count +
      c.y_count * (c.y_count - 1) = totalPairs n := by
    unfold totalPairs
    have hs := c.sum_eq
    -- a*(a-1)+a = a*a in ℕ (nonlinear, omega can't handle, use cases)
    have hdiag : ∀ a : ℕ, a * (a - 1) + a = a * a := by
      intro a; cases a with | zero => simp | succ k => simp [Nat.succ_sub_one]; ring
    have hx := hdiag c.x_count
    have hb := hdiag c.b_count
    have hy := hdiag c.y_count
    have hnn := hdiag n
    -- (x+b+y)² = x²+...+y², via congr + ring (can't rw n directly: dependent types)
    have hn_sq : n * n = (c.x_count + c.b_count + c.y_count) *
        (c.x_count + c.b_count + c.y_count) := by congr 1 <;> exact hs.symm
    have h_sq : c.x_count * c.x_count + c.x_count * c.b_count + c.x_count * c.y_count +
        c.b_count * c.x_count + c.b_count * c.b_count + c.b_count * c.y_count +
        c.y_count * c.x_count + c.y_count * c.b_count + c.y_count * c.y_count = n * n := by
      rw [hn_sq]; ring
    -- omega: linear in opaque products, derives LHS + n = n*n = n*(n-1) + n
    omega
  -- "Other" interaction count = T - bv - 2xy
  have hOther : c.x_count * (c.x_count - 1) + c.b_count * c.x_count +
      c.b_count * (c.b_count - 1) + c.b_count * c.y_count +
      c.y_count * (c.y_count - 1) =
      totalPairs n - c.b_count * c.v - 2 * c.x_count * c.y_count := by
    have := bv_xy2_le_totalPairs c; omega
  -- Step 12: Cast counting identities to ℝ and close with linarith
  have h_other_r : (↑(c.x_count * (c.x_count - 1) + c.b_count * c.x_count +
      c.b_count * (c.b_count - 1) + c.b_count * c.y_count +
      c.y_count * (c.y_count - 1)) : ℝ) =
      ↑(totalPairs n - c.b_count * c.v - 2 * c.x_count * c.y_count : ℕ) := by
    exact_mod_cast hOther
  simp only [Nat.cast_add] at h_other_r
  have h_vb_r : e130 * (↑(c.x_count * c.b_count) : ℝ) + e130 * ↑(c.y_count * c.b_count) =
      ↑(c.b_count * c.v : ℕ) * e130 := by
    rw [← mul_add, mul_comm e130]; congr 1; exact_mod_cast hVB_eq
  have h_xy_r : e258 * (↑(c.x_count * c.y_count) : ℝ) + e258 * ↑(c.y_count * c.x_count) =
      ↑(2 * c.x_count * c.y_count : ℕ) * e258 := by
    rw [← mul_add, mul_comm e258]; congr 1; exact_mod_cast hXY_eq
  linarith [h_bound, h_other_r, h_vb_r, h_xy_r]

/-- **Per-step contraction for countingWActive**: the indicator-weighted
    counting function contracts by exp(-1/n) under the absorbed augmented kernel. -/
theorem countingWActive_per_step (hn : n ≥ 2) (a : AugConfig n) :
    ∫⁻ a', countingWActive a' ∂(absorbedAugKernel hn a) ≤
    ENNReal.ofReal (Real.exp (-(1 : ℝ) / (n : ℝ))) * countingWActive a := by
  unfold absorbedAugKernel
  rw [Kernel.lintegral_piecewise]
  by_cases ha : a ∈ augActiveCentral
  · rw [if_pos ha]
    obtain ⟨c, svb, sxy⟩ := a
    -- ha : (c, svb, sxy) ∈ augActiveCentral, i.e., c ∈ activeCentral
    have hmem : c ∈ activeCentral := ha
    have hc : c.inCentral := hmem.1
    have hv : 0 < c.v := by have := hmem.2; omega
    -- E[Ψ'] ≤ E[W'] ≤ exp(-1/n)·W = exp(-1/n)·Ψ
    calc ∫⁻ a', countingWActive a' ∂(augStepDist (c, svb, sxy) hn).toMeasure
        ≤ ∫⁻ a', countingW a' ∂(augStepDist (c, svb, sxy) hn).toMeasure := by
          apply lintegral_mono; intro a'
          simp only [countingWActive]; split_ifs with h
          · exact le_refl _
          · exact zero_le'
      _ ≤ ENNReal.ofReal (Real.exp (-(1 : ℝ) / ↑n)) *
          countingW (c, svb, sxy) :=
          countingW_active_contraction hn c hc hv svb sxy
      _ = ENNReal.ofReal (Real.exp (-(1 : ℝ) / ↑n)) *
          countingWActive (c, svb, sxy) := by
          congr 1; show countingW _ = countingWActive _
          simp only [countingWActive, augActiveCentral, Set.mem_setOf_eq,
            show (c, (svb, sxy)).1 ∈ activeCentral from hmem, ite_true]
  · rw [if_neg ha, Kernel.id_apply, lintegral_dirac' a countingWActive_measurable]
    simp only [countingWActive, if_neg ha, mul_zero, le_refl]

/-- **Active counting iteration**: E[Ψ_t] ≤ exp(-t/n) for Ψ = 1_{active}·W.
    Starting from (c₀, 0, 0) with c₀ ∈ activeCentral: Ψ₀ = W₀ = 1. -/
theorem countingWActive_iteration (hn : n ≥ 2) (c₀ : Config n)
    (hc₀ : c₀ ∈ activeCentral) (t : ℕ) :
    ∫⁻ a, countingWActive a ∂((absorbedAugKernel hn ^ t) (c₀, 0, 0)) ≤
    ENNReal.ofReal (Real.exp (-(t : ℝ) / (n : ℝ))) := by
  have h := lintegral_geometric_decay
    (absorbedAugKernel hn) countingWActive countingWActive_measurable
    (ENNReal.ofReal (Real.exp (-(1 : ℝ) / (n : ℝ))))
    (fun a => countingWActive_per_step hn a) t (c₀, 0, 0)
  calc ∫⁻ a, countingWActive a ∂((absorbedAugKernel hn ^ t) (c₀, 0, 0))
      ≤ ENNReal.ofReal (Real.exp (-(1 : ℝ) / ↑n)) ^ t *
        countingWActive (c₀, 0, 0) := h
    _ = ENNReal.ofReal (Real.exp (-(1 : ℝ) / ↑n)) ^ t := by
        have hmem : (c₀, (0 : ℕ), (0 : ℕ)).1 ∈ activeCentral := hc₀
        simp only [countingWActive, augActiveCentral, Set.mem_setOf_eq, if_pos hmem,
          countingW]
        simp [Real.exp_zero]
    _ = ENNReal.ofReal (Real.exp (-(1 : ℝ) / ↑n) ^ t) := by
        rw [ENNReal.ofReal_pow (le_of_lt (Real.exp_pos _))]
    _ = ENNReal.ofReal (Real.exp (-(↑t : ℝ) / ↑n)) := by
        congr 1; rw [← Real.exp_nat_mul]; ring_nf

/-! ### Arithmetic helpers for the pointwise bound in Term 2

The pointwise bound requires showing that for states satisfying
blank conservation (sxy ≤ svb + n) and the counting SM constraint
(260·svb + 516·sxy > t), the product of the decay rate and the
augmented product function is ≥ 1/2.

Key decomposition:
  2·R^t · α_vb^svb · α_xy^sxy ≥ 2·(R^776·ρ)^svb · (R^516·α_xy)^n ≥ 1

where R = 1-1/(15000n), ρ = (16n+7)(16n-5)/(16n)², α_xy = (16n-5)/(16n). -/

/-- First-order Bernoulli inequality: (1-x)^k ≥ 1-kx for 0 ≤ x ≤ 1. -/
private lemma bernoulli_sub (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    1 - ↑k * x ≤ (1 - x) ^ k := by
  -- Mathlib's Bernoulli gives 1 + k*(-x) ≤ (1+(-x))^k; (1+(-x)) = (1-x) defeq
  have h : 1 + ↑k * (-x) ≤ (1 - x) ^ k := one_add_mul_le_pow_of_sq_nonneg (a := -x)
    (sq_nonneg _) (sq_nonneg _) (by linarith : (0:ℝ) ≤ 2 + (-x)) k
  linarith [show ↑k * (-x) = -(↑k * x) from mul_neg _ _]

/-- Algebraic core of rate_comparison_776. Opaque R avoids whnf expansion of R^776. -/
private lemma rate_comparison_alg (R : ℝ) (m : ℕ)
    (hm : (2 : ℝ) ≤ ↑m)
    (hR_lower : (15000 * (↑m : ℝ) - 776) / (15000 * ↑m) ≤ R)
    (halg : (16 * (↑m : ℝ)) ^ 2 * (15000 * ↑m) ≤
      (15000 * ↑m - 776) * ((16 * ↑m + 7) * (16 * ↑m - 5))) :
    1 ≤ R * ((16 * ↑m + 7) * (16 * ↑m - 5) / (16 * ↑m) ^ 2) := by
  have h16m : (0 : ℝ) < 16 * ↑m := by nlinarith
  have h15km : (0 : ℝ) < 15000 * ↑m := by positivity
  have hprod_nn : (0 : ℝ) ≤ (16 * ↑m + 7) * (16 * ↑m - 5) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  -- 1 ≤ R * A/B ← B ≤ R*A ← B ≤ (lower)*A
  calc (1 : ℝ) = (16 * ↑m) ^ 2 * (15000 * ↑m) / ((16 * ↑m) ^ 2 * (15000 * ↑m)) := by
        rw [div_self (ne_of_gt (mul_pos (pow_pos h16m 2) h15km))]
    _ ≤ (15000 * ↑m - 776) * ((16 * ↑m + 7) * (16 * ↑m - 5)) /
        ((16 * ↑m) ^ 2 * (15000 * ↑m)) := by gcongr
    _ = (15000 * ↑m - 776) / (15000 * ↑m) *
        ((16 * ↑m + 7) * (16 * ↑m - 5) / (16 * ↑m) ^ 2) := by ring
    _ ≤ R * ((16 * ↑m + 7) * (16 * ↑m - 5) / (16 * ↑m) ^ 2) := by
        gcongr

/-- Rate comparison: R^776 · ρ ≥ 1 for n ≥ 2. -/
private theorem rate_comparison_776 (hn : n ≥ 2) :
    (1 : ℝ) ≤ (1 - 1 / (15000 * (↑n : ℝ))) ^ 776 *
    ((16 * ↑n + 7) * (16 * ↑n - 5) / (16 * ↑n) ^ 2) := by
  have hn_real : (2 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn
  have h15kn : (0 : ℝ) < 15000 * ↑n := by positivity
  have hx_le : 1 / (15000 * (↑n : ℝ)) ≤ 1 := by
    rw [div_le_one h15kn]; nlinarith
  apply rate_comparison_alg _ n hn_real
  · -- R ≥ (15000n-776)/(15000n)
    have hbern := bernoulli_sub (1 / (15000 * ↑n)) (by positivity) hx_le 776
    -- hbern : 1 - ↑776 * (1/(15000n)) ≤ (1-1/(15000n))^776
    calc (15000 * (↑n : ℝ) - 776) / (15000 * ↑n)
        = 1 - 776 * (1 / (15000 * ↑n)) := by field_simp
      _ = 1 - ↑776 * (1 / (15000 * ↑n)) := by push_cast; ring
      _ ≤ _ := hbern
  · -- polynomial bound
    nlinarith [show (0 : ℝ) ≤ ↑n * (↑n - 2) from by nlinarith]

/-- Core of correction bound with opaque B to avoid whnf on R^516. -/
private lemma correction_alg (B : ℝ) (m : ℕ)
    (hm : (2 : ℝ) ≤ ↑m)
    (hB_lower : 1 - (↑516 * (1 / (15000 * (↑m : ℝ))) + 5 / (16 * ↑m)) ≤ B)
    (hB_le : B ≤ 1) :
    1 ≤ 2 * B ^ m := by
  -- c = 516/(15000n) + 5/(16n); nc = 516/15000 + 5/16 = 3469/10000
  have hm_pos : (0 : ℝ) < ↑m := by linarith
  have hc : ↑516 * (1 / (15000 * (↑m : ℝ))) + 5 / (16 * ↑m) ≤ 1 := by
    have h1 : ↑516 * (1 / (15000 * (↑m : ℝ))) ≤ 1 / 4 := by
      have : ↑516 * (1 / (15000 * (↑m : ℝ))) = 516 / (15000 * ↑m) := by push_cast; ring
      rw [this]
      calc (516 : ℝ) / (15000 * ↑m) ≤ 516 / (15000 * 2) := by gcongr
        _ ≤ 1 / 4 := by norm_num
    have h2 : 5 / (16 * (↑m : ℝ)) ≤ 5 / 32 := by gcongr; nlinarith
    linarith [show (5 : ℝ) / 32 ≤ 1 / 4 from by norm_num]
  have hB_nonneg : 0 ≤ B := by linarith
  -- Outer Bernoulli: B^n ≥ 1 - n*(1-B)
  have hBsub := bernoulli_sub (1 - B) (by linarith) (by linarith) m
  -- hBsub : 1 - ↑m * (1-B) ≤ (1-(1-B))^m = B^m
  have hBB : (1 - (1 - B)) = B := by ring
  rw [hBB] at hBsub
  -- B ≥ 1-c, so 1-B ≤ c, so m*(1-B) ≤ m*c
  have hnc : (↑m : ℝ) * (1 - B) ≤
      ↑m * (↑516 * (1 / (15000 * ↑m)) + 5 / (16 * ↑m)) := by
    gcongr; linarith
  -- m*c = 516/15000 + 5/16 ≤ 1/2
  have hnc_val : (↑m : ℝ) * (↑516 * (1 / (15000 * ↑m)) + 5 / (16 * ↑m)) ≤ 1 / 2 := by
    have : (↑m : ℝ) * (↑516 * (1 / (15000 * ↑m)) + 5 / (16 * ↑m)) =
        ↑516 / 15000 + 5 / 16 := by
      field_simp
    rw [this]; push_cast; norm_num
  linarith

set_option maxHeartbeats 400000 in
/-- Correction bound: 2 · (R^516 · α_xy)^n ≥ 1 for n ≥ 2.
    Double Bernoulli: inner R^516 ≥ 1-516/(15000n), outer B^n ≥ 1-n(1-B). -/
private theorem correction_bound_516 (hn : n ≥ 2) :
    (1 : ℝ) ≤ 2 * ((1 - 1 / (15000 * (↑n : ℝ))) ^ 516 *
    ((16 * ↑n - 5) / (16 * ↑n))) ^ (n : ℕ) := by
  have hn_real : (2 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn
  have h15kn : (0 : ℝ) < 15000 * ↑n := by positivity
  have h16n : (0 : ℝ) < 16 * ↑n := by positivity
  have hx_le : 1 / (15000 * (↑n : ℝ)) ≤ 1 := by
    rw [div_le_one h15kn]; nlinarith
  apply correction_alg _ n hn_real
  · -- B ≥ 1 - c
    have hinner := bernoulli_sub (1 / (15000 * ↑n)) (by positivity) hx_le 516
    have hαxy : (16 * (↑n : ℝ) - 5) / (16 * ↑n) = 1 - 5 / (16 * ↑n) := by
      field_simp
    rw [hαxy]
    calc (1 : ℝ) - (516 * (1 / (15000 * ↑n)) + 5 / (16 * ↑n))
        ≤ (1 - 516 * (1 / (15000 * ↑n))) * (1 - 5 / (16 * ↑n)) := by
          nlinarith [show (0 : ℝ) ≤ 516 * (1 / (15000 * ↑n)) * (5 / (16 * ↑n))
            from by positivity]
      _ ≤ (1 - 1 / (15000 * ↑n)) ^ 516 * (1 - 5 / (16 * ↑n)) := by
          apply mul_le_mul_of_nonneg_right hinner
          have : 5 / (16 * (↑n : ℝ)) ≤ 5 / 32 := by gcongr; linarith
          linarith [show (5 : ℝ) / 32 < 1 from by norm_num]
  · -- B ≤ 1
    have hRnn : 0 ≤ 1 - 1 / (15000 * (↑n : ℝ)) := sub_nonneg.mpr hx_le
    have hRle : 1 - 1 / (15000 * (↑n : ℝ)) ≤ 1 := sub_le_self _ (by positivity)
    have hpow : (1 - 1 / (15000 * (↑n : ℝ))) ^ 516 ≤ 1 := pow_le_one₀ hRnn hRle
    have hdiv_nn : (0 : ℝ) ≤ (16 * ↑n - 5) / (16 * ↑n) :=
      div_nonneg (by linarith) (le_of_lt h16n)
    have hdiv_le : (16 * (↑n : ℝ) - 5) / (16 * ↑n) ≤ 1 := by
      rw [div_le_one h16n]; linarith
    calc (1 - 1 / (15000 * (↑n : ℝ))) ^ 516 * ((16 * ↑n - 5) / (16 * ↑n))
        ≤ 1 * ((16 * ↑n - 5) / (16 * ↑n)) := mul_le_mul_of_nonneg_right hpow hdiv_nn
      _ = (16 * ↑n - 5) / (16 * ↑n) := one_mul _
      _ ≤ 1 := hdiv_le

/-- Algebraic rearrangement of the product bound. Extracted as a standalone
    lemma so `ring` sees opaque variables, avoiding timeout on `set` definitions. -/
private lemma product_rearrange (R αvb αxy : ℝ) (s m : ℕ) :
    (R ^ 776 * αvb * αxy) ^ s * (2 * (R ^ 516 * αxy) ^ m) =
    2 * R ^ (776 * s + 516 * m) * αvb ^ s * αxy ^ (s + m) := by
  ring

/-- Core bound chain with opaque parameters, avoiding `set`-induced timeouts.
    All variables are free, so `ring`/`nlinarith`/`positivity` never expand
    concrete definitions like `R = 1-1/(15000n)`. -/
private theorem pointwise_bound_core
    (R αvb αxy : ℝ) (svb sxy t m : ℕ)
    (hR_pos : 0 < R) (hR_le : R ≤ 1)
    (hαvb_pos : 0 < αvb)
    (hαxy_pos : 0 < αxy) (hαxy_le : αxy ≤ 1)
    (hbc : sxy ≤ svb + m)
    (ht_lt : t < 776 * svb + 516 * m)
    (hρ : 1 ≤ R ^ 776 * (αvb * αxy))
    (hcorr : 1 ≤ 2 * (R ^ 516 * αxy) ^ m) :
    (1 : ℝ) ≤ 2 * R ^ t * αvb ^ svb * αxy ^ sxy := by
  have hRt : R ^ (776 * svb + 516 * m) ≤ R ^ t :=
    pow_le_pow_of_le_one (le_of_lt hR_pos) hR_le (by omega)
  have hαxy_pow : αxy ^ (svb + m) ≤ αxy ^ sxy :=
    pow_le_pow_of_le_one (le_of_lt hαxy_pos) hαxy_le hbc
  have hρ_pow : 1 ≤ (R ^ 776 * αvb * αxy) ^ svb := by
    apply one_le_pow₀
    linarith [mul_assoc (R ^ 776) αvb αxy]
  have hstep1 : (1 : ℝ) ≤ (R ^ 776 * αvb * αxy) ^ svb * (2 * (R ^ 516 * αxy) ^ m) :=
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ _ := mul_le_mul hρ_pow hcorr (by norm_num) (by positivity)
  have hstep2 := product_rearrange R αvb αxy svb m
  calc (1 : ℝ) ≤ _ := hstep1
    _ = 2 * R ^ (776 * svb + 516 * m) * αvb ^ svb * αxy ^ (svb + m) := hstep2
    _ ≤ 2 * R ^ t * αvb ^ svb * αxy ^ (svb + m) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hRt (by norm_num : (0:ℝ) ≤ 2))
            (by positivity : (0:ℝ) ≤ αvb ^ svb))
          (by positivity : (0:ℝ) ≤ αxy ^ (svb + m))
    _ ≤ 2 * R ^ t * αvb ^ svb * αxy ^ sxy :=
        mul_le_mul_of_nonneg_left hαxy_pow (by positivity)

/-- Pointwise product-rate bound in ℝ. Given blank conservation and the
    counting SM constraint, we have 1 ≤ 2·R^t·α_vb^svb·α_xy^sxy. -/
private theorem pointwise_bound_real (hn : n ≥ 2)
    (svb sxy t : ℕ) (hbc : sxy ≤ svb + n) (hcount : t < 260 * svb + 516 * sxy) :
    (1 : ℝ) ≤ 2 * (1 - 1 / (15000 * (↑n : ℝ))) ^ t *
    ((16 * (↑n : ℝ) + 7) / (16 * ↑n)) ^ svb *
    ((16 * (↑n : ℝ) - 5) / (16 * ↑n)) ^ sxy := by
  have hn_real : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn
  apply pointwise_bound_core _ _ _ _ _ _ n
  · -- hR_pos: 0 < 1 - 1/(15000n)
    rw [sub_pos, div_lt_one (by positivity : (0:ℝ) < 15000 * ↑n)]; nlinarith
  · -- hR_le: 1 - 1/(15000n) ≤ 1
    linarith [show (0:ℝ) < 1 / (15000 * ↑n) from by positivity]
  · -- hαvb_pos: 0 < (16n+7)/(16n)
    apply div_pos <;> nlinarith
  · -- hαxy_pos: 0 < (16n-5)/(16n)
    apply div_pos <;> nlinarith
  · -- hαxy_le: (16n-5)/(16n) ≤ 1
    rw [div_le_one (by positivity : (0:ℝ) < 16 * ↑n)]; linarith
  · -- hbc
    exact hbc
  · -- ht_lt: t < 776*svb + 516*n
    calc (t : ℕ) < 260 * svb + 516 * sxy := hcount
      _ ≤ 260 * svb + 516 * (svb + n) := by omega
      _ = 776 * svb + 516 * n := by ring
  · -- hρ: 1 ≤ R^776 * (αvb * αxy)
    rw [div_mul_div_comm, ← sq]
    exact rate_comparison_776 hn
  · -- hcorr: 1 ≤ 2*(R^516 * αxy)^n
    exact correction_bound_516 hn

/-! ### Final combination: geometric decay for central region

Combining the M supermartingale (Corollary 2) with the counting
supermartingale (Lemma 5) gives geometric decay for the probability
of remaining in the central region.

**Proof strategy** (union bound):

1. Move to augmented state via `augKernel_proj_eq_absorbedCentral`.

2. Define Ψ = 1_{active}·W. From `countingWActive_iteration`:
   E[Ψ_t] ≤ exp(-t/n).

3. Split: P[active at t] = P[A] + P[B], where
   - Event A: active ∧ W > exp(-t/(2n))  (≡ 130svb+258sxy < t/2)
   - Event B: active ∧ W ≤ exp(-t/(2n))  (≡ 130svb+258sxy ≥ t/2)

4. **Term 1** (event A): On A, Ψ > exp(-t/(2n)).
   By Markov on Ψ: P[A] ≤ E[Ψ_t]/exp(-t/(2n)) = exp(-t/(2n)).

5. **Term 2** (event B): 130svb+258sxy ≥ t/2 and sxy ≤ svb+n
   (blank conservation), so svb ≥ (t/2-258n)/388.
   On active states with svb ≥ k:
     M ≥ ρ^k · α_xy^n / (n²+2n)  where ρ = α_vb·α_xy > 1
   By Markov on M: P[B] ≤ (n²+2n)/(f₀·ρ^k·α_xy^n).

6. Both terms ≤ C·(1-1/(15000n))^t·(n²+2n)/f₀ for constant C ≤ 3/2.
   - exp(-t/(2n)) ≤ (1-1/(15000n))^t (since 1/(2n) > 1/(15000n))
   - ρ^{-k} with k ≈ t/776: ρ^{1/776} ≥ 1+1/(15000n) for n ≥ 2

7. Combine: P[active at t] ≤ 3·(1-1/(15000n))^t·(n²+2n)/f₀. -/

/-- **Main theorem**: geometric decay for the central region,
    proved by combining the augmented supermartingale with the
    counting supermartingale.

    This supplies the central-region probability bound used by
    ConvergenceTime.lean. -/
theorem central_geometric_decay (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    (absorbedKernelCentral hn ^ t) c₀ activeCentral ≤
    3 * ENNReal.ofReal ((1 - 1 / (15000 * (n : ℝ))) ^ t) *
    potentialCentralTrunc c₀ := by
  -- Case: c₀ ∉ activeCentral → both sides are 0
  by_cases hc₀ : c₀ ∈ activeCentral
  · -- Active case: union bound combining counting + M supermartingales.
    -- Step 1: Move to augmented state via projection lemma
    rw [← augKernel_proj_eq_absorbedCentral hn c₀ t]
    set μ := (absorbedAugKernel hn ^ t) (c₀, 0, 0) with hμ_def
    set r := ENNReal.ofReal ((1 - 1 / (15000 * (↑n : ℝ))) ^ t) with hr_def
    set P := potentialCentralTrunc c₀ with hP_def
    set Aset := {a : AugConfig n | a.1 ∈ activeCentral} with hAset_def
    set lam := ENNReal.ofReal (Real.exp (-(↑t : ℝ) / (2 * ↑n))) with hlam_def
    set Bset := {a : AugConfig n | lam ≤ countingWActive a} with hBset_def
    -- Measurability (discrete: all sets are measurable)
    have hBmeas : MeasurableSet Bset :=
      instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _
    -- lam properties
    have hlam_pos : (0 : ℝ) < Real.exp (-(↑t : ℝ) / (2 * ↑n)) := Real.exp_pos _
    have hlam_ne_zero : lam ≠ 0 := by
      simp only [lam, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hlam_pos
    have hlam_ne_top : lam ≠ ⊤ := ENNReal.ofReal_ne_top
    -- TERM 1: Markov bound on countingWActive
    -- μ({Ψ ≥ lam}) ≤ E[Ψ]/lam ≤ exp(-t/n)/exp(-t/(2n)) = exp(-t/(2n)) = lam
    have hterm1 : μ Bset ≤ lam := by
      have hmarkov := mul_meas_ge_le_lintegral₀
        (μ := μ) countingWActive_measurable.aemeasurable lam
      have hiter := countingWActive_iteration hn c₀ hc₀ t
      -- exp(-t/n) = exp(-t/(2n))² = lam²
      have hexp_sq : ENNReal.ofReal (Real.exp (-(↑t : ℝ) / ↑n)) = lam ^ 2 := by
        have hreal : Real.exp (-(↑t : ℝ) / ↑n) =
            (Real.exp (-(↑t : ℝ) / (2 * ↑n))) ^ 2 := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        rw [hreal, ENNReal.ofReal_pow (le_of_lt hlam_pos)]
      have hle_sq : lam * μ Bset ≤ lam ^ 2 :=
        calc lam * μ Bset ≤ ∫⁻ a, countingWActive a ∂μ := hmarkov
          _ ≤ ENNReal.ofReal (Real.exp (-(↑t : ℝ) / ↑n)) := hiter
          _ = lam ^ 2 := hexp_sq
      calc μ Bset
          = lam⁻¹ * (lam * μ Bset) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hlam_ne_zero hlam_ne_top, one_mul]
        _ ≤ lam⁻¹ * lam ^ 2 := by gcongr
        _ = lam := by
            rw [sq, ← mul_assoc, ENNReal.inv_mul_cancel hlam_ne_zero hlam_ne_top, one_mul]
    -- TERM 2: blank conservation + Markov on M
    -- On {active ∧ Ψ < lam ∧ sxy ≤ svb+n}: svb ≥ (t/2-258n)/388, so M is large.
    -- By Markov on M: μ(A\B) ≤ (n²+2n)/(f₀·ρ^k·α_xy^n) ≤ 2·r·P.
    have hterm2 : μ (Aset \ Bset) ≤ 2 * r * P := by
      -- Strategy: show 1 ≤ 2r·prodFun(a) pointwise on (A\B) ∩ {bc},
      -- then integrate and apply expected_product_bound.
      -- Define the product function (integrand from expected_product_bound)
      let prodFun : AugConfig n → ℝ≥0∞ := fun a =>
        (((16 * n + 7 : ℕ) : ℝ≥0∞) ^ a.2.1 *
         ((16 * n - 5 : ℕ) : ℝ≥0∞) ^ a.2.2) /
        ((16 * n : ℕ) : ℝ≥0∞) ^ (a.2.1 + a.2.2)
      have hprod_meas : Measurable prodFun := Measurable.of_discrete
      -- Blank conservation: μ-a.s. sxy ≤ svb + n
      have hbc := blank_conservation hn c₀ t
      -- POINTWISE BOUND: on (A\B) ∩ {bc}, 1 ≤ 2·r·prodFun(a)
      -- This is the key arithmetic fact.
      have hpw : ∀ᵐ a ∂μ, a ∈ Aset \ Bset →
          (1 : ℝ≥0∞) ≤ 2 * r * prodFun a := by
        filter_upwards [hbc] with a ha_bc ha_AB
        -- ha_bc : a.2.2 ≤ a.2.1 + n
        -- ha_AB : a ∈ Aset \ Bset (i.e., active ∧ countingW < lam)
        -- Step 1: Extract counting constraint from ha_AB
        obtain ⟨ha_active, ha_notB⟩ := ha_AB
        have ha_aug : a ∈ augActiveCentral := ha_active
        simp only [hBset_def, Set.mem_setOf_eq, not_le] at ha_notB
        simp only [countingWActive, if_pos ha_aug] at ha_notB
        -- ha_notB : countingW a < lam
        -- Step 2: Extract ℕ counting constraint
        have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
        have hcount : t < 260 * a.2.1 + 516 * a.2.2 := by
          simp only [countingW, hlam_def] at ha_notB
          rw [ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _),
              Real.exp_lt_exp] at ha_notB
          have h2n_pos : (0 : ℝ) < 2 * ↑n := by positivity
          rw [div_lt_div_iff₀ hn_pos h2n_pos] at ha_notB
          have : (↑t : ℝ) < 260 * ↑a.2.1 + 516 * ↑a.2.2 := by nlinarith
          exact_mod_cast this
        -- Step 3: Apply the ℝ bound
        have hreal := pointwise_bound_real hn a.2.1 a.2.2 t ha_bc hcount
        -- Step 4: Convert ENNReal goal to ℝ using hreal
        -- Use le_div_iff to move denominator, convert nat casts to ofReal,
        -- then apply ofReal_le_ofReal with the ℝ bound.
        set svb := a.2.1; set sxy := a.2.2
        -- ENNReal ↔ ℝ conversion: show ofReal(X) = 2*r*prodFun a, then 1 ≤ ofReal(X)
        have h16n_pos : (0 : ℝ) < 16 * ↑n := by positivity
        have hn_real : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn
        have hD_ne : ((16 * n : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hD_ne_top : ((16 * n : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        have hR_nn : (0 : ℝ) ≤ (1 - 1 / (15000 * ↑n)) ^ t := by
          apply pow_nonneg; linarith [show 1 / (15000 * (↑n : ℝ)) ≤ 1 from
            div_le_one_of_le₀ (by nlinarith) (by positivity)]
        have hαxy_base_nn : (0 : ℝ) ≤ (16 * ↑n - 5) / (16 * ↑n) :=
          div_nonneg (by nlinarith) (le_of_lt h16n_pos)
        -- Step 1: prodFun a = ofReal(αvb^svb * αxy^sxy)
        have hpf_eq : prodFun a = ENNReal.ofReal (
            ((16 * (↑n : ℝ) + 7) / (16 * ↑n)) ^ svb *
            ((16 * (↑n : ℝ) - 5) / (16 * ↑n)) ^ sxy) := by
          -- Decompose ofReal through mul/pow/div
          rw [ENNReal.ofReal_mul (pow_nonneg (div_nonneg (by positivity)
                (le_of_lt h16n_pos)) _),
              ENNReal.ofReal_pow (div_nonneg (by positivity) (le_of_lt h16n_pos)),
              ENNReal.ofReal_pow hαxy_base_nn,
              ENNReal.ofReal_div_of_pos h16n_pos,
              ENNReal.ofReal_div_of_pos h16n_pos,
              -- Convert ℝ expressions to ℕ casts (order matters: +7, -5 before bare 16*↑n)
              show (16 * (↑n : ℝ) + 7) = ↑(16 * n + 7 : ℕ) from by push_cast; ring,
              show (16 * (↑n : ℝ) - 5) = ↑(16 * n - 5 : ℕ) from by
                rw [Nat.cast_sub (by omega)]; push_cast; ring]
          simp only [show (16 * (↑n : ℝ)) = ↑(16 * n : ℕ) from by push_cast; ring,
                     ENNReal.ofReal_natCast]
          -- Both sides now use ↑(16n+7), ↑(16n-5), ↑(16n) as ENNReal nat casts
          -- Convert to multiplicative form and normalize
          simp only [prodFun, div_eq_mul_inv, mul_pow, pow_add]
          rw [ENNReal.mul_inv (Or.inl (pow_ne_zero _ hD_ne))
                              (Or.inl (ENNReal.pow_ne_top hD_ne_top))]
          simp only [ENNReal.inv_pow, mul_comm, mul_left_comm, mul_assoc]; rfl
        -- Step 2: 2 * r = ofReal(2 * R^t)
        have h2r_eq : (2 : ℝ≥0∞) * r = ENNReal.ofReal (2 * (1 - 1 / (15000 * ↑n)) ^ t) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by
                rw [show (2:ℝ) = ↑(2:ℕ) from by norm_num]
                exact (ENNReal.ofReal_natCast 2).symm,
              hr_def, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        -- Step 3: final calc
        calc (1 : ℝ≥0∞)
            = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
          _ ≤ ENNReal.ofReal (2 * (1 - 1 / (15000 * ↑n)) ^ t *
              ((16 * ↑n + 7) / (16 * ↑n)) ^ svb *
              ((16 * ↑n - 5) / (16 * ↑n)) ^ sxy) :=
              ENNReal.ofReal_le_ofReal hreal
          _ = ENNReal.ofReal (2 * (1 - 1 / (15000 * ↑n)) ^ t *
              (((16 * ↑n + 7) / (16 * ↑n)) ^ svb *
              ((16 * ↑n - 5) / (16 * ↑n)) ^ sxy)) := by congr 1; ring
          _ = ENNReal.ofReal (2 * (1 - 1 / (15000 * ↑n)) ^ t) *
              ENNReal.ofReal (((16 * ↑n + 7) / (16 * ↑n)) ^ svb *
              ((16 * ↑n - 5) / (16 * ↑n)) ^ sxy) :=
              ENNReal.ofReal_mul (by positivity)
          _ = 2 * r * prodFun a := by rw [h2r_eq, hpf_eq]
      -- INTEGRATION: μ(A\B) ≤ 2r · ∫ prodFun ≤ 2r · P
      calc μ (Aset \ Bset)
          = ∫⁻ a, (Aset \ Bset).indicator 1 a ∂μ := by
            rw [lintegral_indicator
              (instDiscreteMeasurableSpaceAugConfig.forall_measurableSet _)]
            simp
        _ ≤ ∫⁻ a, 2 * r * prodFun a ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [hpw] with a ha
            simp only [Set.indicator_apply, Pi.one_apply]
            split_ifs with h
            · exact ha h
            · exact zero_le'
        _ = 2 * r * ∫⁻ a, prodFun a ∂μ :=
            lintegral_const_mul _ hprod_meas
        _ ≤ 2 * r * P := by
            gcongr
            simp only [hμ_def, hP_def, potentialCentralTrunc, if_pos hc₀]
            exact expected_product_bound hn c₀ t
    -- ARITHMETIC: lam ≤ r * P
    -- exp(-t/(2n)) ≤ (1-1/(15000n))^t · (n²+2n)/f₀
    have hlam_le_rP : lam ≤ r * P := by
      -- P ≥ 1 for active c₀
      have hP_ge_one : (1 : ℝ≥0∞) ≤ P := by
        have h := hc₀; rw [activeCentral_eq_ge_one hn] at h; exact h
      -- Suffices: lam ≤ r (since r * P ≥ r * 1 = r)
      suffices hlam_r : lam ≤ r by
        calc lam ≤ r := hlam_r
          _ = r * 1 := (mul_one r).symm
          _ ≤ r * P := by gcongr
      -- In ENNReal: ofReal(a) ≤ ofReal(b) from a ≤ b
      apply ENNReal.ofReal_le_ofReal
      -- In ℝ: exp(-t/(2n)) ≤ (1-1/(15000n))^t
      have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
      -- Base: exp(-1/(2n)) ≤ 1/(1+1/(2n)) ≤ 1-1/(15000n)
      have hbase : Real.exp (-(1 : ℝ) / (2 * ↑n)) ≤ 1 - 1 / (15000 * ↑n) := by
        have h1 := exp_neg_le_inv_one_add (show (0:ℝ) ≤ 1/(2*↑n) from by positivity)
        suffices hsuff : (1:ℝ) / (1 + 1 / (2 * ↑n)) ≤ 1 - 1 / (15000 * ↑n) by
          calc Real.exp (-(1 : ℝ) / (2 * ↑n))
              = Real.exp (-(1 / (2 * ↑n))) := by rw [neg_div]
            _ ≤ 1 / (1 + 1 / (2 * ↑n)) := h1
            _ ≤ 1 - 1 / (15000 * ↑n) := hsuff
        have h2n : (0:ℝ) < 2 * ↑n + 1 := by positivity
        have h10k : (0:ℝ) < 15000 * ↑n := by positivity
        have hsimp : (1:ℝ) / (1 + 1 / (2 * ↑n)) = 2 * ↑n / (2 * ↑n + 1) := by field_simp
        rw [hsimp, le_sub_iff_add_le, div_add_div _ _ h2n.ne' h10k.ne',
            div_le_one (mul_pos h2n h10k)]
        nlinarith [show (2:ℝ) ≤ ↑n from by exact_mod_cast hn]
      -- Raise to t-th power
      calc Real.exp (-(↑t : ℝ) / (2 * ↑n))
          = (Real.exp (-(1 : ℝ) / (2 * ↑n))) ^ t := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        _ ≤ (1 - 1 / (15000 * ↑n)) ^ t :=
            pow_le_pow_left₀ (Real.exp_nonneg _) hbase t
    -- COMBINE: μ(A) = μ(A∩B) + μ(A\B) ≤ μ(B) + μ(A\B) ≤ lam+2rP ≤ rP+2rP = 3rP
    calc μ Aset
        = μ (Aset ∩ Bset) + μ (Aset \ Bset) :=
          (measure_inter_add_diff Aset hBmeas).symm
      _ ≤ μ Bset + μ (Aset \ Bset) :=
          add_le_add (measure_mono Set.inter_subset_right) le_rfl
      _ ≤ lam + 2 * r * P := add_le_add hterm1 hterm2
      _ ≤ r * P + 2 * r * P := add_le_add hlam_le_rP le_rfl
      _ = 3 * r * P := by
          rw [show (3 : ℝ≥0∞) = 1 + 2 from by norm_num, add_mul, one_mul, add_mul]
  · -- Absorbed case: chain stays at c₀ ∉ activeCentral
    have hLHS : (absorbedKernelCentral hn ^ t) c₀ activeCentral = 0 := by
      -- absorbedKernelCentral freezes outside activeCentral:
      -- K c₀ = Kernel.id c₀ = dirac c₀, so (K^t) c₀ = dirac c₀ for all t.
      have hK : absorbedKernelCentral hn c₀ = Measure.dirac c₀ := by
        unfold absorbedKernelCentral
        rw [Kernel.piecewise_apply, if_neg hc₀, Kernel.id_apply]
      suffices h : (absorbedKernelCentral hn ^ t) c₀ = Measure.dirac c₀ by
        rw [h, Measure.dirac_apply' _
              (instDiscreteMeasurableSpaceConfig.forall_measurableSet _),
            Set.indicator_apply, if_neg hc₀]
      induction t with
      | zero =>
        simp only [pow_zero]
        change Kernel.id c₀ = Measure.dirac c₀
        exact Kernel.id_apply c₀
      | succ t ih =>
        exact Measure.ext (fun S hS => by
          rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hS, ih,
              MeasureTheory.lintegral_dirac' _
                (Kernel.measurable_coe _ hS), hK])
    rw [hLHS]; exact zero_le'

/-- Geometric decay for central region (wrapper matching ConvergenceTime statement). -/
theorem prob_in_activeCentral_le (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    (absorbedKernelCentral hn ^ t) c₀ activeCentral ≤
    3 * ENNReal.ofReal ((1 - 1 / (15000 * (n : ℝ))) ^ t) *
    potentialCentralTrunc c₀ :=
  central_geometric_decay hn c₀ t

/-- Convergence time from central region: unfolded potentialCentralTrunc. -/
theorem convergence_time_central (hn : n ≥ 2) (c₀ : Config n)
    (hc₀ : c₀ ∈ activeCentral) (t : ℕ) :
    (absorbedKernelCentral hn ^ t) c₀ activeCentral ≤
    3 * ENNReal.ofReal ((1 - 1 / (15000 * (n : ℝ))) ^ t) *
    (((n ^ 2 + 2 * n : ℕ) : ℝ≥0∞) * (c₀.potential : ℝ≥0∞)⁻¹) := by
  have h := prob_in_activeCentral_le hn c₀ t
  rwa [show potentialCentralTrunc c₀ =
    ((n ^ 2 + 2 * n : ℕ) : ℝ≥0∞) * (c₀.potential : ℝ≥0∞)⁻¹ from
    if_pos hc₀] at h

end Config
end PopProto

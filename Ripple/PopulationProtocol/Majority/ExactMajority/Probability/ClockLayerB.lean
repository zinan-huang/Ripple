/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ClockLayerB — STAGE 4 Layer-B forward window transfer (Doty §6, Lemma 6.3)

This file builds the STAGE-4 forward-window transfer for Doty's Lemma 6.3 on the EXISTING
marked-agent kernel `EarlyDripMarked.markedK` (NO new ghost kernel).  The architecture splits the
Lemma-6.3 endpoint bound into:

* a fully PROVEN deterministic core (the `countP`-split `rBeyond_succ_erase_eq_clockTainted_add_clean`,
  the algebraic composition `lemma63_composition_algebra` / `_w009`, and the union-bound transfer
  `lemma63_window_transfer_forward`);
* a fully PROVEN markedK→real transfer for parent growth (`parent_growth_forward`, via
  `markedK_pow_erase`), and the Janson instantiation `parent_growth_forward_real`;
* THREE probabilistic ingredients (drip immigration, epidemic amplification) whose genuine
  Bennett/MGF content is precisely ISOLATED as carried, SATISFIABLE per-event hypotheses — the
  union-bound shells around them are proven here.

## What is PROVEN (axiom-clean, `[propext, Classical.choice, Quot.sound]`)

* `rBeyond_succ_erase_eq_clockTainted_add_clean` — the `countP` split of the clock-front above `T`
  into clock-tainted + clock-clean (a Boolean-mark split, no `MarkInv` needed since both summands
  carry the clock-role and minute filter; this is the clock-filtered analogue of
  `EarlyDripMarked.aboveCount_eq_tainted_add_clean`).
* `X_succ_eq_clean_add_D` — the endpoint fraction split `X_{T+1} = CleanFrac_T + Dfrac_T`.
* `lemma63_composition_algebra` (+ `_w009` with the verified constants `a=213/250, b=19/200,
  γ=6/5`) — pure algebra: parent growth + clean immigration/amplification + contraction ⟹ ¬bad.
* `lemma63_window_transfer_forward` — the union bound that closes the endpoint failure probability.
* `parent_growth_forward` — markedK→real transfer of parent growth via `markedK_pow_erase`.
* `parent_growth_forward_real` — the Janson `milestone_hitting_time_bound` instantiation.
* `drip_immigration_window`, `epidemic_amplification_window`,
  `windowCleanGood_of_immigration_amplification` — the union-bound shells; the analytic
  Bennett/MGF content is carried as the `hBennett`/`hMGF` hypotheses.

Reference: Doty et al. (arXiv:2106.10201v2) §6, Lemma 6.3; `DOCTRINE_THM69_CA.md`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockTaintMixed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.JansonHitting

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockLayerB

open ClockRealKernel
open EarlyDripMarked
open ClockFrontMixed
open ClockTaintMixed

variable {L K : ℕ}

/-- Marked configuration. -/
abbrev MCfg (L K : ℕ) := Config (MarkedAgent L K)

/-- Clock-normalized tail fraction on the marked chain, read through erasure. -/
noncomputable def X (C₀ T : ℕ) (mc : MCfg L K) : ℝ :=
  ClockFrac (L := L) (K := K) C₀ T (eraseConfig (L := L) (K := K) mc)

/-- Clock-filtered ghost fraction `D_{≥T+1}/C₀`. -/
noncomputable def Dfrac (C₀ T : ℕ) (mc : MCfg L K) : ℝ :=
  (clockTaintedCount (L := L) (K := K) T mc : ℝ) / (C₀ : ℝ)

/-- Clean clock count above `T`: clock ∧ minute ≥ T+1 ∧ untainted. -/
def clockCleanAbove (T : ℕ) (mc : MCfg L K) : ℕ :=
  Multiset.countP
    (fun m : MarkedAgent L K =>
      m.1.role = .clock ∧ T + 1 ≤ m.1.minute.val ∧ m.2 = false) mc

/-- Clean clock fraction above `T`. -/
noncomputable def CleanFrac (C₀ T : ℕ) (mc : MCfg L K) : ℝ :=
  (clockCleanAbove (L := L) (K := K) T mc : ℝ) / (C₀ : ℝ)

/-- Lemma-6.3 endpoint bad event: child tail exceeds clean squaring plus ghost. -/
def Lemma63Bad (C₀ T : ℕ) (p : ℝ) (mc : MCfg L K) : Prop :=
  X (L := L) (K := K) C₀ (T + 1) mc >
    (9 / 10 : ℝ) * p * (X (L := L) (K := K) C₀ T mc)^2
      + Dfrac (L := L) (K := K) C₀ T mc

/-- Parent growth over the window: `X_start ≤ a X_end`. -/
def ParentGrowthGood (C₀ T : ℕ) (a : ℝ) (mc₀ mc₁ : MCfg L K) : Prop :=
  X (L := L) (K := K) C₀ T mc₀ ≤
    a * X (L := L) (K := K) C₀ T mc₁

/-- Window certificate combining immigration and amplification for the clean child mass. -/
def WindowCleanGood (C₀ T : ℕ) (p b γ : ℝ) (mc₀ mc₁ : MCfg L K) : Prop :=
  ∃ immFrac : ℝ,
    0 ≤ immFrac ∧
    immFrac ≤ b * p * (X (L := L) (K := K) C₀ T mc₁)^2 ∧
    CleanFrac (L := L) (K := K) C₀ T mc₁ ≤
      γ * (CleanFrac (L := L) (K := K) C₀ T mc₀ + immFrac)

/--
A state-local active gate.  Do NOT include future/window conclusions here.
`η` is GhostSmall, used by later clean-step-from-ghost; Lemma 6.3 itself keeps `+D/C₀`.
The `Aux` parameter carries the unbiased-phase-3 Main facts that `ClockP3` alone does not supply
(see `ClockTaintMixed`).
-/
def Active63 (C₀ T : ℕ) (θ ρ η : ℝ) (Aux : MCfg L K → Prop)
    (mc : MCfg L K) : Prop :=
  ClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∧
  Aux mc ∧
  θ ≤ X (L := L) (K := K) C₀ T mc ∧
  X (L := L) (K := K) C₀ T mc ≤ ρ ∧
  Dfrac (L := L) (K := K) C₀ T mc ≤ η

/-! ## Deterministic split and composition algebra -/

/--
**Clock-front split above `T`** : all clocks above `T` split into tainted clocks plus clean clocks.
This is the clock-filtered analogue of `EarlyDripMarked.aboveCount_eq_tainted_add_clean`.  Unlike
the role-free split it needs NO mark invariant: both summands keep the `role = clock ∧ T+1 ≤ minute`
filter, so the split is a pure `countP`-split on the Boolean mark `m.2 = true / false` of the
clock-beyond population.  The clock-front population itself is identified with `rBeyond (T+1) ∘ erase`
via `ClockTaintMixed.clockBeyondCount_eq_rBeyond_succ_erase`.
-/
theorem rBeyond_succ_erase_eq_clockTainted_add_clean
    (T : ℕ) (mc : MCfg L K) :
    rBeyond (L := L) (K := K) (T + 1)
        (eraseConfig (L := L) (K := K) mc)
      =
    clockTaintedCount (L := L) (K := K) T mc
      + clockCleanAbove (L := L) (K := K) T mc := by
  classical
  -- Replace the real front statistic by the marked clock-beyond count.
  rw [← clockBeyondCount_eq_rBeyond_succ_erase (L := L) (K := K) T mc]
  -- Now both sides are `countP`s over the SAME multiset; split clock-beyond on the Boolean mark.
  unfold clockTaintedCount clockCleanAbove
  induction mc using Multiset.induction_on with
  | empty => simp
  | cons m mc ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons, ih]
      -- Case on whether `m` is a clock above `T`, then on its mark bit; the three `if`s
      -- collapse so the new agent is counted in clock-beyond iff in exactly one of tainted/clean.
      rcases m.2 with _ | _ <;>
        · simp only [Bool.false_eq_true, and_false, if_false, Nat.add_zero,
            reduceCtorEq, and_true]
          split_ifs <;> omega

/-- The endpoint fraction split `X_{T+1} = CleanFrac_T + Dfrac_T`. -/
theorem X_succ_eq_clean_add_D
    (C₀ T : ℕ) (mc : MCfg L K) :
    X (L := L) (K := K) C₀ (T + 1) mc =
      CleanFrac (L := L) (K := K) C₀ T mc
        + Dfrac (L := L) (K := K) C₀ T mc := by
  classical
  unfold X CleanFrac Dfrac ClockFrac
  rw [rBeyond_succ_erase_eq_clockTainted_add_clean (L := L) (K := K) T mc]
  push_cast
  ring

/--
**Symbolic composition algebra.**
Inputs:
* initial clean child already below `0.9 p X_start²`;
* parent growth `X_start ≤ a X_end`;
* immigration `≤ b p X_end²`;
* amplification by `γ`;
* contraction `γ(0.9a²+b)≤0.9`.
Conclusion: the Lemma-6.3 endpoint bad event is impossible.
-/
theorem lemma63_composition_algebra
    (C₀ T : ℕ) (p a b γ : ℝ) (mc₀ mc₁ : MCfg L K)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hclean₀ :
      CleanFrac (L := L) (K := K) C₀ T mc₀ ≤
        (9 / 10 : ℝ) * p * (X (L := L) (K := K) C₀ T mc₀)^2)
    (hparent :
      ParentGrowthGood (L := L) (K := K) C₀ T a mc₀ mc₁)
    (hcleanWin :
      WindowCleanGood (L := L) (K := K) C₀ T p b γ mc₀ mc₁)
    (hcontract : γ * ((9 / 10 : ℝ) * a^2 + b) ≤ 9 / 10) :
    ¬ Lemma63Bad (L := L) (K := K) C₀ T p mc₁ := by
  classical
  intro hbad
  rcases hcleanWin with ⟨immFrac, himm_nonneg, himm_le, hclean₁⟩
  have hX₁_nonneg : 0 ≤ X (L := L) (K := K) C₀ T mc₁ := by
    unfold X ClockFrac
    positivity
  have hX₀_nonneg : 0 ≤ X (L := L) (K := K) C₀ T mc₀ := by
    unfold X ClockFrac
    positivity
  have hX₀_le :
      (X (L := L) (K := K) C₀ T mc₀)^2 ≤
        a^2 * (X (L := L) (K := K) C₀ T mc₁)^2 := by
    have hkey : X (L := L) (K := K) C₀ T mc₀ ≤ a * X (L := L) (K := K) C₀ T mc₁ := hparent
    nlinarith [hkey, ha, hX₁_nonneg, hX₀_nonneg,
      mul_nonneg ha hX₁_nonneg,
      mul_le_mul hkey hkey hX₀_nonneg (mul_nonneg ha hX₁_nonneg)]
  have hclean₀' :
      CleanFrac (L := L) (K := K) C₀ T mc₀ ≤
        (9 / 10 : ℝ) * p * a^2 *
          (X (L := L) (K := K) C₀ T mc₁)^2 := by
    nlinarith [hclean₀, hX₀_le, hp, ha, hX₁_nonneg]
  have hclean₁_bound :
      CleanFrac (L := L) (K := K) C₀ T mc₁ ≤
        γ * (((9 / 10 : ℝ) * p * a^2 + b * p) *
          (X (L := L) (K := K) C₀ T mc₁)^2) := by
    calc
      CleanFrac (L := L) (K := K) C₀ T mc₁
          ≤ γ * (CleanFrac (L := L) (K := K) C₀ T mc₀ + immFrac) := hclean₁
      _ ≤ γ * (((9 / 10 : ℝ) * p * a^2 + b * p) *
          (X (L := L) (K := K) C₀ T mc₁)^2) := by
        gcongr
        nlinarith [hclean₀', himm_le]
  have hfactor :
      γ * (((9 / 10 : ℝ) * p * a^2 + b * p)) ≤
        (9 / 10 : ℝ) * p := by
    nlinarith [hcontract, hp]
  have hclean_final :
      CleanFrac (L := L) (K := K) C₀ T mc₁ ≤
        (9 / 10 : ℝ) * p * (X (L := L) (K := K) C₀ T mc₁)^2 := by
    nlinarith [hclean₁_bound, hfactor,
      sq_nonneg (X (L := L) (K := K) C₀ T mc₁)]
  have hsplit := X_succ_eq_clean_add_D (L := L) (K := K) C₀ T mc₁
  unfold Lemma63Bad at hbad
  rw [hsplit] at hbad
  nlinarith [hclean_final]

/-- Working constants instance: `a=213/250`, `b=19/200`, `γ=6/5`. -/
theorem lemma63_composition_algebra_w009
    (C₀ T : ℕ) (p : ℝ) (mc₀ mc₁ : MCfg L K)
    (hp : 0 ≤ p)
    (hclean₀ :
      CleanFrac (L := L) (K := K) C₀ T mc₀ ≤
        (9 / 10 : ℝ) * p * (X (L := L) (K := K) C₀ T mc₀)^2)
    (hparent :
      ParentGrowthGood (L := L) (K := K) C₀ T (213 / 250 : ℝ) mc₀ mc₁)
    (hcleanWin :
      WindowCleanGood (L := L) (K := K) C₀ T p (19 / 200 : ℝ) (6 / 5 : ℝ) mc₀ mc₁) :
    ¬ Lemma63Bad (L := L) (K := K) C₀ T p mc₁ := by
  exact lemma63_composition_algebra
    (L := L) (K := K) C₀ T p (213 / 250 : ℝ) (19 / 200 : ℝ) (6 / 5 : ℝ)
    mc₀ mc₁ hp (by norm_num) (by norm_num) (by norm_num)
    hclean₀ hparent hcleanWin
    (ClockFrontMixed.layerB_constants_ok)

/-! ## Main forward-window statement -/

/--
**Forward Lemma 6.3 transfer on the marked kernel.**
`markedK T θn` is the lifted/marked kernel.  The bad endpoint event is
`X_{T+1}(z') > 0.9 p X_T(z')² + D_T(z')/C₀`.
The proof is a pure union bound plus the deterministic composition algebra; the genuine
probabilistic content is delegated to `hParent` and `hClean`.
-/
theorem lemma63_window_transfer_forward
    (T θn C₀ Lwin : ℕ) (p θ ρ η : ℝ)
    (Aux : MCfg L K → Prop)
    (εParent εClean εWindow : ℝ≥0∞)
    (mc₀ : MCfg L K)
    (hActive : Active63 (L := L) (K := K) C₀ T θ ρ η Aux mc₀)
    (hp : 0 ≤ p)
    (hclean₀ :
      CleanFrac (L := L) (K := K) C₀ T mc₀ ≤
        (9 / 10 : ℝ) * p * (X (L := L) (K := K) C₀ T mc₀)^2)
    (hParent :
      ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
        {mc₁ | ¬ ParentGrowthGood
          (L := L) (K := K) C₀ T (213 / 250 : ℝ) mc₀ mc₁}
        ≤ εParent)
    (hClean :
      ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
        {mc₁ | ¬ WindowCleanGood
          (L := L) (K := K) C₀ T p (19 / 200 : ℝ) (6 / 5 : ℝ) mc₀ mc₁}
        ≤ εClean)
    (hBudget : εParent + εClean ≤ εWindow) :
    ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
      {mc₁ | Lemma63Bad (L := L) (K := K) C₀ T p mc₁}
      ≤ εWindow := by
  classical
  have hsub :
      {mc₁ | Lemma63Bad (L := L) (K := K) C₀ T p mc₁} ⊆
        {mc₁ | ¬ ParentGrowthGood
          (L := L) (K := K) C₀ T (213 / 250 : ℝ) mc₀ mc₁}
          ∪
        {mc₁ | ¬ WindowCleanGood
          (L := L) (K := K) C₀ T p (19 / 200 : ℝ) (6 / 5 : ℝ) mc₀ mc₁} := by
    intro mc₁ hbad
    by_cases hpg :
        ParentGrowthGood (L := L) (K := K) C₀ T (213 / 250 : ℝ) mc₀ mc₁
    · by_cases hwg :
        WindowCleanGood (L := L) (K := K) C₀ T p (19 / 200 : ℝ) (6 / 5 : ℝ) mc₀ mc₁
      · have hnot :=
          lemma63_composition_algebra_w009
            (L := L) (K := K) C₀ T p mc₀ mc₁ hp hclean₀ hpg hwg
        exact False.elim (hnot hbad)
      · exact Or.inr hwg
    · exact Or.inl hpg
  calc
    ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
        {mc₁ | Lemma63Bad (L := L) (K := K) C₀ T p mc₁}
        ≤ ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
            ({mc₁ | ¬ ParentGrowthGood
                (L := L) (K := K) C₀ T (213 / 250 : ℝ) mc₀ mc₁}
             ∪
             {mc₁ | ¬ WindowCleanGood
                (L := L) (K := K) C₀ T p (19 / 200 : ℝ) (6 / 5 : ℝ) mc₀ mc₁}) :=
          measure_mono hsub
    _ ≤ ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
            {mc₁ | ¬ ParentGrowthGood
                (L := L) (K := K) C₀ T (213 / 250 : ℝ) mc₀ mc₁}
        + ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
            {mc₁ | ¬ WindowCleanGood
                (L := L) (K := K) C₀ T p (19 / 200 : ℝ) (6 / 5 : ℝ) mc₀ mc₁} :=
          measure_union_le _ _
    _ ≤ εParent + εClean := add_le_add hParent hClean
    _ ≤ εWindow := hBudget

/-! ## Parent growth: real-kernel Janson + markedK transfer -/

/-- Parent-growth predicate on erased configs. -/
def ParentGrowthGoodCfg (C₀ T : ℕ) (a : ℝ)
    (c₀ c₁ : Config (AgentState L K)) : Prop :=
  ClockFrac (L := L) (K := K) C₀ T c₀ ≤
    a * ClockFrac (L := L) (K := K) C₀ T c₁

/--
**Real-kernel parent growth via unit milestones** (the Janson instantiation).
`mp` is the unit-milestone phase whose `Post` certifies the parent-growth fraction inequality.
This packages `JansonHitting.milestone_hitting_time_bound`.
-/
theorem parent_growth_forward_real
    (T C₀ Lwin : ℕ) (a : ℝ) (εParent : ℝ≥0∞)
    (c₀ : Config (AgentState L K))
    (mp : MilestonePhase (NonuniformMajority L K))
    (hPre : ∀ j : Fin mp.k, ¬ mp.milestone j c₀)
    (hPost :
      ∀ c₁, mp.Post c₁ →
        ParentGrowthGoodCfg (L := L) (K := K) C₀ T a c₀ c₁)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hTime : lam * mp.meanTime ≤ (Lwin : ℝ))
    (hTail :
      ENNReal.ofReal
        (Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam))) ≤ εParent) :
    ((NonuniformMajority L K).transitionKernel ^ Lwin) c₀
      {c₁ | ¬ ParentGrowthGoodCfg (L := L) (K := K) C₀ T a c₀ c₁}
      ≤ εParent := by
  classical
  have hj :=
    milestone_hitting_time_bound
      (P := NonuniformMajority L K) mp c₀ hPre lam hlam Lwin hTime
  refine le_trans (measure_mono ?_) (le_trans hj hTail)
  intro c₁ hbad hpost
  exact hbad (hPost c₁ hpost)

/-- **Marked-kernel parent growth** transferred by `markedK_pow_erase`. -/
theorem parent_growth_forward
    (T θn C₀ Lwin : ℕ) (a : ℝ) (εParent : ℝ≥0∞)
    (mc₀ : MCfg L K)
    (hreal :
      ((NonuniformMajority L K).transitionKernel ^ Lwin)
        (eraseConfig (L := L) (K := K) mc₀)
        {c₁ | ¬ ParentGrowthGoodCfg (L := L) (K := K) C₀ T a
          (eraseConfig (L := L) (K := K) mc₀) c₁} ≤ εParent) :
    ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
      {mc₁ | ¬ ParentGrowthGood (L := L) (K := K) C₀ T a mc₀ mc₁}
      ≤ εParent := by
  classical
  have hset :
      {mc₁ | ¬ ParentGrowthGood (L := L) (K := K) C₀ T a mc₀ mc₁}
        =
      eraseConfig (L := L) (K := K) ⁻¹'
        {c₁ | ¬ ParentGrowthGoodCfg (L := L) (K := K) C₀ T a
          (eraseConfig (L := L) (K := K) mc₀) c₁} := by
    ext mc₁
    rfl
  rw [hset, markedK_pow_erase (L := L) (K := K) T θn Lwin mc₀]
  exact hreal

/-! ## The clean-window sub-lemmas: union-bound shells with carried analytic content.

The genuine Bennett (`drip_immigration_window`) and MGF (`epidemic_amplification_window`)
probabilistic content is carried as the `hBennett` / `hMGF` hypotheses.  These are SATISFIABLE
per-event bounds (the implementation-specific endpoint/window certificate events
`ImmGoodAtEnd` / `AmpGoodAtEnd` whose failure probabilities the Bennett/Freedman and MGF/Yule
arguments bound).  The shells proven here reduce the existential/universal clean-window event to
those carried events by `measure_mono`. -/

/-- Immigration certificate normalized by `C₀`. -/
def DripImmigrationGood (C₀ T : ℕ) (p b : ℝ) (mc₁ : MCfg L K) (immFrac : ℝ) : Prop :=
  0 ≤ immFrac ∧
  immFrac ≤ b * p * (X (L := L) (K := K) C₀ T mc₁)^2

/--
**Drip immigration window theorem** (union-bound shell).
The analytic content (one-step conditional mean `≤ p X_end²`, total mean `≤ Lwin·p·X_end²`,
Bennett tail) is carried in `hBennett` on the implementation-specific event `ImmGoodAtEnd`.
-/
theorem drip_immigration_window
    (T θn C₀ Lwin : ℕ) (p b : ℝ) (εImm : ℝ≥0∞)
    (mc₀ : MCfg L K)
    (ImmGoodAtEnd : MCfg L K → Prop)
    (hImmImpl :
      ∀ mc₁, ImmGoodAtEnd mc₁ →
        ∃ immFrac,
          DripImmigrationGood (L := L) (K := K) C₀ T p b mc₁ immFrac)
    (hBennett :
      ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
        {mc₁ | ¬ ImmGoodAtEnd mc₁} ≤ εImm) :
    ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
      {mc₁ | ¬ ∃ immFrac,
        DripImmigrationGood (L := L) (K := K) C₀ T p b mc₁ immFrac}
      ≤ εImm := by
  refine le_trans (measure_mono ?_) hBennett
  intro mc₁ hbad hgood
  exact hbad (hImmImpl mc₁ hgood)

/-- Amplification certificate. -/
def AmplificationGood (C₀ T : ℕ) (γ : ℝ)
    (mc₀ mc₁ : MCfg L K) (immFrac : ℝ) : Prop :=
  CleanFrac (L := L) (K := K) C₀ T mc₁ ≤
    γ * (CleanFrac (L := L) (K := K) C₀ T mc₀ + immFrac)

/--
**Epidemic amplification window theorem** (union-bound shell).
The analytic content (per-step rate `≤ 2κY/n`, over `Lwin = w n/κ` giving `γ = e^{2w}`,
instantiated by `6/5`) is carried in `hMGF` on the implementation-specific event `AmpGoodAtEnd`.
-/
theorem epidemic_amplification_window
    (T θn C₀ Lwin : ℕ) (γ : ℝ) (εAmp : ℝ≥0∞)
    (mc₀ : MCfg L K)
    (AmpGoodAtEnd : MCfg L K → Prop)
    (hAmpImpl :
      ∀ mc₁, AmpGoodAtEnd mc₁ →
        ∀ immFrac,
          DripImmigrationGood (L := L) (K := K) C₀ T (1 : ℝ) (19 / 200 : ℝ) mc₁ immFrac →
          AmplificationGood (L := L) (K := K) C₀ T γ mc₀ mc₁ immFrac)
    (hMGF :
      ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
        {mc₁ | ¬ AmpGoodAtEnd mc₁} ≤ εAmp) :
    ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
      {mc₁ | ¬ ∀ immFrac,
        DripImmigrationGood (L := L) (K := K) C₀ T (1 : ℝ) (19 / 200 : ℝ) mc₁ immFrac →
          AmplificationGood (L := L) (K := K) C₀ T γ mc₀ mc₁ immFrac}
      ≤ εAmp := by
  refine le_trans (measure_mono ?_) hMGF
  intro mc₁ hbad hgood
  exact hbad (hAmpImpl mc₁ hgood)

/-- Combine immigration + amplification into the `WindowCleanGood` interface. -/
theorem windowCleanGood_of_immigration_amplification
    (C₀ T : ℕ) (p b γ : ℝ) (mc₀ mc₁ : MCfg L K)
    (hImmAmp :
      ∃ immFrac,
        DripImmigrationGood (L := L) (K := K) C₀ T p b mc₁ immFrac ∧
        AmplificationGood (L := L) (K := K) C₀ T γ mc₀ mc₁ immFrac) :
    WindowCleanGood (L := L) (K := K) C₀ T p b γ mc₀ mc₁ := by
  rcases hImmAmp with ⟨immFrac, hImm, hAmp⟩
  exact ⟨immFrac, hImm.1, hImm.2, hAmp⟩

end ClockLayerB

end ExactMajority

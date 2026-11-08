/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Seam Janson drift

This file gives a paper-scale seam epidemic tail: once a seam has at least one
`phase ≥ p+1` seed inside the `allPhaseGe p n` window, the remaining spread is
bounded by the same milestone/Janson epidemic clock as the canonical rumor
epidemic.  The result is local: it does not change the shared
`EpidemicConvergence` calibration.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceEpidemics
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2TimeConvergence
import Ripple.PopulationProtocol.ExactMajority.Probability.RoleSplitConcentration

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

attribute [local instance] Classical.propDecidable

namespace RoleSplitConcentration
namespace MilestonePhaseOn

variable {L K : ℕ} {P : Protocol (AgentState L K)}

/-- Partial-start MGF ceiling: from any start, the truncated partial MGF is at
most the full product over all milestones. -/
theorem truncMGF_le_full (mp : MilestonePhaseOn (L := L) (K := K) P)
    {s : ℝ} (hs_pos : 0 < s)
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c : Config (AgentState L K)) :
    mp.truncMGF s c ≤ ENNReal.ofReal (∏ i : Fin mp.k, mp.mgfFactor s i) := by
  by_cases hPost : mp.Post c
  · rw [truncMGF, if_pos hPost]
    exact bot_le
  · rw [truncMGF, if_neg hPost]
    apply ENNReal.ofReal_le_ofReal
    unfold partialMGF
    exact Finset.prod_le_prod_of_subset_of_one_le
      (by intro i hi; exact Finset.mem_univ i)
      (fun i _ => (mp.mgfFactor_pos hs_valid i).le)
      (fun i _ _ => mp.mgfFactor_ge_one hs_pos hs_valid i)

/-- Inv-relative MGF tail from a partial start.  Unlike
`milestone_tail_bound_via_mgf_on`, this does not require initially unreached
milestones; already reached milestones are simply omitted by the partial MGF and
then bounded by the full product. -/
theorem milestone_tail_bound_via_mgf_on_partial
    (mp : MilestonePhaseOn (L := L) (K := K) P)
    (c₀ : Config (AgentState L K)) (hInv₀ : mp.Inv c₀)
    {s : ℝ} (hs_pos : 0 < s)
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1) (t : ℕ) :
    (P.transitionKernel ^ t) c₀ {c | ¬ mp.Post c} ≤
      ENNReal.ofReal (Real.exp (-s * t) *
        ∏ i : Fin mp.k, mp.mgfFactor s i) := by
  by_cases hk : mp.k = 0
  · have hempty : {c : Config (AgentState L K) | ¬ mp.Post c} = ∅ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not, Post]
      intro i; exact absurd i.2 (by omega)
    simp [hempty]
  have hexp_s_pos : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
  have hmarkov := mul_meas_ge_le_lintegral₀
    (μ := (P.transitionKernel ^ t) c₀) (mp.truncMGF_measurable s).aemeasurable
    (1 : ℝ≥0∞)
  simp only [one_mul] at hmarkov
  calc (P.transitionKernel ^ t) c₀ {c | ¬ mp.Post c}
      ≤ (P.transitionKernel ^ t) c₀ {c | 1 ≤ mp.truncMGF s c} :=
        measure_mono (mp.not_post_subset_ge_one hs_pos hs_valid)
    _ ≤ ∫⁻ c', mp.truncMGF s c' ∂((P.transitionKernel ^ t) c₀) := hmarkov
    _ ≤ ENNReal.ofReal (Real.exp (-s)) ^ t * mp.truncMGF s c₀ :=
        mp.lintegral_geometric_decay_on hs_pos hs_valid t c₀ hInv₀
    _ ≤ ENNReal.ofReal (Real.exp (-s)) ^ t *
          ENNReal.ofReal (∏ i : Fin mp.k, mp.mgfFactor s i) := by
        gcongr
        exact mp.truncMGF_le_full hs_pos hs_valid c₀
    _ = ENNReal.ofReal (Real.exp (-s * t) *
          ∏ i : Fin mp.k, mp.mgfFactor s i) := by
        rw [← ENNReal.ofReal_pow hexp_s_pos.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show -s * (t : ℝ) = (t : ℝ) * (-s) by ring, Real.exp_nat_mul]

/-- Inv-relative Janson hitting-time bound from a partial start. -/
theorem milestone_hitting_time_bound_on_partial
    (mp : MilestonePhaseOn (L := L) (K := K) P)
    (c₀ : Config (AgentState L K)) (hInv₀ : mp.Inv c₀)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (t : ℕ) (ht : lam * mp.meanTime ≤ (t : ℝ)) :
    (P.transitionKernel ^ t) c₀ {c | ¬ mp.Post c} ≤
      ENNReal.ofReal (Real.exp (-mp.pMin * mp.meanTime *
        (lam - 1 - Real.log lam))) := by
  by_cases hk : mp.k = 0
  · have hempty : {c : Config (AgentState L K) | ¬ mp.Post c} = ∅ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not, Post]
      intro i; exact absurd i.2 (by omega)
    simp [hempty]
  by_cases hlam_eq : lam = 1
  · have hzero : -mp.pMin * mp.meanTime * (lam - 1 - Real.log lam) = 0 := by
      rw [hlam_eq, Real.log_one]; ring
    rw [hzero, Real.exp_zero, ENNReal.ofReal_one]
    have hMK : ∀ s : ℕ, IsMarkovKernel (P.transitionKernel ^ s) := by
      intro s
      induction s with
      | zero =>
          rw [pow_zero]
          exact inferInstanceAs
            (IsMarkovKernel (Kernel.id : Kernel (Config (AgentState L K)) _))
      | succ s ih =>
          haveI := ih
          rw [pow_succ]
          exact inferInstanceAs (IsMarkovKernel ((P.transitionKernel ^ s) ∘ₖ _))
    haveI := hMK t
    haveI : IsProbabilityMeasure ((P.transitionKernel ^ t) c₀) :=
      IsMarkovKernel.isProbabilityMeasure _
    calc (P.transitionKernel ^ t) c₀ {c | ¬ mp.Post c}
        ≤ (P.transitionKernel ^ t) c₀ Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ 1 := prob_le_one
  · have hlam_gt : 1 < lam := lt_of_le_of_ne hlam (Ne.symm hlam_eq)
    have hk_pos : 0 < mp.k := Nat.pos_of_ne_zero hk
    set s : ℝ := mp.pMin * (1 - 1 / lam) with hs_def
    have hpmin_pos : 0 < mp.pMin := mp.pMin_pos hk_pos
    have hs_pos : 0 < s := by
      apply mul_pos hpmin_pos
      have : 1 / lam < 1 := by rw [div_lt_one (by linarith)]; exact hlam_gt
      linarith
    have hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1 := by
      intro i
      have hsi : s ≤ mp.p i := by
        calc s = mp.pMin * (1 - 1 / lam) := hs_def
          _ ≤ mp.pMin * 1 := by
              apply mul_le_mul_of_nonneg_left _ hpmin_pos.le
              linarith [div_pos one_pos (show (0 : ℝ) < lam by linarith)]
          _ = mp.pMin := mul_one _
          _ ≤ mp.p i := mp.pMin_le i
      have hne : (-s : ℝ) ≠ 0 := by linarith
      calc (1 - mp.p i) * Real.exp s
          ≤ (1 - s) * Real.exp s := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos s).le
            linarith
        _ < 1 := by
            have h1 : 1 - s < Real.exp (-s) := by
              linarith [Real.add_one_lt_exp hne]
            have h2 := mul_lt_mul_of_pos_right h1 (Real.exp_pos s)
            rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
    have h_opt := janson_exponential_tail_from_mgf mp.toDummyMP lam hlam (t : ℝ) ht s hs_def
    rw [mp.toDummyMP_meanTime, mp.toDummyMP_pMin] at h_opt
    have h_tail := mp.milestone_tail_bound_via_mgf_on_partial c₀ hInv₀ hs_pos hs_valid t
    have hkp : geometricProductMGF mp.toDummyMP.k mp.toDummyMP.p s =
        ∏ i : Fin mp.k, mp.mgfFactor s i := mp.geometricProductMGF_eq_prod_mgfFactor s
    rw [hkp] at h_opt
    exact le_trans h_tail (ENNReal.ofReal_le_ofReal h_opt)

end MilestonePhaseOn
end RoleSplitConcentration

namespace AdvanceJansonDrift

open AdvanceEpidemics
open RoleSplitConcentration

variable {L K : ℕ}

/-- The seam milestone at level `i`: at least `i+2` agents have advanced to
phase `≥ p+1`.  With `k = n-1`, the last milestone is `geCount ≥ n`. -/
def advanceMilestone (p _n i : ℕ) (c : Config (AgentState L K)) : Prop :=
  i + 2 ≤ geCount (L := L) (K := K) (p + 1) c

/-- Seam epidemic milestones over the invariant window `Qwin p n`.  The rates
are exactly the canonical rumor rates `(i+1)(n-i-1)/(n(n-1))`; the progress
field is discharged by `AdvanceEpidemics.ge_advance_prob`. -/
noncomputable def advanceMilestonePhase (p n : ℕ) (hn : 2 ≤ n) :
    MilestonePhaseOn (L := L) (K := K) (NonuniformMajority L K) where
  k := n - 1
  milestone i c := advanceMilestone (L := L) (K := K) p n i.val c
  p i := Phase2Time.epP n i.val
  hp_pos i := Phase2Time.epP_pos hn (by have := i.isLt; omega)
  hp_le_one i := Phase2Time.epP_le_one hn (by have := i.isLt; omega)
  milestone_monotone := by
    intro i c c' h hsupp
    exact geCount_ge_monotone (L := L) (K := K) (p + 1) (i.val + 2) c c' h hsupp
  Inv := SeededAdvanceWin (L := L) (K := K) p n
  inv_closed := by
    intro c hInv
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ¬ SeededAdvanceWin (L := L) (K := K) p n c'} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff
      (p := (NonuniformMajority L K).stepDistOrSelf c)
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro c' hsupp hbad
    exact hbad (SeededAdvanceWin_absorbing (L := L) (K := K) p n c c' hInv hsupp)
  progress_on := by
    intro i c hInv hprev hcur
    have hcount_eq :
        geCount (L := L) (K := K) (p + 1) c = i.val + 1 := by
      have hlt_count :
          geCount (L := L) (K := K) (p + 1) c < i.val + 2 :=
        Nat.lt_of_not_ge hcur
      have hge_count : i.val + 1 ≤ geCount (L := L) (K := K) (p + 1) c := by
        by_cases hi0 : i.val = 0
        · have hseed := hInv.2
          omega
        · have hprev' := hprev ⟨i.val - 1, by omega⟩ (by
            exact Fin.mk_lt_mk.mpr (by omega))
          unfold advanceMilestone at hprev'
          simp only at hprev'
          omega
      omega
    have hbound := ge_advance_prob (L := L) (K := K) p n hn c hInv.1
    have heq :
        ((((geCount (L := L) (K := K) (p + 1) c *
            (n - geCount (L := L) (K := K) (p + 1) c) : ℕ) : ℝ)
          / ((n : ℝ) * ((n : ℝ) - 1)))) = Phase2Time.epP n i.val := by
      have hi_le : i.val + 1 ≤ n := by
        have := i.isLt
        omega
      have hn1 : 1 ≤ n := by omega
      rw [hcount_eq]
      unfold Phase2Time.epP
      norm_num [Nat.cast_mul, Nat.cast_sub hi_le, Nat.cast_sub hn1]
    rw [heq] at hbound
    calc ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | advanceMilestone (L := L) (K := K) p n i.val c'}
        ≥ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | geCount (L := L) (K := K) (p + 1) c + 1 ≤
              geCount (L := L) (K := K) (p + 1) c'} := by
            apply measure_mono
            intro c' hc'
            simp only [Set.mem_setOf_eq] at hc' ⊢
            unfold advanceMilestone
            omega
      _ ≥ ENNReal.ofReal (Phase2Time.epP n i.val) := hbound

theorem advance_meanTime_eq_epidemic (p n : ℕ) (hn : 2 ≤ n) :
    (advanceMilestonePhase (L := L) (K := K) p n hn).meanTime =
      (Phase2Time.epidemicMilestonePhase n hn).meanTime := by
  rfl

theorem advance_pMin_eq_epidemic (p n : ℕ) (hn : 2 ≤ n) :
    (advanceMilestonePhase (L := L) (K := K) p n hn).pMin =
      (Phase2Time.epidemicMilestonePhase n hn).pMin := by
  rfl

/-- The seam Janson horizon: `⌈5 · meanTime⌉`, identical in scale to the
canonical rumor epidemic but valid from partial starts. -/
noncomputable def advanceJansonT (p n : ℕ) (hn : 2 ≤ n) : ℕ :=
  ⌈(5 : ℝ) * (advanceMilestonePhase (L := L) (K := K) p n hn).meanTime⌉₊

theorem advanceJansonT_eq_epidemicWindow (p n : ℕ) (hn : 2 ≤ n) :
    advanceJansonT (L := L) (K := K) p n hn = Phase2Time.epidemicWindow n hn := by
  unfold advanceJansonT Phase2Time.epidemicWindow
  rw [advance_meanTime_eq_epidemic (L := L) (K := K) p n hn]

/-- The new seam horizon is `≤ 11 n (log n + 1)` interactions. -/
theorem advanceJansonT_le_logn (p n : ℕ) (hn : 2 ≤ n) :
    (advanceJansonT (L := L) (K := K) p n hn : ℝ) ≤
      11 * (n : ℝ) * (Real.log n + 1) := by
  rw [advanceJansonT_eq_epidemicWindow (L := L) (K := K) p n hn]
  simpa [Phase2Time.epidemicPhaseConvergence] using
    (Phase2Time.epidemic_phase_logn_scale n hn).1

theorem advance_janson_exp_le_inv_sq (p n : ℕ) (hn : 2 ≤ n) :
    Real.exp (-(advanceMilestonePhase (L := L) (K := K) p n hn).pMin *
        (advanceMilestonePhase (L := L) (K := K) p n hn).meanTime *
        (5 - 1 - Real.log 5)) ≤ ((n : ℝ) ^ 2)⁻¹ := by
  have hpot₀ := Phase2Time.pMin_mul_meanTime_ge n hn
  have hpot :
      Real.log (n : ℝ) ≤
        (advanceMilestonePhase (L := L) (K := K) p n hn).pMin *
          (advanceMilestonePhase (L := L) (K := K) p n hn).meanTime := by
    simpa [advance_pMin_eq_epidemic (L := L) (K := K) p n hn,
      advance_meanTime_eq_epidemic (L := L) (K := K) p n hn] using hpot₀
  have hpot_nonneg :
      0 ≤ (advanceMilestonePhase (L := L) (K := K) p n hn).pMin *
          (advanceMilestonePhase (L := L) (K := K) p n hn).meanTime := by
    exact le_trans (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) hpot
  simpa [mul_assoc] using
    (RoleSplitConcentration.jansonExp_le_inv_sq (n := n) (by omega : 1 ≤ n)
      hpot_nonneg hpot RoleSplitConcentration.five_sub_one_sub_log_five_ge_two)

/-- The milestone postcondition forces `geFinished`; on a size-`n` support slice
this is exactly `allPhaseGe (p+1) n`. -/
theorem advanceMilestonePhase_post_imp_geFinished (p n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hPost : (advanceMilestonePhase (L := L) (K := K) p n hn).Post c) :
    geFinished (L := L) (K := K) p n c := by
  let i : Fin (advanceMilestonePhase (L := L) (K := K) p n hn).k :=
    ⟨n - 2, by change n - 2 < n - 1; omega⟩
  have hi := hPost i
  change advanceMilestone (L := L) (K := K) p n i.val c at hi
  unfold advanceMilestone at hi
  unfold geFinished
  change n ≤ geCount (L := L) (K := K) (p + 1) c
  have hival : i.val = n - 2 := rfl
  omega

/-- **Paper-scale seam drift.**  If the seam horizon dominates
`advanceJansonT = ⌈5·meanTime⌉ ≤ 11 n(log n+1)`, then the seam epidemic failure
probability is at most `1/n²`, from any partial start with at least one seed. -/
theorem advance_drift_janson (p n tseam : ℕ) (hn : 2 ≤ n)
    (hT : advanceJansonT (L := L) (K := K) p n hn ≤ tseam)
    (c : Config (AgentState L K))
    (hPre : allPhaseGe (L := L) (K := K) p n c ∧
      advTriggered (L := L) (K := K) (p + 1) c) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c
        {c' | ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
      ≤ ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) := by
  set mp := advanceMilestonePhase (L := L) (K := K) p n hn with hmp
  have hInv : mp.Inv c := by
    rw [hmp]
    exact ⟨hPre.1, (advTriggered_iff_geCount (L := L) (K := K) p c).mp hPre.2⟩
  have ht0 : (5 : ℝ) * mp.meanTime ≤
      (advanceJansonT (L := L) (K := K) p n hn : ℝ) := by
    rw [hmp]
    unfold advanceJansonT
    exact Nat.le_ceil _
  have ht : (5 : ℝ) * mp.meanTime ≤ (tseam : ℝ) := by
    exact le_trans ht0 (by exact_mod_cast hT)
  have hj := mp.milestone_hitting_time_bound_on_partial c hInv 5 (by norm_num) tseam ht
  have hexp := advance_janson_exp_le_inv_sq (L := L) (K := K) p n hn
  rw [← hmp] at hexp
  have htail :
      ((NonuniformMajority L K).transitionKernel ^ tseam) c {c' | ¬ mp.Post c'} ≤
        ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹) :=
    le_trans hj (ENNReal.ofReal_le_ofReal hexp)
  have hcard_zero :
      ((NonuniformMajority L K).transitionKernel ^ tseam) c
          {c' : Config (AgentState L K) | c'.card ≠ n} = 0 :=
    Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
      (NonuniformMajority L K) (fun c' : Config (AgentState L K) => c'.card = n)
      (fun c₀ c₁ hcard hsupp => by
        change c₁.card = n
        rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c₀ c₁ hsupp]
        exact hcard)
      c hPre.1.1 tseam
  have hsub :
      {c' : Config (AgentState L K) |
          ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
        ⊆ {c' | ¬ mp.Post c'} ∪ {c' | c'.card ≠ n} := by
    intro c' hbad
    by_cases hPost : mp.Post c'
    · right
      intro hcard
      apply hbad
      have hfin : geFinished (L := L) (K := K) p n c' := by
        rw [hmp] at hPost
        exact advanceMilestonePhase_post_imp_geFinished (L := L) (K := K) p n hn c' hPost
      exact (allPhaseGe_succ_iff_geFinished (L := L) (K := K) p n c' hcard).mpr hfin
    · left
      exact hPost
  calc ((NonuniformMajority L K).transitionKernel ^ tseam) c
          {c' | ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
      ≤ ((NonuniformMajority L K).transitionKernel ^ tseam) c
          ({c' | ¬ mp.Post c'} ∪ {c' | c'.card ≠ n}) := measure_mono hsub
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ tseam) c {c' | ¬ mp.Post c'} +
          ((NonuniformMajority L K).transitionKernel ^ tseam) c {c' | c'.card ≠ n} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹) := by
        rw [hcard_zero, add_zero]
        exact htail
    _ = ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) := by
        rw [show (((n : ℝ) ^ 2)⁻¹) = 1 / (n : ℝ) ^ 2 by ring, ENNReal.ofReal]

/-- Full `hDrift` field in the same abstract shape consumed downstream. -/
theorem advance_hDrift_janson (n : ℕ) (hn : 2 ≤ n)
    (seamP seamT : Fin 10 → ℕ)
    (hT : ∀ k, advanceJansonT (L := L) (K := K) (seamP k) n hn ≤ seamT k) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) :=
  fun k c hPre => advance_drift_janson (L := L) (K := K) (seamP k) n (seamT k) hn
    (hT k) c hPre

/-- Per-slot upper bound on the canonical seam horizon.  Thus choosing
`seamT k = advanceJansonT (seamP k) n hn` gives the paper-scale
`11·n·(log n+1)` seam window. -/
theorem advanceJansonT_all_le_logn (n : ℕ) (hn : 2 ≤ n) (seamP : Fin 10 → ℕ) :
    ∀ k : Fin 10,
      (advanceJansonT (L := L) (K := K) (seamP k) n hn : ℝ) ≤
        11 * (n : ℝ) * (Real.log n + 1) :=
  fun k => advanceJansonT_le_logn (L := L) (K := K) (seamP k) n hn

/-! ## Axiom audit -/

#print axioms RoleSplitConcentration.MilestonePhaseOn.milestone_hitting_time_bound_on_partial
#print axioms advanceMilestonePhase
#print axioms advance_drift_janson
#print axioms advance_hDrift_janson
#print axioms advanceJansonT_le_logn

end AdvanceJansonDrift

end Ripple.PopulationProtocol.ExactMajority

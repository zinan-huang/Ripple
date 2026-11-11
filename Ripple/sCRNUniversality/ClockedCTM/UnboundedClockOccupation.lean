import Ripple.sCRNUniversality.ClockedCTM.UnboundedRestart
import Ripple.sCRNUniversality.ClockedCTM.UnboundedMarkov

/-!
# Actual clock occupation and sharp active-window volume for SCWB T41

The original-law transfer uses the explicitly named raw-state restart input.
The terminal stopped potential and the pathwise volume estimate do not use it.
The final XCTM and TM corollaries discharge the phase and restart inputs using
UnboundedMarkov.
-/

noncomputable section

namespace Ripple.sCRNUniversality.Stochastic.MassAction

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

universe u v

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

/-- The prefix-continuation identity for an arbitrary nonnegative reward. -/
theorem rawLaw_prefix_reward
    (hPos : N.hasPositiveRates) (z₀ : State S) (cut : ℕ)
    (A : Set ((i : Finset.Iic cut) → Option N.I))
    (F : (ℕ → Option N.I) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω in {ω | frestrictLe cut ω ∈ A}, F ω ∂rawLaw N hPos z₀) =
      ∫⁻ p in A, ∫⁻ ω, F ω
        ∂Kernel.traj (X := fun _ => Option N.I)
          (fun j => stepKernel N hPos z₀ j) cut p
        ∂Kernel.partialTraj (X := fun _ => Option N.I)
          (fun j => stepKernel N hPos z₀ j) 0 cut (fun _ => none) := by
  let κ := fun j => stepKernel N hPos z₀ j
  let ν := Kernel.partialTraj (X := fun _ => Option N.I) κ 0 cut (fun _ => none)
  have heq :
      (rawLaw N hPos z₀).restrict {ω | frestrictLe cut ω ∈ A} =
        (ν.restrict A).bind
          (Kernel.traj (X := fun _ => Option N.I) κ cut) := by
    apply Measure.ext
    intro B hB
    rw [Measure.restrict_apply hB,
      Measure.bind_apply hB (Kernel.aemeasurable _), Set.inter_comm]
    exact rawLaw_prefix_continuation N hPos z₀ cut A B hB
  rw [heq, Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable]

/-- A uniform fresh reward bound transfers through disjoint finite entry
slices. No almost-sure finiteness of an entry time is required. -/
theorem rawLaw_stopped_prefix_reward_le_of_restart
    (hPos : N.hasPositiveRates) (z₀ : State S)
    {ι : Type*} [Countable ι] (cut : ι → ℕ)
    (A : (i : ι) → Set ((j : Finset.Iic (cut i)) → Option N.I))
    (start : ι → State S)
    (F : ι → (ℕ → Option N.I) → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i))
    (hdisjoint : Pairwise (Function.onFun Disjoint
      (fun i => {ω : ℕ → Option N.I | frestrictLe (cut i) ω ∈ A i})))
    (hRestart : ∀ i p, p ∈ A i →
      (Kernel.traj (X := fun _ => Option N.I)
        (fun j => stepKernel N hPos z₀ j) (cut i) p).map
          (restartLabels N (cut i)) = rawLaw N hPos (start i))
    (B : ℝ≥0∞)
    (hFresh : ∀ i p, p ∈ A i →
      (∫⁻ ω, F i ω ∂rawLaw N hPos (start i)) ≤ B) :
    (∫⁻ ω, ∑' i,
      ({ω | frestrictLe (cut i) ω ∈ A i} : Set (ℕ → Option N.I)).indicator
        (fun ω => F i (restartLabels N (cut i) ω)) ω
      ∂rawLaw N hPos z₀) ≤ B := by
  classical
  letI := rawLaw_isProbabilityMeasure N hPos z₀
  have hA i : MeasurableSet
      {ω : ℕ → Option N.I | frestrictLe (cut i) ω ∈ A i} :=
    (measurable_frestrictLe (cut i))
      (measurableSet_prefixSet N (cut i) (A i))
  have hG (i : ι) :
      AEMeasurable
        (({ω : ℕ → Option N.I | frestrictLe (cut i) ω ∈ A i}).indicator
          (fun ω => F i (restartLabels N (cut i) ω)))
        (rawLaw N hPos z₀) := by
    exact (((hF i).comp (measurable_restartLabels N (cut i))).indicator
      (hA i)).aemeasurable
  rw [lintegral_tsum hG]
  calc
    _ ≤ ∑' i, B * rawLaw N hPos z₀
        {ω | frestrictLe (cut i) ω ∈ A i} := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [lintegral_indicator (hA i),
        rawLaw_prefix_reward N hPos z₀ (cut i) (A i)
          (fun ω => F i (restartLabels N (cut i) ω))
          ((hF i).comp (measurable_restartLabels N (cut i)))]
      calc
        _ ≤ ∫⁻ _p in A i, B
            ∂Kernel.partialTraj (X := fun _ => Option N.I)
              (fun j => stepKernel N hPos z₀ j) 0 (cut i) (fun _ => none) := by
          apply setLIntegral_mono' (measurableSet_prefixSet N (cut i) (A i))
          intro p hp
          rw [← lintegral_map (hF i) (measurable_restartLabels N (cut i)),
            hRestart i p hp]
          exact hFresh i p hp
        _ = _ := by
          rw [lintegral_const, Measure.restrict_apply_univ,
            rawLaw_prefix_eq N hPos z₀ (cut i) (A i)]
    _ = B * rawLaw N hPos z₀
        (⋃ i, {ω | frestrictLe (cut i) ω ∈ A i}) := by
      rw [ENNReal.tsum_mul_left, measure_iUnion hdisjoint hA]
    _ ≤ B * 1 := mul_le_mul_left' prob_le_one B
    _ = B := mul_one B

end Ripple.sCRNUniversality.Stochastic.MassAction


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Classical

variable {Q : Type} [Fintype Q] [DecidableEq Q]

namespace WindowAnalysis

/-- The erased state associated to an arbitrary full state. -/
def occupationWorkView (C : XCTM Q) (z : State (Sp C)) : ClocklessState C :=
  ⟨workView C z, by funext s; cases s <;> rfl⟩

/-- Clock conservation gives an actual inserted-clock representation. -/
theorem exists_clockInsert_of_count_one (C : XCTM Q) (z : State (Sp C))
    (hz : clockMoleculeCount C z = 1) :
    ∃ c : Fin 5, z = clockInsert C (occupationWorkView C z) c := by
  have hsum :
      z (.clock 0) + z (.clock 1) + z (.clock 2) +
        z (.clock 3) + z (.clock 4) = 1 := by
    simpa [clockMoleculeCount, Fin.sum_univ_succ, add_assoc] using hz
  have hex : ∃ c : Fin 5, z (.clock c) = 1 := by
    have h : z (.clock 0) = 1 ∨ z (.clock 1) = 1 ∨
        z (.clock 2) = 1 ∨ z (.clock 3) = 1 ∨ z (.clock 4) = 1 := by omega
    rcases h with h | h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  obtain ⟨c, hc⟩ := hex
  have hclock : ∀ d : Fin 5, z (.clock d) = if d = c then 1 else 0 := by
    intro d
    by_cases hd : d = c
    · simpa [hd] using hc
    · rw [if_neg hd]
      have hpair : z (.clock c) + z (.clock d) ≤ clockMoleculeCount C z := by
        calc
          z (.clock c) + z (.clock d) =
              ∑ i ∈ ({c, d} : Finset (Fin 5)), z (.clock i) :=
            (Finset.sum_pair (f := fun i => z (.clock i)) (Ne.symm hd)).symm
          _ ≤ ∑ i : Fin 5, z (.clock i) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => Nat.zero_le (z (.clock i)))
      rw [hz, hc] at hpair
      omega
  refine ⟨c, ?_⟩
  funext s
  cases s with
  | clock d => rw [clockInsert_clock]; exact hclock d
  | _ => simp [clockInsert, occupationWorkView, workView, unit]

end WindowAnalysis

namespace TimeAnalysis

open WindowAnalysis

/-- Unit cost up to, but excluding the state after, the first tick. -/
noncomputable def firstWindowUnitCost (C : XCTM Q) (z₀ : State (Sp C)) :
    LabelPath C → ℝ≥0∞ :=
  maskedUnitCost C z₀ (fun j ω => tickCount C z₀ ω j = 0)

noncomputable def firstWindowUnitMean (C : XCTM Q) (z₀ : State (Sp C)) : ℝ≥0∞ :=
  ∫⁻ ω, firstWindowUnitCost C z₀ ω ∂windowLaw C z₀

noncomputable def firstWindowWorkCost (C : XCTM Q) (z₀ : State (Sp C)) :
    LabelPath C → ℝ≥0∞ :=
  maskedUnitCost C z₀ (fun j ω => tickCount C z₀ ω j = 0 ∧
    ¬ WorkTerminal C (pathState (net C) z₀ ω j))

noncomputable def firstWindowWorkMean (C : XCTM Q) (z₀ : State (Sp C)) : ℝ≥0∞ :=
  ∫⁻ ω, firstWindowWorkCost C z₀ ω ∂windowLaw C z₀

noncomputable def firstWindowTerminalCost (C : XCTM Q) (z₀ : State (Sp C)) :
    LabelPath C → ℝ≥0∞ :=
  maskedUnitCost C z₀ (fun j ω => tickCount C z₀ ω j = 0 ∧
    WorkTerminal C (pathState (net C) z₀ ω j))

noncomputable def firstWindowTerminalMean (C : XCTM Q) (z₀ : State (Sp C)) : ℝ≥0∞ :=
  ∫⁻ ω, firstWindowTerminalCost C z₀ ω ∂windowLaw C z₀

theorem measurableSet_workTerminal_at (C : XCTM Q) (z₀ : State (Sp C)) (j : ℕ) :
    MeasurableSet {ω | WorkTerminal C (pathState (net C) z₀ ω j)} := by
  have hm : Measurable (fun ω : LabelPath C =>
      pathState (net C) z₀ ω j) := by
    apply measurable_of_frestrictLe (net C) j
    intro ω ω' h
    rw [← prefixToState_eq_pathState (net C) z₀ ω j,
      ← prefixToState_eq_pathState (net C) z₀ ω' j]
    exact congrArg (prefixToState (net C) z₀ j) h
  exact hm (Set.to_countable {z : State (Sp C) | WorkTerminal C z}).measurableSet

theorem measurable_firstWindowUnitCost (C : XCTM Q) (z₀ : State (Sp C)) :
    Measurable (firstWindowUnitCost C z₀) :=
  measurable_maskedUnitCost C z₀ _ (fun j =>
    measurableSet_eq_fun (measurable_tickCount C z₀ j) measurable_const)

theorem measurable_firstWindowWorkCost (C : XCTM Q) (z₀ : State (Sp C)) :
    Measurable (firstWindowWorkCost C z₀) :=
  measurable_maskedUnitCost C z₀ _ (fun j =>
    (measurableSet_eq_fun (measurable_tickCount C z₀ j) measurable_const).inter
      (measurableSet_workTerminal_at C z₀ j).compl)

theorem measurable_firstWindowTerminalCost (C : XCTM Q) (z₀ : State (Sp C)) :
    Measurable (firstWindowTerminalCost C z₀) :=
  measurable_maskedUnitCost C z₀ _ (fun j =>
    (measurableSet_eq_fun (measurable_tickCount C z₀ j) measurable_const).inter
      (measurableSet_workTerminal_at C z₀ j))

theorem firstWindowUnitCost_split (C : XCTM Q) (z₀ : State (Sp C)) (ω : LabelPath C) :
    firstWindowUnitCost C z₀ ω =
      firstWindowWorkCost C z₀ ω + firstWindowTerminalCost C z₀ ω := by
  unfold firstWindowUnitCost firstWindowWorkCost firstWindowTerminalCost maskedUnitCost
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro j
  by_cases hzero : tickCount C z₀ ω j = 0 <;>
    by_cases ht : WorkTerminal C (pathState (net C) z₀ ω j) <;> simp [hzero, ht]

theorem firstWindowUnitMean_split (C : XCTM Q) (z₀ : State (Sp C)) :
    firstWindowUnitMean C z₀ =
      firstWindowWorkMean C z₀ + firstWindowTerminalMean C z₀ := by
  simp only [firstWindowUnitMean, firstWindowUnitCost_split,
    firstWindowWorkMean, firstWindowTerminalMean]
  exact lintegral_add_left (measurable_firstWindowWorkCost C z₀) _

/-- The nonterminal part of the actual first-window reward is charged to
the standalone work law, using the already-proved occupation comparison. -/
theorem firstWindowWorkMean_le_meanDuration (C : XCTM Q)
    (x₀ : ClocklessState C) (c₀ : Fin 5) :
    firstWindowWorkMean C (clockInsert C x₀ c₀) ≤
      StandaloneWork.meanDuration C x₀.val := by
  let z₀ := clockInsert C x₀ c₀
  let H : ClocklessState C → Fin 5 → ℝ≥0∞ := fun x c =>
    if WorkTerminal C x.val then 0
    else ((net C).totalPropensity (clockInsert C x c) : ℝ≥0∞)⁻¹
  let R : ℕ → ℕ → ClocklessState C → Fin 5 → LabelPath C → ℝ≥0∞ :=
    fun n j x c => (windowEvent C z₀ n j (clockInsert C x c)).indicator
      (fun _ => H x c)
  have hR n j x c : Measurable (R n j x c) :=
    measurable_const.indicator (measurableSet_windowEvent C z₀ n j _)
  have hpoint : ∀ ω : LabelPath C,
      firstWindowWorkCost C z₀ ω ≤
        ∑' n : ℕ, ∑' j : ℕ, ∑' x : ClocklessState C, ∑' c : Fin 5,
          R n j x c ω := by
    intro ω
    apply ENNReal.tsum_le_tsum
    intro n
    by_cases ha : tickCount C z₀ ω n = 0 ∧
        ¬ WorkTerminal C (pathState (net C) z₀ ω n)
    · rw [if_pos ha]
      obtain ⟨c, hc⟩ := exists_clockInsert_of_count_one C
        (pathState (net C) z₀ ω n)
        ((clockMoleculeCount_path C z₀ ω n).trans
          (clockMoleculeCount_clockInsert C x₀ c₀))
      let x := occupationWorkView C (pathState (net C) z₀ ω n)
      have hx : ¬ WorkTerminal C x.val := by
        intro ht
        apply ha.2
        rw [hc]
        exact (workTerminal_clockInsert C x c).mpr ht
      have hE : ω ∈ windowEvent C z₀ n (windowCount C z₀ n ω)
          (clockInsert C x c) :=
        (windowEvent_iff C z₀ n _ _ ω).mpr ⟨rfl, ha.1, hc⟩
      calc
        CTMCBridge.meanHolding (net C) z₀ n ω =
            R n (windowCount C z₀ n ω) x c ω := by
          simp only [R, Set.indicator_of_mem hE, H, if_neg hx]
          change ((net C).totalPropensity (pathState (net C) z₀ ω n) : ℝ≥0∞)⁻¹ = _
          rw [hc]
        _ ≤ ∑' d : Fin 5, R n (windowCount C z₀ n ω) x d ω :=
          ENNReal.le_tsum c
        _ ≤ ∑' y : ClocklessState C, ∑' d : Fin 5,
            R n (windowCount C z₀ n ω) y d ω := ENNReal.le_tsum x
        _ ≤ _ := ENNReal.le_tsum (windowCount C z₀ n ω)
    · rw [if_neg ha]
      exact bot_le
  have hint n j x c :
      (∫⁻ ω, R n j x c ω ∂windowLaw C z₀) =
        windowLaw C z₀ (windowEvent C z₀ n j (clockInsert C x c)) * H x c := by
    rw [lintegral_indicator_const (measurableSet_windowEvent C z₀ n j _)]
    exact mul_comm _ _
  calc
    firstWindowWorkMean C z₀ ≤
        ∫⁻ ω, ∑' n : ℕ, ∑' j : ℕ, ∑' x : ClocklessState C, ∑' c : Fin 5,
          R n j x c ω ∂windowLaw C z₀ := lintegral_mono hpoint
    _ = ∑' n : ℕ, ∑' j : ℕ, ∑' x : ClocklessState C, ∑' c : Fin 5,
        windowLaw C z₀ (windowEvent C z₀ n j (clockInsert C x c)) * H x c := by
      rw [lintegral_tsum (fun n =>
        (Measurable.tsum fun j => Measurable.tsum fun x =>
          Measurable.tsum fun c => hR n j x c).aemeasurable)]
      apply tsum_congr
      intro n
      rw [lintegral_tsum (fun j =>
        (Measurable.tsum fun x => Measurable.tsum fun c => hR n j x c).aemeasurable)]
      apply tsum_congr
      intro j
      rw [lintegral_tsum (fun x =>
        (Measurable.tsum fun c => hR n j x c).aemeasurable)]
      apply tsum_congr
      intro x
      rw [lintegral_tsum (fun c => (hR n j x c).aemeasurable)]
      exact tsum_congr (hint n j x)
    _ = ∑' j : ℕ, ∑' x : ClocklessState C,
        if WorkTerminal C x.val then 0 else windowOccupationTotal C z₀ j x := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro j
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro x
      rw [ENNReal.tsum_comm]
      by_cases ht : WorkTerminal C x.val
      · simp [H, ht]
      · simp only [H, if_neg ht]
        simp_rw [ENNReal.tsum_mul_right]
        rw [tsum_fintype]
        rfl
    _ ≤ StandaloneWork.meanDuration C x₀.val :=
      windowOccupation_nonterminal_sum_le_meanDuration C x₀ c₀

end TimeAnalysis
end Ripple.sCRNUniversality.ClockedCTM.Unbounded



namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded.TimeAnalysis

open Stochastic Stochastic.MassAction WindowAnalysis MeasureTheory ProbabilityTheory Classical
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

private def clockTotalRate (C : XCTM Q) (z : State (Sp C)) : ℕ :=
  ∑ r : Rx C, rate C r z

private theorem clockTotalRate_propensity (C : XCTM Q) (z : State (Sp C)) :
    (net C).totalPropensity z = (clockTotalRate C z : Rate) := by
  change (∑ r : Rx C, (rxn C r).propensity z) = _
  simp_rw [propensity_rxn]
  change (∑ r : Rx C, (rate C r z : Rate)) = _
  rw [clockTotalRate, Nat.cast_sum]

private theorem clockTotalRate_pos (C : XCTM Q) (z : State (Sp C))
    (hT : ¬ (net C).Terminal z) : 0 < clockTotalRate C z := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : Rx C, (rxn C r).enabled z := by
    by_contra h
    apply hT
    intro r hr
    exact h ⟨r, hr⟩
  change 0 < ∑ r : Rx C, rate C r z
  exact (Nat.pos_of_ne_zero ((enabled_iff C r z).mp hr)).trans_le
    (Finset.single_le_sum (fun r _ => Nat.zero_le (rate C r z))
      (Finset.mem_univ r))

private theorem clockTotalRate_insert (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) :
    clockTotalRate C (clockInsert C x c) =
      StandaloneWork.totalWorkRate C x.val + backwardCount C x.val +
        (if c.val + 1 < 5 then forwardCount C x.val else 0) := by
  have h := totalPropensity_clockInsert C x c
  rw [clockTotalRate_propensity] at h
  exact_mod_cast h

private theorem clock_pmf_none (C : XCTM Q) (z : State (Sp C))
    (hT : ¬ (net C).Terminal z) :
    massActionPMF (net C) (net_hasPositiveRates C) z none = 0 := by
  change massActionWeight (net C) (net_hasPositiveRates C) z none = 0
  simp only [massActionWeight, dif_neg hT]

private theorem clock_pmf_some (C : XCTM Q) (z : State (Sp C))
    (hT : ¬ (net C).Terminal z) (r : Rx C) :
    massActionPMF (net C) (net_hasPositiveRates C) z (some r) =
      (rate C r z : ℝ≥0∞) / (clockTotalRate C z : ℝ≥0∞) := by
  have hB : (clockTotalRate C z : NNReal) ≠ 0 := by
    exact_mod_cast (clockTotalRate_pos C z hT).ne'
  change massActionWeight (net C) (net_hasPositiveRates C) z (some r) = _
  simp only [massActionWeight, dif_neg hT]
  rw [jumpProbAt, show (net C).rxn r = rxn C r from rfl,
    propensity_rxn, clockTotalRate_propensity, ← ENNReal.coe_nnratCast,
    NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    ENNReal.coe_div hB, ENNReal.coe_natCast, ENNReal.coe_natCast]
  rfl

private theorem clock_drift_real (C : XCTM Q) (z : State (Sp C))
    (hT : ¬ (net C).Terminal z) {cost : ℝ≥0∞}
    {Pn : Option (Rx C) → ℝ≥0∞} {p c : ℝ} {pn : Rx C → ℝ}
    (hcost : cost = ENNReal.ofReal c / (clockTotalRate C z : ℝ≥0∞))
    (hc : 0 ≤ c)
    (hPn : ∀ r, rate C r z ≠ 0 → Pn (some r) ≤ ENNReal.ofReal (pn r))
    (hpn : ∀ r, 0 ≤ pn r)
    (h : c + ∑ r : Rx C, (rate C r z : ℝ) * (pn r - p) ≤ 0) :
    cost + ∑ o : Option (Rx C),
      massActionPMF (net C) (net_hasPositiveRates C) z o * Pn o ≤
        ENNReal.ofReal p := by
  have hB : (0 : ℝ) < clockTotalRate C z := by
    exact_mod_cast clockTotalRate_pos C z hT
  rw [Fintype.sum_option]
  have hnone :
      massActionPMF (net C) (net_hasPositiveRates C) z
        (none : Option (Rx C)) = 0 :=
    clock_pmf_none C z hT
  rw [hnone, zero_mul, zero_add]
  have hterm : ∀ r : Rx C,
      massActionPMF (net C) (net_hasPositiveRates C) z (some r) * Pn (some r) ≤
        ENNReal.ofReal ((rate C r z : ℝ) * pn r / clockTotalRate C z) := by
    intro r
    rw [clock_pmf_some C z hT r]
    by_cases hr : rate C r z = 0
    · simp [hr]
    · calc
        (rate C r z : ℝ≥0∞) / (clockTotalRate C z : ℝ≥0∞) * Pn (some r) ≤
            (rate C r z : ℝ≥0∞) / (clockTotalRate C z : ℝ≥0∞) *
              ENNReal.ofReal (pn r) := by
                gcongr
                exact hPn r hr
        _ = ENNReal.ofReal ((rate C r z : ℝ) * pn r / clockTotalRate C z) := by
          rw [ENNReal.ofReal_div_of_pos hB, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
          simp only [div_eq_mul_inv]
          ring
  have hnn : ∀ r : Rx C, 0 ≤ (rate C r z : ℝ) * pn r / clockTotalRate C z :=
    fun r => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpn r)) hB.le
  calc
    cost + ∑ r : Rx C,
        massActionPMF (net C) (net_hasPositiveRates C) z (some r) * Pn (some r)
        ≤ ENNReal.ofReal (c / clockTotalRate C z) +
          ∑ r : Rx C,
            ENNReal.ofReal ((rate C r z : ℝ) * pn r / clockTotalRate C z) := by
          rw [hcost, ENNReal.ofReal_div_of_pos hB, ENNReal.ofReal_natCast]
          gcongr with r
          exact hterm r
    _ = ENNReal.ofReal (c / clockTotalRate C z +
        ∑ r : Rx C, (rate C r z : ℝ) * pn r / clockTotalRate C z) := by
      rw [ENNReal.ofReal_add (div_nonneg hc hB.le)
        (Finset.sum_nonneg fun r _ => hnn r),
        ENNReal.ofReal_sum_of_nonneg fun r _ => hnn r]
    _ ≤ ENNReal.ofReal p := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.sum_div, ← add_div, div_le_iff₀ hB]
      have hsum :
          (∑ r : Rx C, (rate C r z : ℝ) * pn r) =
            (∑ r : Rx C, (rate C r z : ℝ) * (pn r - p)) +
              (clockTotalRate C z : ℝ) * p := by
        rw [clockTotalRate, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [hsum]
      linarith

private def stoppedClockPosition (C : XCTM Q) (c : Fin 5) : Rx C → Fin 5
  | .tick _ => Fin.last 4
  | .up i _ => i.succ
  | .down i _ => i.castSucc
  | _ => c

private noncomputable def stoppedClockUpdate (C : XCTM Q)
    (a : Bool × Fin 5) (z : State (Sp C)) (o : Option (Rx C)) : Bool × Fin 5 :=
  match windowLabel C z o with
  | none => a
  | some r => (a.1 && !(isTick r), stoppedClockPosition C a.2 r)

private theorem stoppedClockUpdate_dead (C : XCTM Q)
    (c : Fin 5) (z : State (Sp C)) (o : Option (Rx C)) :
    (stoppedClockUpdate C (false, c) z o).1 = false := by
  unfold stoppedClockUpdate
  split <;> simp

private theorem stoppedClockUpdate_enabled (C : XCTM Q)
    (a : Bool × Fin 5) (z : State (Sp C)) (r : Rx C)
    (he : (rxn C r).enabled z) :
    stoppedClockUpdate C a z (some r) =
      (a.1 && !(isTick r), stoppedClockPosition C a.2 r) := by
  simp only [stoppedClockUpdate, windowLabel_of_enabled C z r he]

private theorem clock_stateStep_enabled (C : XCTM Q)
    (z : State (Sp C)) (r : Rx C) (he : (rxn C r).enabled z) :
    stateStep (net C) z (some r) = (rxn C r).fire z := by
  have hT : ¬ (net C).Terminal z := fun h => h r he
  rw [stateStep, dif_neg hT, fireOptionSanitized_of_enabled (net C) z r hT he]
  rfl

private theorem clock_work_fire_insert (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) (r : Rx C) (hr : isClock r = false) :
    (rxn C r).fire (clockInsert C x c) =
      clockInsert C (workSuccessor C x ⟨r, hr⟩) c := by
  have hclock (d : Fin 5) :
      (rxn C r).fire (clockInsert C x c) (.clock d) =
        clockInsert C x c (.clock d) := by
    cases r <;>
      simp_all [isClock, fire_apply, sourceLeft, sourceRight, products,
        unit, Pi.add_apply, Pi.smul_apply]
  have hv :
      workView C ((rxn C r).fire (clockInsert C x c)) =
        workView C (clockInsert C (workSuccessor C x ⟨r, hr⟩) c) := by
    rw [work_fire_view C r _ hr, clockInsert_workView, clockInsert_workView]
    rfl
  funext s
  have hs := congrFun hv s
  cases s with
  | clock d => rw [hclock d, clockInsert_clock, clockInsert_clock]
  | _ => simpa only [workView] using hs


private theorem clock_move_fire_insert (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) (r : Rx C)
    (hc : isClock r = true) (ht : isTick r = false)
    (he : (rxn C r).enabled (clockInsert C x c)) :
    (rxn C r).fire (clockInsert C x c) =
      clockInsert C x (stoppedClockPosition C c r) := by
  have hp := (enabled_iff C r (clockInsert C x c)).mp he
  cases r with
  | up i latent =>
      have hsource : i.castSucc = c := by
        by_contra h
        apply hp
        cases latent <;>
          simp [rate, sourceLeft, sourceRight, clockInsert, unit,
            clockless_clock_zero, h]
      subst c
      cases latent <;>
        simp only [rate, sourceLeft, sourceRight] at hp
      all_goals
        simp [clockInsert, unit, clockless_clock_zero] at hp
        funext s
        cases s <;>
          simp [stoppedClockPosition, clockInsert, fire_apply,
            sourceLeft, sourceRight, products, unit, clockless_clock_zero,
            Pi.add_apply, Pi.smul_apply] <;> omega
  | down i latent =>
      have hsource : i.succ = c := by
        by_contra h
        apply hp
        cases latent <;>
          simp [rate, sourceLeft, sourceRight, clockInsert, unit,
            clockless_clock_zero, h]
      subst c
      cases latent <;>
        simp only [rate, sourceLeft, sourceRight] at hp
      all_goals
        simp [clockInsert, unit, clockless_clock_zero] at hp
        funext s
        cases s <;>
          simp [stoppedClockPosition, clockInsert, fire_apply,
            sourceLeft, sourceRight, products, unit, clockless_clock_zero,
            Pi.add_apply, Pi.smul_apply] <;> omega
  | _ => simp_all [isClock, isTick]

private abbrev TerminalClockChannel := Bool × (Fin 4 × Bool)

private def terminalClockRx (C : XCTM Q) (p : TerminalClockChannel) : Rx C :=
  if p.1 then .up p.2.1 p.2.2 else .down p.2.1 p.2.2

private def terminalReactionEquiv (C : XCTM Q) :
    (WorkLabel C ⊕ (Bool ⊕ TerminalClockChannel)) ≃ Rx C where
  toFun
    | .inl r => r.val
    | .inr (.inl b) => .tick b
    | .inr (.inr p) => terminalClockRx C p
  invFun r :=
    if h : isClock r = false then .inl ⟨r, h⟩ else
      match r with
      | .tick b => .inr (.inl b)
      | .up i b => .inr (.inr (true, i, b))
      | .down i b => .inr (.inr (false, i, b))
      | _ => .inr (.inl false)
  left_inv := by
    intro u
    rcases u with r | (b | ⟨b, i, latent⟩)
    · simp [r.property]
    · simp [isClock]
    · cases b <;> simp [terminalClockRx, isClock]
  right_inv := by
    intro r
    cases r <;> simp [isClock, terminalClockRx]

private theorem terminal_clock_sum (C : XCTM Q) (F : Rx C → ℝ)
    (hwork : ∀ r, isClock r = false → F r = 0) :
    (∑ r : Rx C, F r) =
      (∑ b : Bool, F (.tick b)) +
        (∑ i : Fin 4, ∑ b : Bool, F (.up i b)) +
        (∑ i : Fin 4, ∑ b : Bool, F (.down i b)) := by
  calc
    (∑ r : Rx C, F r) =
        ∑ u : WorkLabel C ⊕ (Bool ⊕ TerminalClockChannel),
          F ((terminalReactionEquiv C) u) :=
      ((terminalReactionEquiv C).sum_comp F).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type]
      have hw : (∑ r : WorkLabel C, F r.val) = 0 :=
        Finset.sum_eq_zero fun r _ => hwork r.val r.property
      change (∑ r : WorkLabel C, F r.val) +
        ((∑ b : Bool, F (.tick b)) +
          ∑ p : TerminalClockChannel, F (terminalClockRx C p)) = _
      rw [hw, zero_add]
      simp [Fintype.sum_prod_type, Fintype.sum_bool, terminalClockRx, add_assoc,
        add_comm, add_left_comm]

private noncomputable def terminalClockNextValue (C : XCTM Q)
    (a f : ℝ) : Rx C → ℝ
  | .tick _ => 0
  | .up i _ => tickWait (a / f) f (i.val + 2)
  | .down i _ => tickWait (a / f) f (i.val + 1)
  | _ => 0

private theorem terminalClockNextValue_nonneg (C : XCTM Q)
    {a f : ℝ} (ha : 0 ≤ a) (hf : 0 < f) (r : Rx C) :
    0 ≤ terminalClockNextValue C a f r := by
  cases r <;>
    simp only [terminalClockNextValue] <;>
    first | exact le_rfl | exact tickWait_nonneg (div_nonneg ha hf.le) hf _

private theorem terminal_clock_generator (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) (ht : WorkTerminal C x.val)
    (p : ℝ) :
    (∑ r : Rx C, (rate C r (clockInsert C x c) : ℝ) *
      (terminalClockNextValue C (forwardCount C x.val) (backwardCount C x.val) r - p)) =
      (if c.val = 0 then (backwardCount C x.val : ℝ) * (0 - p) else 0) +
      (if c.val + 1 < 5 then (forwardCount C x.val : ℝ) *
        (tickWait ((forwardCount C x.val : ℝ) / backwardCount C x.val)
          (backwardCount C x.val) (c.val + 2) - p) else 0) +
      (if 0 < c.val then (backwardCount C x.val : ℝ) *
        (tickWait ((forwardCount C x.val : ℝ) / backwardCount C x.val)
          (backwardCount C x.val) c.val - p) else 0) := by
  rw [terminal_clock_sum C _ (by
    intro r hr
    rw [work_rate_clockInsert C x c r hr,
      (workTerminal_iff C x.val).mp ht r hr, Nat.cast_zero, zero_mul])]
  fin_cases c <;>
    simp [Fintype.sum_bool, Fin.sum_univ_succ, terminalClockNextValue,
      rate, sourceLeft, sourceRight, clockInsert, unit, clockless_clock_zero,
      forwardCount, backwardCount, Nat.cast_add] <;> ring

private theorem terminal_clock_generator_eq_neg_one (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5) (ht : WorkTerminal C x.val)
    (hf : 0 < backwardCount C x.val) :
    (∑ r : Rx C, (rate C r (clockInsert C x c) : ℝ) *
      (terminalClockNextValue C (forwardCount C x.val) (backwardCount C x.val) r -
        tickWait ((forwardCount C x.val : ℝ) / backwardCount C x.val)
          (backwardCount C x.val) (c.val + 1))) = -1 := by
  have hfr : (backwardCount C x.val : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  rw [terminal_clock_generator C x c ht]
  have hrec (j : ℕ) (hj : 1 ≤ j) (hjlast : j < 5) :=
    tickWait_backward (r := (forwardCount C x.val : ℝ) / backwardCount C x.val)
      (f := (backwardCount C x.val : ℝ)) hfr hj hjlast
  have hlast := tickWait_reflecting
    (r := (forwardCount C x.val : ℝ) / backwardCount C x.val)
    (f := (backwardCount C x.val : ℝ)) hfr
  simp only [div_mul_cancel₀ _ hfr] at hrec
  fin_cases c
  · have h := hrec 1 (by norm_num) (by norm_num)
    norm_num [tickWait_zero] at h ⊢
    linarith
  · have h := hrec 2 (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  · have h := hrec 3 (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  · have h := hrec 4 (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  · norm_num at hlast ⊢
    linarith


private def terminalClockGuard (C : XCTM Q)
    {start target : ClocklessState C} (P : WorkCertificate C start.val target.val)
    (c : Fin 5) (z : State (Sp C)) : Prop :=
  ∃ x : ClocklessState C, P.inv x.val ∧ z = clockInsert C x c

private theorem terminalClockGuard_fire (C : XCTM Q)
    {start target : ClocklessState C} (P : WorkCertificate C start.val target.val)
    (c : Fin 5) (z : State (Sp C)) (hg : terminalClockGuard C P c z)
    (r : Rx C) (he : (rxn C r).enabled z) (ht : isTick r = false) :
    terminalClockGuard C P (stoppedClockPosition C c r) ((rxn C r).fire z) := by
  rcases hg with ⟨x, hx, rfl⟩
  cases hc : isClock r with
  | false =>
      have he' : (rxn C r).enabled x.val := by
        have h := (work_enabled_view C r (clockInsert C x c) hc).mpr he
        simpa only [clockInsert_workView] using h
      refine ⟨workSuccessor C x ⟨r, hc⟩, ?_, ?_⟩
      · exact P.closed x.val _ hx ⟨r, hc, he', rfl⟩
      · rw [clock_work_fire_insert C x c r hc]
        have hp : stoppedClockPosition C c r = c := by
          cases r <;> simp_all [isClock, stoppedClockPosition]
        rw [hp]
  | true =>
      exact ⟨x, hx, clock_move_fire_insert C x c r hc ht he⟩

private theorem terminalClockGuard_target (C : XCTM Q)
    {start target : ClocklessState C} (P : WorkCertificate C start.val target.val)
    (c : Fin 5) (z : State (Sp C)) (hg : terminalClockGuard C P c z)
    (ht : WorkTerminal C z) :
    z = clockInsert C target c := by
  rcases hg with ⟨x, hx, rfl⟩
  have ht' := (workTerminal_clockInsert C x c).mp ht
  have he : x.val = target.val := x.property.symm.trans (P.terminal _ hx ht')
  have hx' : x = target := Subtype.ext he
  rw [hx']

private theorem terminal_insert_nonterminal (C : XCTM Q)
    (x : ClocklessState C) (c : Fin 5)
    (hx : WorkTerminal C x.val) (hf : 0 < backwardCount C x.val) :
    ¬ (net C).Terminal (clockInsert C x c) := by
  intro ht
  have hz : clockTotalRate C (clockInsert C x c) = 0 := by
    unfold clockTotalRate
    apply Finset.sum_eq_zero
    intro r _
    by_contra hr
    exact ht r ((enabled_iff C r _).mpr hr)
  rw [clockTotalRate_insert, totalWorkRate_eq_zero_of_terminal C x.val hx] at hz
  omega

private noncomputable def stoppedTerminalPotential (C : XCTM Q)
    {start target : ClocklessState C} (P : WorkCertificate C start.val target.val)
    (y : (Bool × Fin 5) × State (Sp C)) : ℝ≥0∞ :=
  if y.1.1 then
    if terminalClockGuard C P y.1.2 y.2 then
      if WorkTerminal C y.2 then
        ENNReal.ofReal
          (tickWait ((forwardCount C target.val : ℝ) / backwardCount C target.val)
            (backwardCount C target.val) (y.1.2.val + 1))
      else
        ENNReal.ofReal
          (tickWait ((forwardCount C target.val : ℝ) / backwardCount C target.val)
            (backwardCount C target.val) 5)
    else ⊤
  else 0

private noncomputable def stoppedTerminalCost (C : XCTM Q)
    (y : (Bool × Fin 5) × State (Sp C)) : ℝ≥0∞ :=
  if y.1.1 = true ∧ WorkTerminal C y.2 then
    ((net C).totalPropensity y.2 : ℝ≥0∞)⁻¹
  else 0

private theorem stoppedTerminalPotential_le_top (C : XCTM Q)
    {start target : ClocklessState C} (P : WorkCertificate C start.val target.val)
    (hf : 0 < backwardCount C target.val)
    (b : Bool) (c : Fin 5) (z : State (Sp C))
    (hg : terminalClockGuard C P c z) :
    stoppedTerminalPotential C P ((b, c), z) ≤
      ENNReal.ofReal
        (tickWait ((forwardCount C target.val : ℝ) / backwardCount C target.val)
          (backwardCount C target.val) 5) := by
  have hfr : (0 : ℝ) < backwardCount C target.val := by exact_mod_cast hf
  cases b with
  | false => simp [stoppedTerminalPotential]
  | true =>
      by_cases ht : WorkTerminal C z
      · have h := ENNReal.ofReal_le_ofReal
          (tickWait_le_top
            (r := (forwardCount C target.val : ℝ) / backwardCount C target.val)
            (f := (backwardCount C target.val : ℝ))
            (div_nonneg (Nat.cast_nonneg (forwardCount C target.val)) hfr.le) hfr
            (by omega : c.val + 1 ≤ 5))
        simpa [stoppedTerminalPotential, hg, ht] using h
      · simp [stoppedTerminalPotential, hg, ht]

private theorem stoppedTerminalPotential_drift (C : XCTM Q)
    {start target : ClocklessState C} (P : WorkCertificate C start.val target.val)
    (hf : 0 < backwardCount C target.val) :
    ∀ y : (Bool × Fin 5) × State (Sp C),
      stoppedTerminalCost C y +
        ∑ o : Option (Rx C), massActionPMF (net C) (net_hasPositiveRates C) y.2 o *
          stoppedTerminalPotential C P
            (stoppedClockUpdate C y.1 y.2 o, stateStep (net C) y.2 o) ≤
        stoppedTerminalPotential C P y := by
  classical
  rintro ⟨⟨b, c⟩, z⟩
  cases b with
  | false =>
      have hzero (o : Option (Rx C)) :
          stoppedTerminalPotential C P
            (stoppedClockUpdate C (false, c) z o, stateStep (net C) z o) = 0 := by
        unfold stoppedTerminalPotential
        rw [stoppedClockUpdate_dead]
        rfl
      rw [show stoppedTerminalCost C ((false, c), z) = 0 by rfl,
        show stoppedTerminalPotential C P ((false, c), z) = 0 by rfl]
      simp_rw [hzero]
      simp
  | true =>
      by_cases hg : terminalClockGuard C P c z
      · by_cases ht : WorkTerminal C z
        · have hz := terminalClockGuard_target C P c z hg ht
          subst z
          have htt := (workTerminal_clockInsert C target c).mp ht
          have hT := terminal_insert_nonterminal C target c htt hf
          have hfr : (0 : ℝ) < backwardCount C target.val := by exact_mod_cast hf
          have hcost :
              stoppedTerminalCost C ((true, c), clockInsert C target c) =
                ((net C).totalPropensity (clockInsert C target c) : ℝ≥0∞)⁻¹ := by
            simp [stoppedTerminalCost, ht]
          have hcurrent :
              stoppedTerminalPotential C P ((true, c), clockInsert C target c) =
                ENNReal.ofReal
                  (tickWait
                    ((forwardCount C target.val : ℝ) / backwardCount C target.val)
                    (backwardCount C target.val) (c.val + 1)) := by
            simp [stoppedTerminalPotential, hg, ht]
          rw [hcost, hcurrent]
          apply clock_drift_real C (clockInsert C target c) hT
            (c := 1)
            (pn := terminalClockNextValue C (forwardCount C target.val)
              (backwardCount C target.val))
          · rw [clockTotalRate_propensity, ← ENNReal.coe_nnratCast,
              NNRat.cast_natCast, ENNReal.coe_natCast]
            simp only [ENNReal.ofReal_one, one_div]
          · norm_num
          · intro r hr
            have he := (enabled_iff C r _).mpr hr
            have hc : isClock r = true := by
              cases hclock : isClock r with
              | true => rfl
              | false => exact False.elim (ht r hclock he)
            have hstate :
                stateStep (net C) (clockInsert C target c)
                    (some r : Option (Rx C)) =
                  (rxn C r).fire (clockInsert C target c) :=
              clock_stateStep_enabled C (clockInsert C target c) r he
            rw [stoppedClockUpdate_enabled C (true, c) (clockInsert C target c) r he,
              hstate]
            cases htick : isTick r with
            | true =>
                have hp : terminalClockNextValue C
                    (forwardCount C target.val) (backwardCount C target.val) r = 0 := by
                  cases r <;> simp_all [isTick, terminalClockNextValue]
                simp [stoppedTerminalPotential, htick, hp]
            | false =>
                have hfire := clock_move_fire_insert C target c r hc htick he
                have hg' := terminalClockGuard_fire C P c _ hg r he htick
                have ht' : WorkTerminal C ((rxn C r).fire (clockInsert C target c)) := by
                  rw [hfire]
                  exact (workTerminal_clockInsert C target _).mpr htt
                change stoppedTerminalPotential C P
                    ((true, stoppedClockPosition C c r),
                      (rxn C r).fire (clockInsert C target c)) ≤ _
                have hpot :
                    stoppedTerminalPotential C P
                        ((true, stoppedClockPosition C c r),
                          (rxn C r).fire (clockInsert C target c)) =
                      ENNReal.ofReal
                        (tickWait
                          ((forwardCount C target.val : ℝ) / backwardCount C target.val)
                          (backwardCount C target.val)
                          ((stoppedClockPosition C c r).val + 1)) := by
                  simp [stoppedTerminalPotential, hg', ht']
                rw [hpot]
                have hp :
                    tickWait
                        ((forwardCount C target.val : ℝ) / backwardCount C target.val)
                        (backwardCount C target.val)
                        ((stoppedClockPosition C c r).val + 1) =
                      terminalClockNextValue C
                        (forwardCount C target.val) (backwardCount C target.val) r := by
                  cases r <;>
                    simp_all [isClock, isTick, stoppedClockPosition, terminalClockNextValue,
                      Nat.add_assoc]
                rw [hp]
          · exact terminalClockNextValue_nonneg C (Nat.cast_nonneg _) hfr
          · rw [terminal_clock_generator_eq_neg_one C target c htt hf]
            norm_num
        · have hT : ¬ (net C).Terminal z := by
            intro h
            apply ht
            intro r _
            exact h r
          have hnext (o : Option (Rx C))
              (ho : massActionPMF (net C) (net_hasPositiveRates C) z o ≠ 0) :
              stoppedTerminalPotential C P
                  (stoppedClockUpdate C (true, c) z o, stateStep (net C) z o) ≤
                ENNReal.ofReal
                  (tickWait
                    ((forwardCount C target.val : ℝ) / backwardCount C target.val)
                    (backwardCount C target.val) 5) := by
            cases o with
            | none => exact False.elim (ho (clock_pmf_none C z hT))
            | some r =>
                have he :=
                  CTMCBridge.massActionPMF_some_ne_zero_enabled
                    (net C) (net_hasPositiveRates C) z r ho
                have hstate :
                    stateStep (net C) z (some r : Option (Rx C)) = (rxn C r).fire z :=
                  clock_stateStep_enabled C z r he
                rw [stoppedClockUpdate_enabled C (true, c) z r he, hstate]
                cases htick : isTick r with
                | true =>
                    simp [stoppedTerminalPotential, htick]
                | false =>
                    have hg' := terminalClockGuard_fire C P c z hg r he htick
                    simpa [htick] using
                      stoppedTerminalPotential_le_top C P hf true
                        (stoppedClockPosition C c r) ((rxn C r).fire z) hg'
          have hcost : stoppedTerminalCost C ((true, c), z) = 0 := by
            simp [stoppedTerminalCost, ht]
          have hcurrent :
              stoppedTerminalPotential C P ((true, c), z) =
                ENNReal.ofReal
                  (tickWait
                    ((forwardCount C target.val : ℝ) / backwardCount C target.val)
                    (backwardCount C target.val) 5) := by
            simp [stoppedTerminalPotential, hg, ht]
          rw [hcost, zero_add, hcurrent]
          calc
            (∑ o : Option (Rx C),
                massActionPMF (net C) (net_hasPositiveRates C) z o *
                  stoppedTerminalPotential C P
                    (stoppedClockUpdate C (true, c) z o, stateStep (net C) z o)) ≤
                ∑ o : Option (Rx C),
                  massActionPMF (net C) (net_hasPositiveRates C) z o *
                    ENNReal.ofReal
                      (tickWait
                        ((forwardCount C target.val : ℝ) / backwardCount C target.val)
                        (backwardCount C target.val) 5) := by
              apply Finset.sum_le_sum
              intro o _
              by_cases ho : massActionPMF (net C) (net_hasPositiveRates C) z o = 0
              · simp [ho]
              · exact mul_le_mul_left' (hnext o ho) _
            _ = _ := by
              rw [← Finset.sum_mul]
              have hs :
                  (∑ o : Option (Rx C),
                    massActionPMF (net C) (net_hasPositiveRates C) z o) = 1 :=
                massActionWeight_sum_eq_one (net C) (net_hasPositiveRates C) z
              simpa only [one_mul] using congrArg
                (fun t : ℝ≥0∞ => t * ENNReal.ofReal
                  (tickWait
                    ((forwardCount C target.val : ℝ) / backwardCount C target.val)
                    (backwardCount C target.val) 5)) hs
      · simp [stoppedTerminalPotential, hg]


private theorem stoppedClockUpdate_live (C : XCTM Q)
    (a : Bool × Fin 5) (z : State (Sp C)) (o : Option (Rx C)) :
    (stoppedClockUpdate C a z o).1 = (a.1 && !(windowTick C z o)) := by
  cases hlabel : windowLabel C z o <;>
    simp [stoppedClockUpdate, windowTick, hlabel]

private theorem terminal_windowLabel_eq_pathFired (C : XCTM Q)
    (z₀ : State (Sp C)) (n : ℕ) (ω : LabelPath C) :
    windowLabel C (pathState (net C) z₀ ω n) (ω (n + 1)) =
      pathFired (net C) z₀ ω n := by
  classical
  by_cases hT : (net C).Terminal (pathState (net C) z₀ ω n)
  · simp only [windowLabel, pathFired, dif_pos hT] <;> rfl
  · simp only [windowLabel, pathFired, dif_neg hT] <;> rfl

private theorem stoppedClockState_snd (C : XCTM Q)
    (z₀ : State (Sp C)) (c₀ : Fin 5) (n : ℕ) (ω : LabelPath C) :
    (extState (net C) z₀ (stoppedClockUpdate C) (true, c₀) n ω).2 =
      pathState (net C) z₀ ω n :=
  (extState_snd (net C) z₀ (stoppedClockUpdate C) (true, c₀) n ω).trans
    (prefixToState_eq_pathState (net C) z₀ ω n)

private theorem stoppedClockState_live_iff (C : XCTM Q)
    (z₀ : State (Sp C)) (c₀ : Fin 5) (n : ℕ) (ω : LabelPath C) :
    (extState (net C) z₀ (stoppedClockUpdate C) (true, c₀) n ω).1.1 = true ↔
      tickCount C z₀ ω n = 0 := by
  induction n with
  | zero => simp [extState, extOf, tickCount]
  | succ n ih =>
      have hstep :
          (extState (net C) z₀ (stoppedClockUpdate C) (true, c₀) (n + 1) ω).1.1 =
            ((extState (net C) z₀ (stoppedClockUpdate C) (true, c₀) n ω).1.1 &&
              !(firedTick C z₀ ω n)) := by
        rw [extState_succ, stoppedClockUpdate_live, stoppedClockState_snd]
        unfold windowTick firedTick
        rw [terminal_windowLabel_eq_pathFired] <;>
          cases pathFired (net C) z₀ ω n <;> rfl
      rw [hstep]
      cases ht : firedTick C z₀ ω n <;>
        simp [tickCount, TickAt, ht, ih]

/-- Actual terminal-work occupation before the first tick is finite and is
bounded by the frozen target clock's worst-position tick wait. Work before
completion is charged zero in this theorem. -/
theorem terminalWindowMean_le_tickWait (C : XCTM Q)
    (start target : ClocklessState C)
    (P : WorkCertificate C start.val target.val)
    (hf : 0 < backwardCount C target.val) (c₀ : Fin 5) :
    (∫⁻ ω, maskedUnitCost C (clockInsert C start c₀)
      (fun j ω => tickCount C (clockInsert C start c₀) ω j = 0 ∧
        WorkTerminal C (pathState (net C) (clockInsert C start c₀) ω j)) ω
      ∂windowLaw C (clockInsert C start c₀)) ≤
      ENNReal.ofReal
        (tickWait ((forwardCount C target.val : ℝ) / backwardCount C target.val)
          (backwardCount C target.val) 5) := by
  have h := lintegral_tsum_cost_le (net C) (net_hasPositiveRates C)
    (clockInsert C start c₀) (stoppedClockUpdate C) (true, c₀)
    (stoppedTerminalPotential C P) (stoppedTerminalCost C)
    (stoppedTerminalPotential_drift C P hf)
  have heq (ω : LabelPath C) :
      (∑' n, stoppedTerminalCost C
        (extState (net C) (clockInsert C start c₀) (stoppedClockUpdate C)
          (true, c₀) n ω)) =
      maskedUnitCost C (clockInsert C start c₀)
        (fun j ω => tickCount C (clockInsert C start c₀) ω j = 0 ∧
          WorkTerminal C (pathState (net C) (clockInsert C start c₀) ω j)) ω := by
    unfold maskedUnitCost
    apply tsum_congr
    intro n
    simp only [stoppedTerminalCost, stoppedClockState_snd,
      stoppedClockState_live_iff, CTMCBridge.meanHolding]
  simp_rw [heq] at h
  exact h.trans
    (stoppedTerminalPotential_le_top C P hf true c₀ (clockInsert C start c₀)
      ⟨start, P.initial, rfl⟩)

theorem terminalWindowMean_ne_top (C : XCTM Q)
    (start target : ClocklessState C)
    (P : WorkCertificate C start.val target.val)
    (hf : 0 < backwardCount C target.val) (c₀ : Fin 5) :
    (∫⁻ ω, maskedUnitCost C (clockInsert C start c₀)
      (fun j ω => tickCount C (clockInsert C start c₀) ω j = 0 ∧
        WorkTerminal C (pathState (net C) (clockInsert C start c₀) ω j)) ω
      ∂windowLaw C (clockInsert C start c₀)) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (terminalWindowMean_le_tickWait C start target P hf c₀)

end Ripple.sCRNUniversality.ClockedCTM.Unbounded.TimeAnalysis


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded.TimeAnalysis

open Stochastic Stochastic.MassAction WindowAnalysis MeasureTheory
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The actual fresh-window unit reward splits into standalone work and
terminal clock waiting, with no time change and no assumed balance law. -/
theorem firstWindowUnitMean_le_work_add_tickWait (C : XCTM Q)
    (start target : ClocklessState C)
    (P : WorkCertificate C start.val target.val)
    (hf : 0 < backwardCount C target.val) (c₀ : Fin 5) :
    firstWindowUnitMean C (clockInsert C start c₀) ≤
      StandaloneWork.meanDuration C start.val +
        ENNReal.ofReal
          (tickWait ((forwardCount C target.val : ℝ) / backwardCount C target.val)
            (backwardCount C target.val) 5) := by
  rw [firstWindowUnitMean_split]
  exact add_le_add (firstWindowWorkMean_le_meanDuration C start c₀)
    (terminalWindowMean_le_tickWait C start target P hf c₀)

theorem firstWindowUnitMean_ne_top (C : XCTM Q)
    (start target : ClocklessState C)
    (P : WorkCertificate C start.val target.val)
    (hf : 0 < backwardCount C target.val) (c₀ : Fin 5) :
    firstWindowUnitMean C (clockInsert C start c₀) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr
      ⟨StandaloneWork.meanDuration_ne_top C P, ENNReal.ofReal_ne_top⟩)
    (firstWindowUnitMean_le_work_add_tickWait C start target P hf c₀)

/-- Every actual terminal clock occupation is bounded by the complete
terminal reward; this also supplies individual occupation finiteness. -/
theorem terminal_windowOccupation_le_terminalMean (C : XCTM Q)
    (z₀ : State (Sp C)) (j : ℕ) (x : ClocklessState C) (c : Fin 5)
    (ht : WorkTerminal C x.val) :
    windowOccupation C z₀ j x c ≤ firstWindowTerminalMean C z₀ := by
  classical
  let h : ℝ≥0∞ := ((net C).totalPropensity (clockInsert C x c) : ℝ≥0∞)⁻¹
  have heq :
      windowOccupation C z₀ j x c =
        ∫⁻ ω, ∑' n : ℕ,
          (windowEvent C z₀ n j (clockInsert C x c)).indicator (fun _ => h) ω
          ∂windowLaw C z₀ := by
    rw [lintegral_tsum (fun n =>
      (measurable_const.indicator
        (measurableSet_windowEvent C z₀ n j (clockInsert C x c))).aemeasurable)]
    simp_rw [lintegral_indicator_const
      (measurableSet_windowEvent C z₀ _ j (clockInsert C x c))]
    rw [ENNReal.tsum_mul_left]
    unfold windowOccupation windowOcc
    rw [div_eq_mul_inv, mul_comm]
  rw [heq]
  apply lintegral_mono
  intro ω
  apply ENNReal.tsum_le_tsum
  intro n
  by_cases hE : ω ∈ windowEvent C z₀ n j (clockInsert C x c)
  · have hp := (windowEvent_iff C z₀ n j (clockInsert C x c) ω).mp hE
    have hT : WorkTerminal C (pathState (net C) z₀ ω n) := by
      rw [hp.2.2]
      exact (workTerminal_clockInsert C x c).mpr ht
    rw [Set.indicator_of_mem hE]
    rw [if_pos ⟨hp.2.1, hT⟩]
    change h ≤ ((net C).totalPropensity
      (pathState (net C) z₀ ω n) : ℝ≥0∞)⁻¹
    rw [hp.2.2]
  · rw [Set.indicator_of_notMem hE]
    exact bot_le

theorem terminal_windowOccupation_ne_top (C : XCTM Q)
    (start target : ClocklessState C)
    (P : WorkCertificate C start.val target.val)
    (hf : 0 < backwardCount C target.val)
    (c₀ : Fin 5) (j : ℕ) (x : ClocklessState C) (c : Fin 5)
    (ht : WorkTerminal C x.val) :
    windowOccupation C (clockInsert C start c₀) j x c ≠ ⊤ :=
  ne_top_of_le_ne_top (terminalWindowMean_ne_top C start target P hf c₀)
    (terminal_windowOccupation_le_terminalMean C (clockInsert C start c₀) j x c ht)

end Ripple.sCRNUniversality.ClockedCTM.Unbounded.TimeAnalysis


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Classical

variable {Q : Type} [Fintype Q] [DecidableEq Q]

namespace TimeAnalysis

open WindowAnalysis

private theorem occupation_tsum_eq_tail (f : ℕ → ℝ≥0∞) (cut : ℕ)
    (hzero : ∀ j < cut, f j = 0) :
    (∑' j, f j) = ∑' j, f (cut + j) := by
  induction cut generalizing f with
  | zero => simp
  | succ cut ih =>
      rw [tsum_eq_zero_add' ENNReal.summable, hzero 0 (by omega), zero_add]
      have ht := ih (fun j => f (j + 1))
        (fun j hj => hzero (j + 1) (by omega))
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem goodPrefix_has_goodWindowEntry
    (C : XCTM Q) (z₀ : State (Sp C)) (ω : LabelPath C) (k j : ℕ)
    (hgood : goodPrefix C z₀ j ω) (hcount : tickCount C z₀ ω j = k + 1) :
    ∃ cut ≤ j, ω ∈ goodWindowEntry C z₀ k cut := by
  let hex : ∃ n : ℕ, k + 1 ≤ tickCount C z₀ ω n := ⟨j, hcount.ge⟩
  let cut := Nat.find hex
  have hcut : cut ≤ j := Nat.find_min' hex hcount.ge
  have hfound : k + 1 ≤ tickCount C z₀ ω cut := Nat.find_spec hex
  have hpos : 0 < cut := by
    by_contra h
    have hz : cut = 0 := by omega
    rw [hz] at hfound
    change k + 1 ≤ 0 at hfound
    omega
  let m := cut - 1
  have hm : m + 1 = cut := by dsimp only [m]; omega
  have hbefore : ¬ k + 1 ≤ tickCount C z₀ ω m :=
    Nat.find_min hex (by dsimp only [m]; omega)
  have hstep := tickCount_succ_le C z₀ ω m
  rw [hm] at hstep
  have hmc : tickCount C z₀ ω m = k := by omega
  have hTick : TickAt C z₀ ω m := by
    by_contra h
    have hflat : tickCount C z₀ ω (m + 1) = tickCount C z₀ ω m := by
      simp only [tickCount, if_neg h, Nat.add_zero]
    rw [hm] at hflat
    omega
  refine ⟨m + 1, by omega, hmc, hTick, ?_⟩
  intro l hl
  exact hgood l (by omega)

theorem goodWindowUnitCost_le_restart
    (C : XCTM Q) (z₀ : State (Sp C)) (k cut : ℕ) (ω : LabelPath C)
    (hentry : ω ∈ goodWindowEntry C z₀ k cut) :
    maskedUnitCost C z₀ (windowActive C z₀ (k + 1)) ω ≤
      firstWindowUnitCost C (pathState (net C) z₀ ω cut)
        (restartLabels (net C) cut ω) := by
  have hbefore : ∀ j < cut, ¬ windowActive C z₀ (k + 1) j ω := by
    intro j hj ha
    cases cut with
    | zero => omega
    | succ m =>
        have hm : tickCount C z₀ ω m = k := hentry.1
        have hmono := tickCount_mono C z₀ ω (show j ≤ m by omega)
        change tickCount C z₀ ω j ≤ tickCount C z₀ ω m at hmono
        have hc : tickCount C z₀ ω j = k + 1 := ha.1
        omega
  change (∑' j, if windowActive C z₀ (k + 1) j ω then
      CTMCBridge.meanHolding (net C) z₀ j ω else 0) ≤ _
  rw [occupation_tsum_eq_tail _ cut (fun j hj => if_neg (hbefore j hj))]
  apply ENNReal.tsum_le_tsum
  intro j
  by_cases ha : windowActive C z₀ (k + 1) (cut + j) ω
  · rw [if_pos ha]
    have hcc := goodWindowEntry_count C z₀ k cut ω hentry
    have hshift := tickCount_restartLabels_add C z₀ ω cut j
    have hzero : tickCount C (pathState (net C) z₀ ω cut)
        (restartLabels (net C) cut ω) j = 0 := by
      rw [ha.1, hcc] at hshift
      omega
    rw [if_pos hzero]
    change ((net C).totalPropensity (pathState (net C) z₀ ω (cut + j)) : ℝ≥0∞)⁻¹ ≤
      ((net C).totalPropensity
        (pathState (net C) (pathState (net C) z₀ ω cut)
          (restartLabels (net C) cut ω) j) : ℝ≥0∞)⁻¹
    rw [pathState_restartLabels]
  · rw [if_neg ha]
    exact bot_le

theorem goodWindowUnitMean_zero_le_first (C : XCTM Q) (z₀ : State (Sp C)) :
    goodWindowUnitMean C z₀ 0 ≤ firstWindowUnitMean C z₀ := by
  apply lintegral_mono
  intro ω
  apply ENNReal.tsum_le_tsum
  intro j
  by_cases ha : windowActive C z₀ 0 j ω
  · simp only [if_pos ha, if_pos ha.1, le_refl]
  · rw [if_neg ha]
    exact bot_le

/-- State-dependent fresh reward bounds transfer through the actual entry
slices. The countable partition by both entry index and entry state also
covers idle windows whose accumulated signal count is not deterministic. -/
theorem goodWindowUnitMean_succ_le_fresh_bound
    (C : XCTM Q) (z₀ : State (Sp C)) (k : ℕ)
    (hLemmaEightRestart : RawStateRestart C z₀) (B : ℝ≥0∞)
    (hFresh : ∀ cut ω, ω ∈ goodWindowEntry C z₀ k cut →
      firstWindowUnitMean C (pathState (net C) z₀ ω cut) ≤ B) :
    goodWindowUnitMean C z₀ (k + 1) ≤ B := by
  let A : (a : ℕ × State (Sp C)) →
      Set ((j : Finset.Iic a.1) → Option (Rx C)) :=
    fun a => goodWindowEntryPrefix C z₀ k a.1 ∩
      {p | prefixToState (net C) z₀ a.1 p = a.2}
  have hprefix (cut : ℕ) (ω : LabelPath C) :
      prefixToState (net C) z₀ cut (Preorder.frestrictLe cut ω) =
        pathState (net C) z₀ ω cut :=
    prefixToState_eq_pathState (net C) z₀ ω cut
  have hAevent (a : ℕ × State (Sp C)) :
      {ω : LabelPath C | Preorder.frestrictLe a.1 ω ∈ A a} =
        goodWindowEntry C z₀ k a.1 ∩
          {ω | pathState (net C) z₀ ω a.1 = a.2} := by
    ext ω
    change (Preorder.frestrictLe a.1 ω ∈ goodWindowEntryPrefix C z₀ k a.1 ∧
      prefixToState (net C) z₀ a.1 (Preorder.frestrictLe a.1 ω) = a.2) ↔ _
    rw [hprefix a.1 ω]
    have he : (Preorder.frestrictLe a.1 ω ∈ goodWindowEntryPrefix C z₀ k a.1) ↔
        ω ∈ goodWindowEntry C z₀ k a.1 := by
      change ω ∈ {ω : LabelPath C | Preorder.frestrictLe a.1 ω ∈
        goodWindowEntryPrefix C z₀ k a.1} ↔ _
      rw [goodWindowEntryPrefix_event C z₀ k a.1]
    exact and_congr he Iff.rfl
  have hdisjoint : Pairwise (Function.onFun Disjoint
      (fun a : ℕ × State (Sp C) =>
        {ω : LabelPath C | Preorder.frestrictLe a.1 ω ∈ A a})) := by
    intro a b hab
    refine Set.disjoint_left.mpr ?_
    intro ω ha hb
    change ω ∈ {ω : LabelPath C | Preorder.frestrictLe a.1 ω ∈ A a} at ha
    change ω ∈ {ω : LabelPath C | Preorder.frestrictLe b.1 ω ∈ A b} at hb
    rw [hAevent a] at ha
    rw [hAevent b] at hb
    by_cases hc : a.1 = b.1
    · have hs : a.2 = b.2 := by
        rw [← ha.2, ← hb.2, hc]
      exact hab (Prod.ext hc hs)
    · exact (Set.disjoint_left.mp (goodWindowEntry_pairwise C z₀ k hc)) ha.1 hb.1
  have hrestart : ∀ (a : ℕ × State (Sp C))
      (p : (j : Finset.Iic a.1) → Option (Rx C)), p ∈ A a →
      (Kernel.traj (X := fun _ => Option (net C).I)
        (fun j => stepKernel (net C) (net_hasPositiveRates C) z₀ j)
        a.1 p).map (restartLabels (net C) a.1) =
          rawLaw (net C) (net_hasPositiveRates C) a.2 := by
    intro a p hp
    have hr := hLemmaEightRestart a.1 p
    rw [hp.2] at hr
    exact hr
  have hfresh : ∀ (a : ℕ × State (Sp C))
      (p : (j : Finset.Iic a.1) → Option (Rx C)), p ∈ A a →
      (∫⁻ ω, firstWindowUnitCost C a.2 ω
        ∂rawLaw (net C) (net_hasPositiveRates C) a.2) ≤ B := by
    intro a p hp
    obtain ⟨ω, hω, heq⟩ := hp.1
    have hs : pathState (net C) z₀ ω a.1 = a.2 := by
      rw [← hprefix a.1 ω, heq]
      exact hp.2
    simpa only [hs] using hFresh a.1 ω hω
  have hbound := rawLaw_stopped_prefix_reward_le_of_restart
    (net C) (net_hasPositiveRates C) z₀
    (fun a : ℕ × State (Sp C) => a.1) A
    (fun a => a.2) (fun a => firstWindowUnitCost C a.2)
    (fun a => measurable_firstWindowUnitCost C a.2)
    hdisjoint hrestart B hfresh
  refine (lintegral_mono ?_).trans hbound
  intro ω
  by_cases ha : ∃ j, windowActive C z₀ (k + 1) j ω
  · obtain ⟨j, hj⟩ := ha
    obtain ⟨cut, _, hentry⟩ :=
      goodPrefix_has_goodWindowEntry C z₀ ω k j hj.2 hj.1
    let a : ℕ × State (Sp C) := (cut, pathState (net C) z₀ ω cut)
    have hA : ω ∈ {ω : LabelPath C | Preorder.frestrictLe a.1 ω ∈ A a} := by
      rw [hAevent a]
      exact ⟨hentry, rfl⟩
    calc
      maskedUnitCost C z₀ (windowActive C z₀ (k + 1)) ω ≤
          firstWindowUnitCost C a.2 (restartLabels (net C) a.1 ω) :=
        goodWindowUnitCost_le_restart C z₀ k cut ω hentry
      _ = ({ω | Preorder.frestrictLe a.1 ω ∈ A a} : Set (LabelPath C)).indicator
          (fun ω => firstWindowUnitCost C a.2 (restartLabels (net C) a.1 ω)) ω :=
        (Set.indicator_of_mem hA
          (fun ω => firstWindowUnitCost C a.2 (restartLabels (net C) a.1 ω))).symm
      _ ≤ _ := ENNReal.le_tsum a
  · have hz : maskedUnitCost C z₀ (windowActive C z₀ (k + 1)) ω = 0 := by
      unfold maskedUnitCost
      apply ENNReal.tsum_eq_zero.mpr
      intro j
      exact if_neg (fun hj => ha ⟨j, hj⟩)
    rw [hz]
    exact bot_le

end TimeAnalysis
end Ripple.sCRNUniversality.ClockedCTM.Unbounded


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction WindowAnalysis
open scoped ENNReal

variable {Q : Type} [Fintype Q] [DecidableEq Q]

namespace WindowAnalysis

/-- A clockless clean payload with any number of idle signal molecules. -/
def idleWork (C : XCTM Q) (p : Plan C) (signal : ℕ) : ClocklessState C :=
  ⟨Plan.workState C p + signal • unit .signal, by
    cases p <;> funext s <;> cases s <;>
      simp [workView, Plan.workState, payload, unit, Pi.smul_apply]⟩

theorem idleWork_forwardCount (C : XCTM Q) (p : Plan C) (signal : ℕ) :
    forwardCount C (idleWork C p signal).val = forwardCount C (Plan.workState C p) := by
  simp [idleWork, forwardCount, unit, Pi.smul_apply]

theorem idleWork_backwardCount (C : XCTM Q) (p : Plan C) (signal : ℕ) :
    backwardCount C (idleWork C p signal).val = backwardCount C (Plan.workState C p) := by
  simp [idleWork, backwardCount, unit, Pi.smul_apply]

theorem idleWork_terminal (C : XCTM Q) (p : Plan C) (signal : ℕ)
    (hh : Plan.halted C p = true) :
    WorkTerminal C (idleWork C p signal).val := by
  cases p with
  | first q w a latent =>
      have hm : C.mode q = .halt := by
        cases he : C.mode q <;> simp_all [Plan.halted]
      exact halted_payload_terminal C q w a latent signal hm
  | _ => simp [Plan.halted] at hh

theorem planWork_backwardCount_pos (C : XCTM Q) (p : Plan C)
    (hs : 3 ≤ p.tape.length) :
    0 < backwardCount C (Plan.workState C p) := by
  have hd : 0 < stateCount p.tape.length := by unfold stateCount; positivity
  have hdiv : 0 < stateCount p.tape.length / 3 := by
    have he := stateCount_div_exact p.tape.length hs
    omega
  cases p with
  | first q w a latent =>
      cases latent
      · simpa [Plan.tape, backwardCount, Plan.workState, payload] using hd
      · simpa [Plan.tape, backwardCount, Plan.workState, payload] using hdiv
  | second q w a =>
      simpa [Plan.tape, backwardCount, Plan.workState, payload] using hd
  | third q w a =>
      simpa [Plan.tape, backwardCount, Plan.workState, payload] using hd
  | write q b w a =>
      simpa [Plan.tape, backwardCount, Plan.workState, payload] using hd
  | extend e w a =>
      simpa [Plan.tape, backwardCount, Plan.workState, payload] using hdiv

theorem idleWork_backwardCount_pos (C : XCTM Q) (p : Plan C) (signal : ℕ)
    (hs : 3 ≤ p.tape.length) :
    0 < backwardCount C (idleWork C p signal).val := by
  rw [idleWork_backwardCount]
  exact planWork_backwardCount_pos C p hs

/-- The work certificate for an already terminal clockless state. -/
def terminalWorkCertificate (C : XCTM Q) (x : ClocklessState C)
    (ht : WorkTerminal C x.val) : WorkCertificate C x.val x.val where
  inv z := z = x.val
  rank _ := 0
  initial := rfl
  closed z y hz hstep := by
    subst z
    rcases hstep with ⟨r, hr, he, _⟩
    exact (ht r hr he).elim
  decreases z y hz hstep := by
    subst z
    rcases hstep with ⟨r, hr, he, _⟩
    exact (ht r hr he).elim
  terminal z hz _ := by
    subst z
    exact x.property

theorem idleWork_meanDuration_eq_zero (C : XCTM Q) (p : Plan C) (signal : ℕ)
    (hh : Plan.halted C p = true) :
    StandaloneWork.meanDuration C (idleWork C p signal).val = 0 :=
  StandaloneWork.meanDuration_eq_zero_of_terminal C _
    (idleWork_terminal C p signal hh)

end WindowAnalysis

namespace TimeAnalysis

/-- Every scheduled work contribution is finite from the compiled rank
certificates; no quantitative phase estimate is needed for this fact. -/
theorem scheduled_workMean_ne_top (C : XCTM Q)
    (i : ℕ) (w : List Bool) (hs : 3 ≤ w.length) (k : ℕ) :
    StandaloneWork.meanDuration C (scheduledWorkStart C i w k) ≠ ⊤ := by
  cases k with
  | zero =>
      rw [scheduledWorkStart, StandaloneWork.initial_meanDuration_eq_zero]
      exact ENNReal.zero_ne_top
  | succ k =>
      change StandaloneWork.meanDuration C
        (Plan.workState C (plan C i w k) + unit .signal) ≠ ⊤
      cases hh : Plan.halted C (plan C i w k) with
      | true =>
          rw [StandaloneWork.halted_next_meanDuration_eq_zero C _ hh]
          exact ENNReal.zero_ne_top
      | false =>
          exact StandaloneWork.next_window_meanDuration_ne_top C _
            (plan_valid C i w hs k) hh

end TimeAnalysis

end Ripple.sCRNUniversality.ClockedCTM.Unbounded

namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction WindowAnalysis
open scoped ENNReal

variable {Q : Type} [Fintype Q] [DecidableEq Q]

namespace WindowAnalysis

/-- Exact catalyst counts at the ends of the four windows in one active cycle. -/
theorem first_iterate_terminal_counts (C : XCTM Q)
    (q : Q) (w : List Bool) (a : ℕ) (latent : Bool)
    (hs : 3 ≤ w.length) (hh : C.mode q ≠ .halt)
    (r : ℕ) (hr : r < 4) :
    forwardCount C (Plan.workState C (Plan.iterate C (.first q w a latent) r)) =
        (if r = 0 then a else a + 1) *
          backwardCount C (Plan.workState C (Plan.iterate C (.first q w a latent) r)) ∧
      backwardCount C (Plan.workState C (Plan.iterate C (.first q w a latent) r)) =
        if r = 0 then
          (if latent then stateCount w.length / 3 else stateCount w.length)
        else stateCount w.length := by
  cases hmode : C.mode q with
  | read =>
      have hfirst :
          Plan.advance C (.first q w a latent) =
            .second (.inl ⟨q, hmode⟩) w (a + 1) := by
        dsimp only [Plan.advance]
        split <;> first
          | rfl
          | (exfalso; rename_i hm; rw [hmode] at hm; cases hm)
          | simp_all
      have hlen := read_length w (by omega : 1 ≤ w.length)
        (C.next q (w.headD false)).2
      have hlenNat : w.length - 1 + 1 = w.length := by omega
      interval_cases r <;>
        simp only [Plan.iterate, hfirst] <;>
        cases latent <;>
        simp [Plan.advance, Plan.workState, forwardCount, backwardCount, payload, hlen, hlenNat]
  | extend q' =>
      have hfirst :
          Plan.advance C (.first q w a latent) =
            .second (.inr ⟨q, ⟨q', hmode⟩⟩) w (a + 1) := by
        dsimp only [Plan.advance]
        split <;> first
          | rfl
          | (exfalso; rename_i hm; rw [hmode] at hm; cases hm)
          | simp_all
      have hd : stateCount (w.length + 1) / 3 = stateCount w.length := by
        rw [stateCount_succ w.length (by omega)]
        omega
      interval_cases r <;>
        simp only [Plan.iterate, hfirst] <;>
        cases latent <;>
        simp [Plan.advance, Plan.workState, forwardCount, backwardCount, payload, hd]
  | halt => exact False.elim (hh hmode)

end WindowAnalysis

namespace TimeAnalysis

/-- The terminal ratio is exact; only the backward rate is relaxed in W1. -/
theorem terminal_schedule_parameters (C : XCTM Q)
    (i : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (n : ℕ) (hbefore : BeforeHalt C w n) (k : ℕ) (hk : k < 4 * n) :
    (forwardCount C (Plan.workState C (plan C i w k)) : ℝ) =
        terminalRatioBudget i k *
          (backwardCount C (Plan.workState C (plan C i w k)) : ℝ) ∧
      terminalBackwardBudget C w k ≤
        (backwardCount C (Plan.workState C (plan C i w k)) : ℝ) := by
  let m := k / 4
  let r := k % 4
  have hr : r < 4 := Nat.mod_lt _ (by norm_num)
  have hmod : k % 4 = r := rfl
  have hdiv : k / 4 = m := rfl
  have hm : m < n := by dsimp only [m]; omega
  have hdecomp : k = 4 * m + r := by dsimp only [m, r]; omega
  have hp := plan_at_step C i w hs m (fun j hj => hbefore j (by omega))
  have hsrun : 3 ≤ (C.runT (C.start, w) m).2.length := by
    have hv := plan_valid C i w hs (4 * m)
    rw [hp] at hv
    exact hv
  have hc := first_iterate_terminal_counts C
    (C.runT (C.start, w) m).1 (C.runT (C.start, w) m).2
    (i + m) (previousExtension C w m) hsrun (hbefore m hm) r hr
  have hp' :
      plan C i w k =
        Plan.iterate C
          (.first (C.runT (C.start, w) m).1 (C.runT (C.start, w) m).2
            (i + m) (previousExtension C w m)) r := by
    rw [hdecomp, plan_add, hp]
  rw [← hp'] at hc
  constructor
  · by_cases hz : r = 0
    · have haNat :
          forwardCount C (Plan.workState C (plan C i w k)) =
            (i + m) * backwardCount C (Plan.workState C (plan C i w k)) := by
        simpa only [hz, if_pos rfl] using hc.1
      have ha :
          (forwardCount C (Plan.workState C (plan C i w k)) : ℝ) =
            (i + m : ℕ) *
              (backwardCount C (Plan.workState C (plan C i w k)) : ℝ) := by
        exact_mod_cast haNat
      simpa only [terminalRatioBudget, windowAccuracy, hmod, hz, if_pos rfl,
        hdiv, Nat.cast_add] using ha
    · have haNat :
          forwardCount C (Plan.workState C (plan C i w k)) =
            (i + m + 1) * backwardCount C (Plan.workState C (plan C i w k)) := by
        simpa only [if_neg hz] using hc.1
      have ha :
          (forwardCount C (Plan.workState C (plan C i w k)) : ℝ) =
            (i + m + 1 : ℕ) *
              (backwardCount C (Plan.workState C (plan C i w k)) : ℝ) := by
        exact_mod_cast haNat
      simpa only [terminalRatioBudget, windowAccuracy, hmod, if_neg hz,
        hdiv, Nat.cast_add, Nat.cast_one] using ha
  · by_cases hz : r = 0
    · have hd := stateCount_div_exact (C.runT (C.start, w) m).2.length hsrun
      have hd' :
          (3 : ℝ) * (stateCount (C.runT (C.start, w) m).2.length / 3 : ℕ) =
            (stateCount (C.runT (C.start, w) m).2.length : ℝ) := by
        exact_mod_cast hd
      have hb := hc.2
      simp only [hz, if_pos rfl] at hb
      rw [hb]
      simp only [terminalBackwardBudget, windowPopulation, hmod, hz, if_pos rfl, hdiv]
      cases previousExtension C w m <;> simp only [Bool.false_eq_true, if_false, if_true]
      · have hnonneg : (0 : ℝ) ≤ stateCount (C.runT (C.start, w) m).2.length :=
          Nat.cast_nonneg _
        linarith
      · linarith
    · have hb := hc.2
      simp only [if_neg hz] at hb
      rw [hb]
      simp only [terminalBackwardBudget, windowPopulation, hmod, if_neg hz, hdiv]
      exact le_rfl

theorem terminalRatioBudget_nonneg (i k : ℕ) :
    0 ≤ terminalRatioBudget i k := by
  unfold terminalRatioBudget windowAccuracy
  split_ifs <;> positivity

theorem terminalBackwardBudget_pos (C : XCTM Q) (w : List Bool) (k : ℕ) :
    0 < terminalBackwardBudget C w k := by
  unfold terminalBackwardBudget
  split_ifs
  · exact div_pos (windowPopulation_pos C w k) (by norm_num)
  · exact windowPopulation_pos C w k

/-- A larger positive backward rate can only shorten the frozen clock wait. -/
theorem tickWait_antitone_backward {r f g : ℝ} (hr : 0 ≤ r)
    (hf : 0 < f) (hfg : f ≤ g) (c : ℕ) :
    tickWait r g c ≤ tickWait r f c := by
  unfold tickWait
  apply div_le_div_of_nonneg_left _ hf hfg
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => pow_nonneg hr j

end TimeAnalysis

end Ripple.sCRNUniversality.ClockedCTM.Unbounded


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction WindowAnalysis
open scoped ENNReal

variable {Q : Type} [Fintype Q] [DecidableEq Q]

namespace WindowAnalysis

theorem cleanView_true_eq_idleWork (C : XCTM Q)
    (p : Plan C) (z : State (Sp C))
    (h : cleanView C true z = Plan.workState C p) :
    workView C z = (idleWork C p (z .signal)).val := by
  cases p <;> funext s
  all_goals
    have he := congrFun h s
    cases s <;>
      simpa [idleWork, cleanView, workView, Plan.workState, payload, unit] using he

theorem tick_fire_eq_idleWindowStart (C : XCTM Q)
    (p : Plan C) (signal : ℕ) (z : State (Sp C)) (b : Bool)
    (hwork : workView C z = (idleWork C p signal).val)
    (hclock : clockMoleculeCount C z = 1)
    (he : (rxn C (.tick b)).enabled z) :
    (rxn C (.tick b)).fire z = clockInsert C (idleWork C p (signal + 1)) 4 := by
  have hp := (enabled_iff C (.tick b) z).mp he
  have hpos : 0 < z (.clock 0) := by
    by_contra h
    have hz : z (.clock 0) = 0 := by omega
    apply hp
    cases b <;> simp [rate, sourceLeft, sourceRight, hz]
  have hc : ∀ c : Fin 5, z (.clock c) = if c = 0 then 1 else 0 := by
    simp [clockMoleculeCount, Fin.sum_univ_succ] at hclock
    intro c
    fin_cases c <;> simp <;> omega
  have hw := tick_workView C b z he
  rw [hwork] at hw
  funext s
  have hws := congrFun hw s
  cases s with
  | clock c =>
      rw [clockInsert_clock]
      cases b <;> fin_cases c <;>
        simp [fire_apply, sourceLeft, sourceRight, products, unit, hc]
  | _ =>
      simpa [workView, clockInsert, idleWork, unit, add_nsmul, add_assoc] using hws

/-- Halting does not reset accumulated signal. The restarted state contains
exactly the clean halted payload, a finite signal count, and the top clock. -/
theorem goodWindowEntry_halted_state
    (C : XCTM Q) (i : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (k : ℕ) (hh : Plan.halted C (plan C i w k) = true)
    (cut : ℕ) (ω : LabelPath C)
    (h : ω ∈ goodWindowEntry C (initial C i w) k cut) :
    ∃ signal : ℕ,
      pathState (net C) (initial C i w) ω cut =
        clockInsert C (idleWork C (plan C i w k) signal) 4 := by
  cases cut with
  | zero => exact False.elim h
  | succ j =>
      obtain ⟨hcount, hTick, hNo⟩ := h
      have hW := window_of_noBadTick_before C i w hs ω j
        (fun m hm => hNo m (by omega))
      have ht : WorkTerminal C (pathState (net C) (initial C i w) ω j) := by
        by_contra hn
        exact hNo j (Nat.lt_succ_self j) ⟨hTick, hn⟩
      have hclean := window_terminal_clean C i w hs _ _ hW ht
      rw [hcount] at hclean
      have hclean' :
          cleanView C true (pathState (net C) (initial C i w) ω j) =
            Plan.workState C (plan C i w k) := by
        simpa only [Clean, hh, gamma] using hclean
      have hwork := cleanView_true_eq_idleWork C (plan C i w k) _ hclean'
      have hclock : clockMoleculeCount C
          (pathState (net C) (initial C i w) ω j) = 1 := by
        rw [clockMoleculeCount_path]
        simp [clockMoleculeCount, initial, Fin.sum_univ_succ]
      have hv := pathFired_valid (net C) (initial C i w) ω j
      cases hF : pathFired (net C) (initial C i w) ω j with
      | none => simp [TickAt, firedTick, hF] at hTick
      | some r =>
          simp only [hF] at hv
          have hrt : isTick r = true := by
            simpa only [TickAt, firedTick, hF] using hTick
          have hcases : ∃ b : Bool, r = .tick b := by
            cases r <;> simp_all [isTick]
          obtain ⟨b, rfl⟩ := hcases
          refine ⟨pathState (net C) (initial C i w) ω j .signal + 1, ?_⟩
          rw [hv.2]
          exact tick_fire_eq_idleWindowStart C (plan C i w k) _ _ b hwork hclock hv.1

end WindowAnalysis

end Ripple.sCRNUniversality.ClockedCTM.Unbounded


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction WindowAnalysis
open scoped ENNReal

variable {Q : Type} [Fintype Q] [DecidableEq Q]

namespace WindowAnalysis

def planWork (C : XCTM Q) (p : Plan C) : ClocklessState C :=
  ⟨Plan.workState C p, workView_planState C p⟩

theorem initial_eq_clockInsert_planWork (C : XCTM Q) (i : ℕ) (w : List Bool) :
    initial C i w = clockInsert C (planWork C (plan C i w 0)) 4 := by
  funext s
  have he := congrFun (initial_workView C i w) s
  cases s with
  | clock c =>
      rw [clockInsert_clock]
      rfl
  | _ => simpa [workView, gamma, clockInsert, planWork, unit] using he

end WindowAnalysis

namespace TimeAnalysis

/-- The exact frozen-clock wait at a clean terminal payload. -/
noncomputable def terminalPlanWait (C : XCTM Q) (p : Plan C) : ℝ :=
  tickWait ((forwardCount C (Plan.workState C p) : ℝ) /
      backwardCount C (Plan.workState C p))
    (backwardCount C (Plan.workState C p)) 5

theorem firstWindowUnitMean_idle_le (C : XCTM Q)
    (p : Plan C) (hs : 3 ≤ p.tape.length)
    (hh : Plan.halted C p = true) (signal : ℕ) :
    firstWindowUnitMean C (clockInsert C (idleWork C p signal) 4) ≤
      ENNReal.ofReal (terminalPlanWait C p) := by
  have hb := firstWindowUnitMean_le_work_add_tickWait C
    (idleWork C p signal) (idleWork C p signal)
    (terminalWorkCertificate C (idleWork C p signal) (idleWork_terminal C p signal hh))
    (idleWork_backwardCount_pos C p signal hs) 4
  simpa only [idleWork_meanDuration_eq_zero C p signal hh, zero_add,
    idleWork_forwardCount, idleWork_backwardCount, terminalPlanWait] using hb

theorem firstWindowUnitMean_next_le (C : XCTM Q)
    (p : Plan C) (hs : 3 ≤ p.tape.length)
    (hh : Plan.halted C p = false) :
    firstWindowUnitMean C (clockInsert C (nextWindowWork C p) 4) ≤
      StandaloneWork.meanDuration C (Plan.workState C p + unit .signal) +
        ENNReal.ofReal (terminalPlanWait C (Plan.advance C p)) := by
  exact firstWindowUnitMean_le_work_add_tickWait C
    (nextWindowWork C p) (planWork C (Plan.advance C p))
    (planCertificate C p hs hh)
    (planWork_backwardCount_pos C (Plan.advance C p) (Plan.advance_valid C p hs)) 4

theorem firstWindowUnitMean_initial_le (C : XCTM Q)
    (i : ℕ) (w : List Bool) (hs : 3 ≤ w.length) :
    firstWindowUnitMean C (initial C i w) ≤
      StandaloneWork.meanDuration C (scheduledWorkStart C i w 0) +
        ENNReal.ofReal (terminalPlanWait C (plan C i w 0)) := by
  let x := planWork C (plan C i w 0)
  have ht : WorkTerminal C x.val := Plan.workState_terminal C (plan C i w 0)
  have hf : 0 < backwardCount C x.val :=
    planWork_backwardCount_pos C (plan C i w 0) (plan_valid C i w hs 0)
  have hb := firstWindowUnitMean_le_work_add_tickWait C x x
    (terminalWorkCertificate C x ht) hf 4
  rw [initial_eq_clockInsert_planWork]
  simpa only [x, planWork, scheduledWorkStart, initial_workView, gamma,
    terminalPlanWait] using hb

/-- All windows satisfy the work plus exact terminal-clock split. The
halting branch keeps arbitrary idle signals instead of resetting them. -/
theorem goodWindowUnitMean_le_scheduled_work_clock
    (C : XCTM Q) (i : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (hLemmaEightRestart : RawStateRestart C (initial C i w)) (k : ℕ) :
    goodWindowUnitMean C (initial C i w) k ≤
      StandaloneWork.meanDuration C (scheduledWorkStart C i w k) +
        ENNReal.ofReal (terminalPlanWait C (plan C i w k)) := by
  cases k with
  | zero =>
      exact (goodWindowUnitMean_zero_le_first C (initial C i w)).trans
        (firstWindowUnitMean_initial_le C i w hs)
  | succ k =>
      apply goodWindowUnitMean_succ_le_fresh_bound C (initial C i w) k
        hLemmaEightRestart
      intro cut ω hentry
      cases hh : Plan.halted C (plan C i w k) with
      | false =>
          rw [goodWindowEntry_state C i w hs k hh cut ω hentry]
          simpa only [scheduledWorkStart, plan_succ] using
            firstWindowUnitMean_next_le C (plan C i w k) (plan_valid C i w hs k) hh
      | true =>
          obtain ⟨signal, hstate⟩ := goodWindowEntry_halted_state C i w hs k hh
            cut ω hentry
          rw [hstate]
          have hp : plan C i w (k + 1) = plan C i w k := by
            rw [plan_succ, Plan.advance_fixed_of_halted C _ hh]
          have hw : StandaloneWork.meanDuration C (scheduledWorkStart C i w (k + 1)) = 0 :=
            StandaloneWork.halted_next_meanDuration_eq_zero C (plan C i w k) hh
          simpa only [hp, hw, zero_add] using
            firstWindowUnitMean_idle_le C (plan C i w k)
              (plan_valid C i w hs k) hh signal

theorem terminalPlanWait_le_schedule_budget (C : XCTM Q)
    (i : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (n : ℕ) (hbefore : BeforeHalt C w n) (k : ℕ) (hk : k < 4 * n) :
    terminalPlanWait C (plan C i w k) ≤
      tickWait (terminalRatioBudget i k) (terminalBackwardBudget C w k) 5 := by
  obtain ⟨ha, hf⟩ := terminal_schedule_parameters C i w hs n hbefore k hk
  have hpos : (0 : ℝ) < backwardCount C (Plan.workState C (plan C i w k)) := by
    exact_mod_cast planWork_backwardCount_pos C (plan C i w k) (plan_valid C i w hs k)
  have hr :
      (forwardCount C (Plan.workState C (plan C i w k)) : ℝ) /
          backwardCount C (Plan.workState C (plan C i w k)) = terminalRatioBudget i k :=
    (div_eq_iff (ne_of_gt hpos)).mpr ha
  unfold terminalPlanWait
  rw [hr]
  exact tickWait_antitone_backward (terminalRatioBudget_nonneg i k)
    (terminalBackwardBudget_pos C w k) hf 5

/-- Lemma 14.4's actual occupation split, with only the separately proved
raw-law restart identity as an input. -/
theorem lemmaFourteenFourOccupation_of_restart (C : XCTM Q)
    (hLemmaEightRestart : ∀ z₀, RawStateRestart C z₀) :
    LemmaFourteenFourOccupation C := by
  intro w i δ hacc n hbefore k hk
  exact (goodWindowUnitMean_le_scheduled_work_clock C i w hacc.1
    (hLemmaEightRestart (initial C i w)) k).trans
    (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (terminalPlanWait_le_schedule_budget C i w hacc.1 n hbefore k hk)))

/-- Finiteness holds at every fixed window, including the final W1 buffer
and all subsequent halted windows with accumulated idle signals. -/
theorem goodWindowUnitMean_ne_top_of_restart (C : XCTM Q)
    (i : ℕ) (w : List Bool) (hs : 3 ≤ w.length)
    (hLemmaEightRestart : RawStateRestart C (initial C i w)) (k : ℕ) :
    goodWindowUnitMean C (initial C i w) k ≠ ⊤ := by
  apply ne_top_of_le_ne_top _
    (goodWindowUnitMean_le_scheduled_work_clock C i w hs hLemmaEightRestart k)
  exact ENNReal.add_ne_top.mpr
    ⟨scheduled_workMean_ne_top C i w hs k, ENNReal.ofReal_ne_top⟩

theorem lemmaFourteenFourTailFinite_of_restart (C : XCTM Q)
    (hLemmaEightRestart : ∀ z₀, RawStateRestart C z₀) :
    LemmaFourteenFourTailFinite C := by
  intro w i δ hacc k _htail
  exact goodWindowUnitMean_ne_top_of_restart C i w hacc.1
    (hLemmaEightRestart (initial C i w)) k

end TimeAnalysis

end Ripple.sCRNUniversality.ClockedCTM.Unbounded


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded.TimeAnalysis

open Stochastic Stochastic.MassAction WindowAnalysis
open scoped BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-! Linear molecule budgets for Lemma 14.3. -/

def weightedMoleculeCount (C : XCTM Q) (weight : Sp C → ℕ)
    (x : State (Sp C)) : ℕ := ∑ s, weight s * x s

private theorem weighted_count_one (C : XCTM Q) (x : State (Sp C)) :
    weightedMoleculeCount C (fun _ => 1) x = moleculeCount C x := by
  simp [weightedMoleculeCount, moleculeCount]

private theorem weighted_count_zero (C : XCTM Q) (weight : Sp C → ℕ) :
    weightedMoleculeCount C weight 0 = 0 := by
  simp [weightedMoleculeCount]

private theorem weighted_count_add (C : XCTM Q) (weight : Sp C → ℕ)
    (x y : State (Sp C)) :
    weightedMoleculeCount C weight (x + y) =
      weightedMoleculeCount C weight x + weightedMoleculeCount C weight y := by
  simp [weightedMoleculeCount, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem weighted_count_unit (C : XCTM Q) (weight : Sp C → ℕ) (s : Sp C) :
    weightedMoleculeCount C weight (unit s) = weight s := by
  classical
  simp [weightedMoleculeCount, unit, mul_ite]

private theorem weighted_count_smul (C : XCTM Q) (weight : Sp C → ℕ)
    (n : ℕ) (x : State (Sp C)) :
    weightedMoleculeCount C weight (n • x) = n * weightedMoleculeCount C weight x := by
  induction n with
  | zero => simp [weighted_count_zero]
  | succ n ih =>
      rw [succ_nsmul, weighted_count_add, ih]
      ring

private theorem weighted_count_mul_two (C : XCTM Q) (weight : Sp C → ℕ)
    (x : State (Sp C)) :
    weightedMoleculeCount C weight ((2 : State (Sp C)) * x) =
      2 * weightedMoleculeCount C weight x := by
  simpa only [nsmul_eq_mul] using weighted_count_smul C weight 2 x

private theorem weighted_count_mul_three (C : XCTM Q) (weight : Sp C → ℕ)
    (x : State (Sp C)) :
    weightedMoleculeCount C weight ((3 : State (Sp C)) * x) =
      3 * weightedMoleculeCount C weight x := by
  simpa only [nsmul_eq_mul] using weighted_count_smul C weight 3 x

private theorem weighted_count_mul_four (C : XCTM Q) (weight : Sp C → ℕ)
    (x : State (Sp C)) :
    weightedMoleculeCount C weight ((4 : State (Sp C)) * x) =
      4 * weightedMoleculeCount C weight x := by
  simpa only [nsmul_eq_mul] using weighted_count_smul C weight 4 x

private theorem weighted_count_sum (C : XCTM Q) (weight : Sp C → ℕ)
    {ι : Type*} (t : Finset ι) (f : ι → State (Sp C)) :
    weightedMoleculeCount C weight (∑ j ∈ t, f j) =
      ∑ j ∈ t, weightedMoleculeCount C weight (f j) := by
  simp only [weightedMoleculeCount, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem moleculeCount_le_weighted (C : XCTM Q) (weight : Sp C → ℕ)
    (hw : ∀ s, 1 ≤ weight s) (x : State (Sp C)) :
    moleculeCount C x ≤ weightedMoleculeCount C weight x := by
  unfold moleculeCount weightedMoleculeCount
  apply Finset.sum_le_sum
  intro s _
  simpa only [one_mul] using Nat.mul_le_mul_right (x s) (hw s)

theorem weighted_count_fire_le (C : XCTM Q) (weight : Sp C → ℕ)
    (r : Rx C) (x : State (Sp C)) (he : (rxn C r).enabled x)
    (hproducts : weightedMoleculeCount C weight (products C r) ≤
      weight (sourceLeft C r) + weight (sourceRight C r)) :
    weightedMoleculeCount C weight ((rxn C r).fire x) ≤
      weightedMoleculeCount C weight x := by
  have hpoint (s : Sp C) :
      weight s * ((rxn C r).fire x) s + weight s * (rxn C r).l s =
        weight s * x s + weight s * products C r s := by
    have hs := he s
    change weight s * (x s - (rxn C r).l s + products C r s) +
      weight s * (rxn C r).l s = _
    have hb : x s - (rxn C r).l s + (rxn C r).l s = x s :=
      Nat.sub_add_cancel hs
    calc
      _ = weight s * (x s - (rxn C r).l s + (rxn C r).l s) +
          weight s * products C r s := by ring
      _ = _ := by rw [hb]
  have hbalance := congrArg (fun f : Sp C → ℕ => ∑ s, f s)
    (funext hpoint)
  simp only [Finset.sum_add_distrib] at hbalance
  have hl :
      weightedMoleculeCount C weight (rxn C r).l =
        weight (sourceLeft C r) + weight (sourceRight C r) := by
    change weightedMoleculeCount C weight
      (unit (sourceLeft C r) + unit (sourceRight C r)) = _
    rw [weighted_count_add, weighted_count_unit, weighted_count_unit]
  change weightedMoleculeCount C weight ((rxn C r).fire x) +
      weightedMoleculeCount C weight (rxn C r).l =
    weightedMoleculeCount C weight x +
      weightedMoleculeCount C weight (products C r) at hbalance
  rw [hl] at hbalance
  omega

private theorem weighted_count_reachable (C : XCTM Q)
    {start target : State (Sp C)} (P : WorkCertificate C start target)
    (weight : Sp C → ℕ)
    (hproducts : ∀ x, P.inv x → ∀ r, isClock r = false →
      (rxn C r).enabled x →
      weightedMoleculeCount C weight (products C r) ≤
        weight (sourceLeft C r) + weight (sourceRight C r))
    {x : State (Sp C)} (hr : WorkReach C start x) :
    weightedMoleculeCount C weight x ≤ weightedMoleculeCount C weight start := by
  have hi := workReach_invariant C
    (fun y => P.inv y ∧
      weightedMoleculeCount C weight y ≤ weightedMoleculeCount C weight start)
    (by
      rintro y z ⟨hy, hb⟩ ⟨r, hc, he, rfl⟩
      exact ⟨P.closed _ _ hy ⟨r, hc, he, rfl⟩,
        (weighted_count_fire_le C weight r y he
          (hproducts y hy r hc he)).trans hb⟩)
    hr ⟨P.initial, le_rfl⟩
  exact hi.2

-- First exclude noncontrol species from the controller, so only the target
-- species are enumerated. Keep the existing local budget for the finite sum.
set_option maxHeartbeats 600000 in
private theorem payload_decomposition (C : XCTM Q)
    (controller : Sp C) (d a : ℕ) (latent : Bool) (memory : Mem → ℕ)
    (hc : controller.IsControl) :
    payload C controller d a latent memory =
      d • unit controller +
      (if latent then 0 else a * d) • unit .forward +
      (if latent then a * (d / 3) else 0) • unit .forwardLatent +
      (if latent then 0 else d) • unit .backward +
      (if latent then d / 3 else 0) • unit .backwardLatent +
      ∑ m : Mem, memory m • unit (.mem m) := by
  have hnoncontrol (s : Sp C) (hs : ¬ s.IsControl) : s ≠ controller := by
    intro h
    exact hs (h.symm ▸ hc)
  have hforward : (.forward : Sp C) ≠ controller :=
    hnoncontrol _ (by simp [Sp.IsControl])
  have hforwardLatent : (.forwardLatent : Sp C) ≠ controller :=
    hnoncontrol _ (by simp [Sp.IsControl])
  have hbackward : (.backward : Sp C) ≠ controller :=
    hnoncontrol _ (by simp [Sp.IsControl])
  have hbackwardLatent : (.backwardLatent : Sp C) ≠ controller :=
    hnoncontrol _ (by simp [Sp.IsControl])
  have hclock (c : Fin 5) : (.clock c : Sp C) ≠ controller :=
    hnoncontrol _ (by simp [Sp.IsControl])
  have hmem (cell : Mem) : (.mem cell : Sp C) ≠ controller :=
    hnoncontrol _ (by simp [Sp.IsControl])
  funext s
  cases latent <;> cases s <;>
    simp [payload, unit, Finset.sum_apply, Pi.add_apply,
      Pi.smul_apply, nsmul_eq_mul, mul_ite, ite_apply, Pi.mul_apply,
      Pi.natCast_apply, Pi.zero_apply, hforward, hforwardLatent,
      hbackward, hbackwardLatent, hclock, hmem]

private theorem weighted_count_payload (C : XCTM Q) (weight : Sp C → ℕ)
    (controller : Sp C) (d a : ℕ) (latent : Bool) (memory : Mem → ℕ)
    (hc : controller.IsControl) :
    weightedMoleculeCount C weight (payload C controller d a latent memory) =
      d * weight controller +
      (if latent then 0 else a * d) * weight .forward +
      (if latent then a * (d / 3) else 0) * weight .forwardLatent +
      (if latent then 0 else d) * weight .backward +
      (if latent then d / 3 else 0) * weight .backwardLatent +
      ∑ m : Mem, memory m * weight (.mem m) := by
  rw [payload_decomposition C controller d a latent memory hc]
  simp only [weighted_count_add, weighted_count_smul,
    weighted_count_unit, weighted_count_sum]

private theorem mem_univ_volume :
    (Finset.univ : Finset Mem) =
      {.m, .md, .ms, .t, .td, .ts, .d, .ds, .k1, .k2, .b, .bs} := by
  ext m
  cases m <;> simp

private theorem volume_tape_data (w : List Bool) (hs : 3 ≤ w.length) :
    9 ≤ stateCount w.length ∧ tval w < 3 * stateCount w.length ∧
      threshold w.length ≤ 3 * stateCount w.length ∧
      9 * threshold w.length = 20 * stateCount w.length := by
  have hp : 0 < 3 ^ (w.length - 3) := by positivity
  have hv := (tape_facts (n := w.length - 3) (w := w) (by omega) false).2.2.2.2.2
  rw [stateCount_eq w.length hs, threshold_eq w.length hs]
  omega

private theorem moleculeCount_add (C : XCTM Q) (x y : State (Sp C)) :
    moleculeCount C (x + y) = moleculeCount C x + moleculeCount C y := by
  simp [moleculeCount, Pi.add_apply, Finset.sum_add_distrib]

theorem moleculeCount_eq_work_add_clock (C : XCTM Q) (x : State (Sp C)) :
    moleculeCount C x = moleculeCount C (workView C x) + clockMoleculeCount C x := by
  have he :
      x = workView C x + ∑ c : Fin 5, x (.clock c) • unit (.clock c) := by
    funext s
    cases s <;>
      simp [workView, unit, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, mul_ite]
  calc
    moleculeCount C x =
        moleculeCount C (workView C x + ∑ c : Fin 5, x (.clock c) • unit (.clock c)) :=
      congrArg (moleculeCount C) he
    _ = moleculeCount C (workView C x) + clockMoleculeCount C x := by
      rw [moleculeCount_add, ← weighted_count_one C
        (∑ c : Fin 5, x (.clock c) • unit (.clock c)), weighted_count_sum]
      simp only [weighted_count_smul, weighted_count_unit, mul_one]
      rfl


def restoreVolumeWeight (C : XCTM Q) : Sp C → ℕ
  | .forwardLatent | .backwardLatent => 3
  | .mem .ds => 2
  | _ => 1

def readVolumeWeight (C : XCTM Q) : Sp C → ℕ
  | .mem .m | .mem .ms | .mem .t | .mem .ts => 3
  | .mem .d => 4
  | .mem .b => 3
  | _ => 1

def extensionVolumeWeight (C : XCTM Q) (e : ExtendState C) : Sp C → ℕ
  | .third q => if q = .inr e then 3 else 1
  | .mem .m | .mem .ms | .mem .t | .mem .ts | .mem .d => 3
  | .mem .b => 2
  | _ => 1

private theorem restoreVolumeWeight_pos (C : XCTM Q) (s : Sp C) :
    1 ≤ restoreVolumeWeight C s := by
  cases s with
  | mem m => cases m <;> simp [restoreVolumeWeight]
  | _ => simp [restoreVolumeWeight]

private theorem readVolumeWeight_pos (C : XCTM Q) (s : Sp C) :
    1 ≤ readVolumeWeight C s := by
  cases s with
  | mem m => cases m <;> simp [readVolumeWeight]
  | _ => simp [readVolumeWeight]

private theorem extensionVolumeWeight_pos (C : XCTM Q) (e : ExtendState C) (s : Sp C) :
    1 ≤ extensionVolumeWeight C e s := by
  cases s with
  | mem m => cases m <;> simp [extensionVolumeWeight]
  | third q =>
      change 1 ≤ (if q = Sum.inr e then 3 else 1)
      split_ifs <;> omega
  | _ => simp [extensionVolumeWeight]

private theorem restore_volume_products (C : XCTM Q) (r : Rx C)
    (hr : RestoreLabel r) :
    weightedMoleculeCount C (restoreVolumeWeight C) (products C r) ≤
      restoreVolumeWeight C (sourceLeft C r) + restoreVolumeWeight C (sourceRight C r) := by
  cases r <;>
    simp_all [RestoreLabel, products, sourceLeft, sourceRight, restoreVolumeWeight,
      weighted_count_add, weighted_count_smul, weighted_count_mul_two, weighted_count_mul_three, weighted_count_mul_four,
      weighted_count_unit, weighted_count_zero]

private def ReadVolumeLabel {C : XCTM Q} : Rx C → Prop
  | .startRead _ | .chooseRead _ _ | .growWrite _ _ |
      .readRestoreM _ _ | .readRestoreTs _ _ | .readRestoreT _ _ |
      .readShift _ _ | .readZero _ _ | .readWrite _ _ |
      .pair | .consumeSingle | .consumeDouble => True
  | _ => False

private theorem read_volume_label (C : XCTM Q)
    {m T g v v' : ℕ} {q : ReadState C} {b : Bool} {x : State (Sp C)}
    (hx : ReadWindow C m T g q b v v' x)
    (r : Rx C) (hc : isClock r = false) (he : (rxn C r).enabled x) :
    ReadVolumeLabel r := by
  rcases hx with ⟨hO, hI, hs, hM⟩ | ⟨hO, hR, hs, hM⟩ | ⟨hO, hs, hu, hM⟩
  · have hr := read_start_enabled C hO hM r hc he
    subst r
    trivial
  · have hr := read_choose_enabled C hO hM r hc he
    subst r
    trivial
  · have hr := read_work_enabled C hO r hc he
    simp only [readWorkLabels, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

private theorem read_volume_products (C : XCTM Q) (r : Rx C)
    (hr : ReadVolumeLabel r) :
    weightedMoleculeCount C (readVolumeWeight C) (products C r) ≤
      readVolumeWeight C (sourceLeft C r) + readVolumeWeight C (sourceRight C r) := by
  cases r with
  | chooseRead q b =>
      cases b <;>
        simp [products, sourceLeft, sourceRight, readVolumeWeight,
          weighted_count_add, weighted_count_smul, weighted_count_mul_two, weighted_count_mul_three, weighted_count_mul_four,
          weighted_count_unit]
  | readZero q b =>
      cases b <;>
        simp [products, sourceLeft, sourceRight, readVolumeWeight,
          weighted_count_add, weighted_count_smul, weighted_count_mul_two, weighted_count_mul_three, weighted_count_mul_four,
          weighted_count_unit]
  | readWrite q b =>
      cases hb : (C.next q.val b).2 <;>
        simp [products, sourceLeft, sourceRight, readVolumeWeight, hb, Bool.toNat,
          weighted_count_add, weighted_count_smul, weighted_count_mul_two, weighted_count_mul_three, weighted_count_mul_four,
          weighted_count_unit]
  | _ =>
      simp_all [ReadVolumeLabel, products, sourceLeft, sourceRight, readVolumeWeight,
        weighted_count_add, weighted_count_smul, weighted_count_mul_two, weighted_count_mul_three, weighted_count_mul_four,
        weighted_count_unit, weighted_count_zero]

private theorem extension_volume_products (C : XCTM Q) (e : ExtendState C)
    (r : Rx C) (hr : ExtensionLabel C e r) :
    weightedMoleculeCount C (extensionVolumeWeight C e) (products C r) ≤
      extensionVolumeWeight C e (sourceLeft C r) +
        extensionVolumeWeight C e (sourceRight C r) := by
  unfold ExtensionLabel at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [products, sourceLeft, sourceRight, extensionVolumeWeight,
      weighted_count_add, weighted_count_smul, weighted_count_mul_two, weighted_count_mul_three, weighted_count_mul_four,
      weighted_count_unit]

private theorem buffer_volume_products (C : XCTM Q) (b : Buffer C)
    (r : Rx C) (hr : r = Buffer.seed C b ∨ r = Buffer.grow C b) :
    weightedMoleculeCount C (fun _ => 1) (products C r) ≤ 1 + 1 := by
  rcases hr with rfl | rfl <;> cases b <;>
    simp [Buffer.seed, Buffer.grow, products,
      weighted_count_smul, weighted_count_mul_two, weighted_count_mul_three, weighted_count_mul_four, weighted_count_unit]

private theorem restore_volume_start (C : XCTM Q) (q : Q)
    (w : List Bool) (accuracy a : ℕ) (latent : Bool) (hs : 3 ≤ w.length)
    (ha : accuracy ≤ a) :
    weightedMoleculeCount C (restoreVolumeWeight C)
        (Plan.workState C (.first q w accuracy latent) + unit .signal) + 1 ≤
      (a + 24) * stateCount w.length := by
  obtain ⟨hd, hv, ht, hrel⟩ := volume_tape_data w hs
  have hdiv := stateCount_div_exact w.length hs
  have hmul := Nat.mul_le_mul_right (stateCount w.length) ha
  have hdivmul :
      3 * (accuracy * (stateCount w.length / 3)) = accuracy * stateCount w.length := by
    nlinarith [congrArg (fun n : ℕ => accuracy * n) hdiv]
  cases latent <;>
    simp [Plan.workState, weighted_count_add, weighted_count_unit,
      weighted_count_payload, Sp.IsControl, restoreVolumeWeight, storedMemory,
      mem_univ_volume] <;> nlinarith

private theorem read_volume_start (C : XCTM Q) (q : ReadState C)
    (w : List Bool) (accuracy a : ℕ) (hs : 3 ≤ w.length)
    (ha : accuracy ≤ a + 1) :
    weightedMoleculeCount C (readVolumeWeight C)
        (Plan.workState C (.third (.inl q) w accuracy) + unit .signal) + 1 ≤
      (a + 24) * stateCount w.length := by
  obtain ⟨hd, hv, ht, hrel⟩ := volume_tape_data w hs
  have hmul := Nat.mul_le_mul_right (stateCount w.length) ha
  have hm := Nat.sub_add_cancel (min_le_left (tval w) (threshold w.length))
  have hT := Nat.sub_add_cancel (min_le_right (tval w) (threshold w.length))
  simp [Plan.workState, weighted_count_add, weighted_count_unit,
    weighted_count_payload, Sp.IsControl, readVolumeWeight, comparedMemory,
    mem_univ_volume]
  nlinarith

private theorem extension_volume_start (C : XCTM Q) (e : ExtendState C)
    (w : List Bool) (accuracy a : ℕ) (hs : 3 ≤ w.length)
    (ha : accuracy ≤ a + 1) :
    weightedMoleculeCount C (extensionVolumeWeight C e)
        (Plan.workState C (.third (.inr e) w accuracy) + unit .signal) + 1 ≤
      (a + 24) * stateCount w.length := by
  obtain ⟨hd, hv, ht, hrel⟩ := volume_tape_data w hs
  have hvSucc : tval w + 1 ≤ 3 * stateCount w.length := Nat.succ_le_of_lt hv
  have hmul := Nat.mul_le_mul_right (stateCount w.length) ha
  have hm := Nat.sub_add_cancel (min_le_left (tval w) (threshold w.length))
  have hT := Nat.sub_add_cancel (min_le_right (tval w) (threshold w.length))
  simp [Plan.workState, weighted_count_add, weighted_count_unit,
    weighted_count_payload, Sp.IsControl, extensionVolumeWeight, comparedMemory,
    mem_univ_volume]
  nlinarith


/-- The restoration phase uses the old accuracy; the other phases use
the incremented accuracy. -/
def VolumeAccuracyBound (C : XCTM Q) : Plan C → ℕ → Prop
  | .first _ _ accuracy _, a => accuracy ≤ a
  | .second _ _ accuracy, a | .third _ _ accuracy, a |
      .write _ _ _ accuracy, a | .extend _ _ accuracy, a => accuracy ≤ a + 1

private theorem volumeAccuracyBound_mono (C : XCTM Q) (p : Plan C)
    {a b : ℕ} (hab : a ≤ b) (ha : VolumeAccuracyBound C p a) :
    VolumeAccuracyBound C p b := by
  cases p <;> simp only [VolumeAccuracyBound] at * <;> omega

private theorem first_cycle_volume_data (C : XCTM Q) (q : Q) (w : List Bool)
    (a : ℕ) (latent : Bool) (hh : C.mode q ≠ .halt)
    (r : ℕ) (hr : r < 4) :
    Plan.halted C (Plan.iterate C (.first q w a latent) r) = false ∧
      VolumeAccuracyBound C (Plan.iterate C (.first q w a latent) r) a := by
  cases hmode : C.mode q with
  | read =>
      have hfirst :
          Plan.advance C (.first q w a latent) =
            .second (.inl ⟨q, hmode⟩) w (a + 1) := by
        dsimp only [Plan.advance]
        split <;> first
          | rfl
          | (exfalso; rename_i hm; rw [hmode] at hm; cases hm)
          | simp_all
      interval_cases r <;> simp only [Plan.iterate, hfirst] <;>
        simp [Plan.advance, Plan.halted, hmode, VolumeAccuracyBound]
  | extend q' =>
      have hfirst :
          Plan.advance C (.first q w a latent) =
            .second (.inr ⟨q, ⟨q', hmode⟩⟩) w (a + 1) := by
        dsimp only [Plan.advance]
        split <;> first
          | rfl
          | (exfalso; rename_i hm; rw [hmode] at hm; cases hm)
          | simp_all
      interval_cases r <;> simp only [Plan.iterate, hfirst] <;>
        simp [Plan.advance, Plan.halted, hmode, VolumeAccuracyBound]
  | halt => exact False.elim (hh hmode)

theorem scheduled_volume_data (C : XCTM Q) (i : ℕ) (w : List Bool)
    (hs : 3 ≤ w.length) (n : ℕ) (hbefore : BeforeHalt C w n)
    (m : ℕ) (hm : m < 4 * n) :
    Plan.halted C (plan C i w m) = false ∧
      VolumeAccuracyBound C (plan C i w m) (i + m / 4) := by
  have hquot : m / 4 < n := by omega
  have hp := plan_at_step C i w hs (m / 4)
    (fun j hj => hbefore j (lt_trans hj hquot))
  have hd := first_cycle_volume_data C
    (C.runT (C.start, w) (m / 4)).1 (C.runT (C.start, w) (m / 4)).2
    (i + m / 4) (previousExtension C w (m / 4))
    (hbefore (m / 4) hquot) (m % 4) (Nat.mod_lt _ (by norm_num))
  have he : 4 * (m / 4) + m % 4 = m := by omega
  rw [← hp, ← plan_add, he] at hd
  exact hd


private theorem plain_volume_stored (C : XCTM Q) (controller : Sp C)
    (w : List Bool) (accuracy a : ℕ) (latent : Bool)
    (hs : 3 ≤ w.length) (hc : controller.IsControl) (ha : accuracy ≤ a + 1) :
    weightedMoleculeCount C (fun _ => 1)
        (payload C controller (stateCount w.length) accuracy latent (storedMemory w) +
          unit .signal) + 1 ≤ (a + 24) * stateCount w.length := by
  obtain ⟨hd, hv, ht, hrel⟩ := volume_tape_data w hs
  have hmul := Nat.mul_le_mul_right (stateCount w.length) ha
  have hdiv : stateCount w.length / 3 ≤ stateCount w.length := Nat.div_le_self _ _
  have hlat := Nat.mul_le_mul_left accuracy hdiv
  rw [weighted_count_add, weighted_count_unit,
    weighted_count_payload C _ _ _ _ _ _ hc]
  cases latent <;> simp [storedMemory, mem_univ_volume] <;> nlinarith

private theorem plain_volume_compared (C : XCTM Q) (controller : Sp C)
    (w : List Bool) (accuracy a : ℕ)
    (hs : 3 ≤ w.length) (hc : controller.IsControl) (ha : accuracy ≤ a + 1) :
    weightedMoleculeCount C (fun _ => 1)
        (payload C controller (stateCount w.length) accuracy false (comparedMemory w) +
          unit .signal) + 1 ≤ (a + 24) * stateCount w.length := by
  obtain ⟨hd, hv, ht, hrel⟩ := volume_tape_data w hs
  have hmul := Nat.mul_le_mul_right (stateCount w.length) ha
  have hm := Nat.sub_add_cancel (min_le_left (tval w) (threshold w.length))
  have hT := Nat.sub_add_cancel (min_le_right (tval w) (threshold w.length))
  rw [weighted_count_add, weighted_count_unit,
    weighted_count_payload C _ _ _ _ _ _ hc]
  simp [comparedMemory, mem_univ_volume]
  nlinarith

private theorem buffer_volume_start (C : XCTM Q) (b : Buffer C) (a : ℕ)
    (hs : 3 ≤ (Buffer.before C b).tape.length)
    (ha : VolumeAccuracyBound C (Buffer.before C b) a) :
    weightedMoleculeCount C (fun _ => 1)
        (Plan.workState C (Buffer.before C b) + unit .signal) + 1 ≤
      (a + 24) * stateCount (Buffer.before C b).tape.length := by
  cases b with
  | fromRead q bit w accuracy =>
      exact plain_volume_stored C (.write q bit) w accuracy a false hs (by trivial) ha
  | fromExtension e w accuracy =>
      exact plain_volume_stored C (.extend e) w accuracy a true hs (by trivial) ha
  | toThird q w accuracy =>
      exact plain_volume_compared C (.second q) w accuracy a hs (by trivial) ha

private theorem buffer_work_volume_le (C : XCTM Q) (b : Buffer C) (a : ℕ)
    (hs : 3 ≤ (Buffer.before C b).tape.length)
    (ha : VolumeAccuracyBound C (Buffer.before C b) a)
    {x : State (Sp C)}
    (hr : WorkReach C (Plan.workState C (Buffer.before C b) + unit .signal) x) :
    moleculeCount C x + 1 ≤ (a + 24) * stateCount (Buffer.before C b).tape.length := by
  have hcount := weighted_count_reachable C (bufferCertificate C b) (fun _ => 1)
    (fun y hy r hc he =>
      buffer_volume_products C b r (buffer_enabled C hy hc he)) hr
  have hstart := buffer_volume_start C b a hs ha
  simp only [weighted_count_one] at hcount hstart
  omega

private theorem restore_work_volume_le (C : XCTM Q) (q : ActiveState C)
    (w : List Bool) (accuracy a : ℕ) (latent : Bool)
    (hs : 3 ≤ w.length) (ha : accuracy ≤ a)
    {x : State (Sp C)}
    (hr : WorkReach C
      (Plan.workState C (.first (activeControl C q) w accuracy latent) + unit .signal) x) :
    moleculeCount C x + 1 ≤ (a + 24) * stateCount w.length := by
  have hcount := weighted_count_reachable C
    (restoreCertificate C q w accuracy latent hs) (restoreVolumeWeight C)
    (fun y hy r hc he =>
      restore_volume_products C r (restoreAt_label (restore_enabled_at C hy hc he))) hr
  change weightedMoleculeCount C (restoreVolumeWeight C) x ≤
    weightedMoleculeCount C (restoreVolumeWeight C)
      (Plan.workState C (.first (activeControl C q) w accuracy latent) +
        unit .signal) at hcount
  have hactual := moleculeCount_le_weighted C (restoreVolumeWeight C)
    (restoreVolumeWeight_pos C) x
  have hstart := restore_volume_start C (activeControl C q) w accuracy a latent hs ha
  exact (Nat.add_le_add_right (hactual.trans hcount) 1).trans hstart

private theorem read_work_volume_le (C : XCTM Q) (q : ReadState C)
    (w : List Bool) (accuracy a : ℕ) (hs : 3 ≤ w.length)
    (ha : accuracy ≤ a + 1) {x : State (Sp C)}
    (hr : WorkReach C (Plan.workState C (.third (.inl q) w accuracy) + unit .signal) x) :
    moleculeCount C x + 1 ≤ (a + 24) * stateCount w.length := by
  have hcount := weighted_count_reachable C (readCertificate C q w accuracy hs)
    (readVolumeWeight C)
    (fun y hy r hc he => read_volume_products C r
      (read_volume_label C hy.1 r hc he)) hr
  have hactual := moleculeCount_le_weighted C (readVolumeWeight C)
    (readVolumeWeight_pos C) x
  have hstart := read_volume_start C q w accuracy a hs ha
  omega

private theorem extension_work_volume_le (C : XCTM Q) (e : ExtendState C)
    (w : List Bool) (accuracy a : ℕ) (hs : 3 ≤ w.length)
    (ha : accuracy ≤ a + 1) {x : State (Sp C)}
    (hr : WorkReach C (Plan.workState C (.third (.inr e) w accuracy) + unit .signal) x) :
    moleculeCount C x + 1 ≤ (a + 24) * stateCount w.length := by
  have hcount := weighted_count_reachable C (extensionCertificate C e w accuracy hs)
    (extensionVolumeWeight C e)
    (fun y hy r hc he => extension_volume_products C e r
      (extension_enabled_label C e _ _ _ _ _ y hy r hc he)) hr
  have hactual := moleculeCount_le_weighted C (extensionVolumeWeight C e)
    (extensionVolumeWeight_pos C e) x
  have hstart := extension_volume_start C e w accuracy a hs ha
  omega

/-- A work interval, together with its one clock molecule, satisfies
the sharp Lemma 14.3 budget. -/
theorem workReach_volume_le (C : XCTM Q) (p : Plan C) (a : ℕ)
    (hs : 3 ≤ p.tape.length) (hh : Plan.halted C p = false)
    (ha : VolumeAccuracyBound C p a) {x : State (Sp C)}
    (hr : WorkReach C (Plan.workState C p + unit .signal) x) :
    moleculeCount C x + 1 ≤ (a + 24) * stateCount p.tape.length := by
  cases p with
  | first q w accuracy latent =>
      cases hm : C.mode q with
      | read =>
          exact restore_work_volume_le C (.inl ⟨q, hm⟩) w accuracy a latent hs ha hr
      | extend q' =>
          exact restore_work_volume_le C (.inr ⟨q, ⟨q', hm⟩⟩)
            w accuracy a latent hs ha hr
      | halt => simp [Plan.halted, hm] at hh
  | second q w accuracy =>
      exact buffer_work_volume_le C (.toThird q w accuracy) a hs ha hr
  | third q w accuracy =>
      cases q with
      | inl q => exact read_work_volume_le C q w accuracy a hs ha hr
      | inr e => exact extension_work_volume_le C e w accuracy a hs ha hr
  | write q bit w accuracy =>
      exact buffer_work_volume_le C (.fromRead q bit w accuracy) a hs ha hr
  | extend e w accuracy =>
      exact buffer_work_volume_le C (.fromExtension e w accuracy) a hs ha hr


/-- The molecule-count premise of Lemma 14.3 follows pathwise from the
good-prefix invariant. No probabilistic restart hypothesis is needed. -/
theorem lemmaFourteenThreeVolume (C : XCTM Q) : LemmaFourteenThreeVolume C := by
  intro w i δ hacc n hbefore k hk j ω hactive
  have hwindow := window_of_noBadTick_before C i w hacc.1 ω j hactive.2
  rw [hactive.1] at hwindow
  have hclockInitial : clockMoleculeCount C (initial C i w) = 1 := by
    change (∑ c : Fin 5, if c = Fin.last 4 then (1 : ℕ) else 0) = 1
    norm_num [Fin.sum_univ_succ]
  have hclock := clockMoleculeCount_path_one C (initial C i w) hclockInitial ω j
  have hnat :
      moleculeCount C (pathState (net C) (initial C i w) ω j) ≤
        (i + k / 4 + 24) * stateCount (C.runT (C.start, w) (k / 4)).2.length := by
    cases k with
    | zero =>
        change workView C (pathState (net C) (initial C i w) ω j) =
          gamma C i w 0 at hwindow
        have hweight := moleculeCount_le_weighted C (restoreVolumeWeight C)
          (restoreVolumeWeight_pos C) (Plan.workState C (.first C.start w i false))
        have hstart := restore_volume_start C C.start w i i false hacc.1 le_rfl
        simp only [weighted_count_add, weighted_count_unit, restoreVolumeWeight] at hstart
        rw [moleculeCount_eq_work_add_clock, hclock, hwindow]
        change moleculeCount C (Plan.workState C (.first C.start w i false)) + 1 ≤
          (i + 24) * stateCount w.length
        omega
    | succ m =>
        obtain ⟨hh, ha⟩ := scheduled_volume_data C i w hacc.1 n hbefore m (by omega)
        have hreach : WorkReach C
            (Plan.workState C (plan C i w m) + unit .signal)
            (workView C (pathState (net C) (initial C i w) ω j)) := by
          simpa only [Window, hh, Bool.false_eq_true, ↓reduceIte, gamma] using hwindow
        have hcount := workReach_volume_le C (plan C i w m) (i + (m + 1) / 4)
          (plan_valid C i w hacc.1 m) hh
          (volumeAccuracyBound_mono C _ (by omega) ha) hreach
        have he : 4 * ((m + 1) / 4) + (m + 1) % 4 = m + 1 := by omega
        have htape := next_window_schedule_tape C i w hacc.1
          ((m + 1) / 4) ((m + 1) % 4) (Nat.mod_lt _ (by norm_num))
          (by rw [he]; omega)
          (by rw [he, Nat.add_sub_cancel]; exact hh)
        rw [he, Nat.add_sub_cancel] at htape
        rw [htape] at hcount
        rw [moleculeCount_eq_work_add_clock, hclock]
        exact hcount
  unfold windowAccuracy windowPopulation
  exact_mod_cast hnat

end Ripple.sCRNUniversality.ClockedCTM.Unbounded.TimeAnalysis


namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded

open Stochastic Stochastic.MassAction
open scoped ENNReal

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The three clock/volume inputs of the old combined reducer. -/
theorem clock_note_estimates_of_restart (C : XCTM Q)
    (hLemmaEightRestart : ∀ z₀, RawStateRestart C z₀) :
    TimeAnalysis.LemmaFourteenFourOccupation C ∧
      TimeAnalysis.LemmaFourteenFourTailFinite C ∧
        TimeAnalysis.LemmaFourteenThreeVolume C :=
  ⟨TimeAnalysis.lemmaFourteenFourOccupation_of_restart C hLemmaEightRestart,
    TimeAnalysis.lemmaFourteenFourTailFinite_of_restart C hLemmaEightRestart,
    TimeAnalysis.lemmaFourteenThreeVolume C⟩

/-- All-window progress now needs no quantitative work estimate. -/
theorem allGoodWindowMeansFinite_of_restart (C : XCTM Q)
    (hLemmaEightRestart : ∀ z₀, RawStateRestart C z₀) :
    AllGoodWindowMeansFinite C := by
  intro w i δ hacc k
  exact TimeAnalysis.goodWindowUnitMean_ne_top_of_restart C i w hacc.1
    (hLemmaEightRestart (initial C i w)) k

/-- The error reducer retains exactly the phase and restart inputs provided
by the separate Markov file. -/
theorem errorClaim_of_phases_and_restart (C : XCTM Q)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (hLemmaEightRestart : ∀ z₀, RawStateRestart C z₀) :
    ErrorClaim C :=
  errorClaim_of_note_window_estimates C hLemmaEightFour_phases
    (fun _w _i _δ _hacc => hLemmaEightRestart _)
    (allGoodWindowMeansFinite_of_restart C hLemmaEightRestart)

namespace TimeAnalysis

/-- The original unit-time premise, with occupation discharged. -/
theorem unitTime_of_phases_and_restart (C : XCTM Q)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (hLemmaEightRestart : ∀ z₀, RawStateRestart C z₀)
    (w : List Bool) (i : ℕ) (δ : ℝ) (hacc : AdmissibleAccuracy w i δ)
    (n : ℕ) (hbefore : BeforeHalt C w n) (k : ℕ) (hk : k < 4 * n) :
    goodWindowUnitMean C (initial C i w) k ≤
      ENNReal.ofReal ((27 / 8 : ℝ) * (windowAccuracy i k + 1) ^ 4 /
        windowPopulation C w k) :=
  unitTime_of_phase_and_occupation_estimates C hLemmaEightFour_phases
    (lemmaFourteenFourOccupation_of_restart C hLemmaEightRestart)
    w i δ hacc n hbefore k hk

end TimeAnalysis

/-- The three clock/volume inputs are discharged. This reducer retains the
phase and restart arguments for reuse; the final corollaries supply both. -/
theorem error_and_timeClaims_of_phases_and_restart (C : XCTM Q)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (hLemmaEightRestart : ∀ z₀, RawStateRestart C z₀) :
    ErrorClaim C ∧ TimeClaim C :=
  error_and_timeClaims_of_note_estimates C hLemmaEightFour_phases
    (fun _w _i _δ _hacc => hLemmaEightRestart _)
    (TimeAnalysis.lemmaFourteenThreeVolume C)
    (TimeAnalysis.lemmaFourteenFourOccupation_of_restart C hLemmaEightRestart)
    (TimeAnalysis.lemmaFourteenFourTailFinite_of_restart C hLemmaEightRestart)

theorem timeClaim_of_phases_and_restart (C : XCTM Q)
    (hLemmaEightFour_phases : LemmaEightFourPhases C)
    (hLemmaEightRestart : ∀ z₀, RawStateRestart C z₀) :
    TimeClaim C :=
  (error_and_timeClaims_of_phases_and_restart C
    hLemmaEightFour_phases hLemmaEightRestart).2


/-- SCWB Theorem 7.1 for every XCTM: the phase, restart, occupation,
and tail-finiteness inputs are supplied by the proved mechanisms above. -/
theorem errorClaim (C : XCTM Q) : ErrorClaim C :=
  errorClaim_of_phases_and_restart C
    (lemmaEightFourPhases C) (rawStateRestart C)

/-- SCWB Theorem 7.2 for every XCTM, with the physical-time constant
and accuracy dependence in the existing TimeClaim definition. -/
theorem timeClaim (C : XCTM Q) : TimeClaim C :=
  timeClaim_of_phases_and_restart C
    (lemmaEightFourPhases C) (rawStateRestart C)

/-- The TM form of the physical-time estimate, with the existing
552 coefficient and precision/space polynomial. -/
theorem tmTimeClaim
    {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) : TMTimeClaim M :=
  TimeAnalysis.tmTimeClaim_of_timeClaim M (timeClaim (xctmOf M))

/-- The TM simulation-failure bound with the XCTM ErrorClaim discharged.
The blank-symbol, input-length, and accuracy conditions are exactly those
of the existing TM correctness corollary. -/
theorem tm_failure_bound
    {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) (hb : M.blank = false)
    (s i₀ : ℕ) (input : List Bool)
    (hs : 1 ≤ s) (hi : input.length ≤ s) {δ : ℝ}
    (hacc : AdmissibleAccuracy (xencT (xInputTape s input)) i₀ δ) :
    jumpLaw (xctmOf M) i₀ (xencT (xInputTape s input))
        {ω | ¬ TMSimulatesAll M s i₀ input ω} ≤
      ENNReal.ofReal (errorBound i₀) :=
  tm_failure_bound_of_errorClaim M hb s i₀ input hs hi hacc
    (errorClaim (xctmOf M))

/-- **SCWB Theorem 4.1** (Soloveichik, Cook, Winfree, Bruck, "Computation with finite
stochastic chemical reaction networks", Caltech TR etr085v2 / Nat. Comput. 7 (2008),
Theorem 4.1), for the repaired network of `docs/audit/FIX3-SCWB-T41.md`.

The network `xctmOf M` depends only on the machine `M`. For every space bound `s ≥ 1` and
accuracy `0 < δ ≤ 1`, the initial accuracy count `i₀ = accuracyIndex (2 s + 2) δ` (at most
`2 s + 4 + 37/√δ`) makes, for every input of length at most `s`, the probability that the
reaction path fails to visit a clean encoding of every configuration of the unbounded TM run
at most `1344/(i₀ - 1)² ≤ δ`; unboundedly many steps and unbounded space are covered.
The second conjunct is the physical-time estimate `TMTimeClaim M`. -/
theorem scwb_theorem_4_1
    {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) (hb : M.blank = false)
    (s : ℕ) (hs : 1 ≤ s) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    (∀ input : List Bool, input.length ≤ s →
      jumpLaw (xctmOf M) (accuracyIndex (2 * s + 2) δ) (xencT (xInputTape s input))
          {ω | ¬ TMSimulatesAll M s (accuracyIndex (2 * s + 2) δ) input ω} ≤
        ENNReal.ofReal (errorBound (accuracyIndex (2 * s + 2) δ)) ∧
      errorBound (accuracyIndex (2 * s + 2) δ) ≤ δ) ∧
    TMTimeClaim M := by
  refine ⟨fun input hi => ?_, tmTimeClaim M⟩
  have hlen := xInputTape_encoding_length s input hs hi
  have hacc := TimeAnalysis.accuracyIndex_admissible (xencT (xInputTape s input)) δ
    (by rw [hlen]; omega) hδ hδone
  rw [hlen] at hacc
  exact ⟨tm_failure_bound M hb s _ input hs hi hacc,
    (errorClaim (xctmOf M) _ _ δ hacc).2.1⟩

end Ripple.sCRNUniversality.ClockedCTM.Unbounded

-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedNonlinearService.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedNonlinearScalar
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingStoppedDebtLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingServiceProbability

/-!
# First-barrier nonlinear service on the physical scheduler

A failed current-state gate kills the integer debt on the same sampled
step. Recorded-prefix bounds are then spliced under law init, including at
genuine pair-log stopping times. No future-success event is conditioned on.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem PairLog PhaseOneDrain AveragingRecordedExpectation AveragingRecordedSplice
open AveragingStoppedDebt AveragingServiceProbability

variable {L K : ℕ}

open Classical in
/-- Helper: a function bounded by one on a countable discrete space is integrable;
unlike `indicator_integrable` it does not fix the decidability instance. -/
private theorem integrable_of_abs_le_one {α : Type*} [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    Integrable f μ :=
  (integrable_const (1 : ℝ)).mono' (measurable_of_countable f).aestronglyMeasurable
    (ae_of_all μ fun x => by rw [Real.norm_eq_abs]; exact hf x)

open Classical in
/-- The conditional death inequality is derived from the actual sampled draw,
including killing on the sampled step which first fails the gate. -/
theorem stoppedDebt_conditional_nonlinear_death
    (init : Cfg L K) (s : ℕ) (p : (i : Finset.Iic s) → Draw L K)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop) (M : ℕ) (N : ℝ)
    (hservice : ∀ c, W c →
      nonlinearServiceRate N (Nat.ceil (F c - A)) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (t : ℕ) :
    (fun ω => nonlinearServiceRate N (stoppedDebt init s F A W M t ω))
      ≤ᵐ[recordedFuture init s p]
        (recordedFuture init s p)[fun ω => if stoppedDebt init s F A W M (t + 1) ω <
              stoppedDebt init s F A W M t ω then (1 : ℝ) else 0 |
            shiftedPairLog L K s t] := by
  classical
  have hA := measurableSet_debtLive init s F A W M t
  rw [pairLogFiltration_eq_comap] at hA
  obtain ⟨B, -, hB⟩ := hA
  have hmem (ω : Ω L K) :
      frestrictLe (π := fun _ : ℕ => Draw L K) (s + t) ω ∈ B ↔
        DebtLive init s F A W M t ω := by
    change ω ∈ frestrictLe (π := fun _ : ℕ => Draw L K) (s + t) ⁻¹' B ↔ _
    rw [hB]
    rfl
  let H : ((i : Finset.Iic (s + t)) → Draw L K) → Draw L K → ℝ :=
    fun r d =>
      if (if r ∈ B ∧ W (applyDraw (prefixCfg init (s + t) r) d)
          then Nat.ceil (F (applyDraw (prefixCfg init (s + t) r) d) - A)
          else 0) <
        (if r ∈ B then Nat.ceil (F (prefixCfg init (s + t) r) - A) else 0)
      then 1 else 0
  have hH : ∀ r d, |H r d| ≤ 1 := by
    intro r d
    dsimp [H]
    split_ifs <;> norm_num
  have heq : recordedNext (s + t) H =
      (fun ω => if stoppedDebt init s F A W M (t + 1) ω <
          stoppedDebt init s F A W M t ω then (1 : ℝ) else 0) := by
    funext ω
    rw [stoppedDebt_succ]
    dsimp only [recordedNext, H]
    rw [hmem]
    rfl
  have hce := recordedNext_condExp init s (s + t) (by omega) p H 1 hH
  rw [heq] at hce
  filter_upwards [hce] with ω hω
  change nonlinearServiceRate N (stoppedDebt init s F A W M t ω) ≤ _
  refine le_of_le_of_eq ?_ hω.symm
  let c := trace init ω (s + t)
  let r := frestrictLe (π := fun _ : ℕ => Draw L K) (s + t) ω
  have hcfg : prefixCfg init (s + t) r = c := rfl
  change nonlinearServiceRate N (stoppedDebt init s F A W M t ω) ≤
    ∫ d, H r d ∂(drawLaw c).toMeasure
  by_cases hlive : DebtLive init s F A W M t ω
  · have hr : r ∈ B := (hmem ω).mpr hlive
    rw [stoppedDebt, if_pos hlive]
    change nonlinearServiceRate N (Nat.ceil (F c - A)) ≤ _
    have hw : W c := hlive.2 t le_rfl
    by_cases hpos : 0 < Nat.ceil (F c - A)
    · refine (hservice c hw).trans ?_
      refine integral_mono (integrable_of_abs_le_one _ _ (fun d => ?_))
        (integrable_of_abs_le_one _ _ (hH r)) ?_
      · split_ifs <;> norm_num
      intro d
      beta_reduce
      by_cases hd : ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
      · rw [if_pos hd]
        have hH1 : H r d =
            if (if r ∈ B ∧ W (applyDraw c d)
                then Nat.ceil (F (applyDraw c d) - A) else 0) <
              Nat.ceil (F c - A) then 1 else 0 := by
          dsimp only [H]
          rw [hcfg, if_pos hr]
        have hlt : (if r ∈ B ∧ W (applyDraw c d)
            then Nat.ceil (F (applyDraw c d) - A) else 0) <
              Nat.ceil (F c - A) := by
          rcases hd with hbad | hdrop
          · rw [if_neg (fun h => hbad h.2)]
            exact hpos
          · have hdceil : Nat.ceil (F (applyDraw c d) - A) < Nat.ceil (F c - A) :=
              ceil_strict_drop hpos (by linarith)
            by_cases hnext : W (applyDraw c d)
            · rw [if_pos (And.intro hr hnext)]
              exact hdceil
            · rw [if_neg (fun h : r ∈ B ∧ W (applyDraw c d) => hnext h.2)]
              exact hpos
        have hH2 : H r d = 1 := by rw [hH1, if_pos hlt]
        exact hH2.ge
      · rw [if_neg hd]
        dsimp [H]
        split_ifs <;> norm_num
    · have hz : Nat.ceil (F c - A) = 0 := by omega
      rw [hz]
      simp only [nonlinearServiceRate, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
      exact integral_nonneg fun d => by dsimp [H]; split_ifs <;> norm_num
  · have hr : r ∉ B := fun hb => hlive ((hmem ω).mp hb)
    simp only [stoppedDebt, if_neg hlive, nonlinearServiceRate, Nat.cast_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
    exact integral_nonneg fun d => by dsimp [H]; split_ifs <;> norm_num


open Classical in
/-- Both ordered orientations give the exact quadratic probability; the
denominator is n(n−1), without an n² relaxation. -/
theorem nonlinear_service_rectangle (n J : ℕ) (c : Cfg L K)
    (hn : 2 ≤ n) (hpop : c.card = n)
    (P Q : AgentState L K → Prop) (E : Cfg L K → Prop)
    (hP : J ≤ c.countP P) (hQ : J ≤ c.countP Q)
    (hdisjoint : ∀ a, P a → ¬ Q a)
    (hservice : ∀ s t, Protocol.Applicable c s t →
      (P s ∧ Q t) ∨ (Q s ∧ P t) →
      E (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) :
    nonlinearServiceRate ((n : ℝ) * ((n : ℝ) - 1)) J ≤
      ∫ d, (if E (applyDraw c d) then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure := by
  have htotal : (c.totalPairs : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    simp only [Config.totalPairs, hpop, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n),
      Nat.cast_one]
  calc
    nonlinearServiceRate ((n : ℝ) * ((n : ℝ) - 1)) J =
        (2 * (J : ℝ) * (J : ℝ)) / (c.totalPairs : ℝ) := by
      rw [htotal]
      unfold nonlinearServiceRate
      ring
    _ ≤ (2 * (c.countP P : ℝ) * (c.countP Q : ℝ)) / (c.totalPairs : ℝ) := by
      gcongr <;> first | exact_mod_cast hP | exact_mod_cast hQ
    _ ≤ _ := service_rectangle_real c (by rw [hpop]; exact hn)
      P Q E hdisjoint hservice

def nonlinearDebtFailure (init : Cfg L K) (s : ℕ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M b T : ℕ) : Set (Ω L K) :=
  {ω | DebtLive init s F A W M T ω ∧
    b < Nat.ceil (F (trace init ω (s + T)) - A)}

theorem measurableSet_nonlinearDebtFailure (init : Cfg L K) (s : ℕ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop) (M b T : ℕ) :
    MeasurableSet (nonlinearDebtFailure init s F A W M b T) := by
  have hlarge : MeasurableSet[pairLogFiltration L K (s + T)]
      {ω | b < Nat.ceil (F (trace init ω (s + T)) - A)} :=
    (Set.to_countable {c : Cfg L K | b < Nat.ceil (F c - A)}).measurableSet.preimage
      (measurable_trace_at init (s + T))
  exact (pairLogFiltration L K).le (s + T) _
    ((measurableSet_debtLive init s F A W M T).inter hlarge)

open Classical in
/-- The local theorem constructs adaptation, boundedness and the conditional
nonlinear death inequality for the killed physical debt. -/
theorem recorded_nonlinear_service_tail (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M b : ℕ) (N : ℝ) (hN : 0 < N) (hb : 0 < b)
    (hbM : b ≤ M) (hcap : 2 * (M : ℝ) ^ 2 ≤ N)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) → F (applyDraw c d) ≤ F c)
    (hservice : ∀ c, W c →
      nonlinearServiceRate N (Nat.ceil (F c - A)) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (T : ℕ) (hT : N / (b : ℝ) ≤ T) :
    recordedFuture init s p (nonlinearDebtFailure init s F A W M b T) ≤
      ENNReal.ofReal (Real.exp (-(b : ℝ) / 6)) := by
  have htail := adapted_nonlinear_death_tail
    (μ := recordedFuture init s p) (ℱ := shiftedPairLog L K s)
    (stoppedDebt init s F A W M) M b N hN hb hbM hcap
    (stoppedDebt_stronglyMeasurable init s F A W M)
    (fun t => ae_of_all _ fun ω => stoppedDebt_le init s F A W M hmono t ω)
    (fun t => ae_of_all _ fun ω => stoppedDebt_mono init s F A W M hmono t ω)
    (stoppedDebt_conditional_nonlinear_death init s p F A W M N hservice) T hT
  have hsub : nonlinearDebtFailure init s F A W M b T ⊆
      {ω | b < stoppedDebt init s F A W M T ω} := by
    rintro ω ⟨hlive, hlarge⟩
    change b < stoppedDebt init s F A W M T ω
    rw [stoppedDebt, if_pos hlive]
    exact hlarge
  have hreal := (measureReal_mono hsub).trans htail
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hcast

open Classical in
/-- A prefix event retains its original-law probability factor. -/
theorem nonlinear_service_tail_from (init : Cfg L K) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L K))
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M b : ℕ) (N : ℝ) (hN : 0 < N) (hb : 0 < b)
    (hbM : b ≤ M) (hcap : 2 * (M : ℝ) ^ 2 ≤ N)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) → F (applyDraw c d) ≤ F c)
    (hservice : ∀ c, W c →
      nonlinearServiceRate N (Nat.ceil (F c - A)) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (T : ℕ) (hT : N / (b : ℝ) ≤ T) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ B ∧
      ω ∈ nonlinearDebtFailure init s F A W M b T} ≤
      ENNReal.ofReal (Real.exp (-(b : ℝ) / 6)) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ B} :=
  law_prefix_joint_bound init s B (nonlinearDebtFailure init s F A W M b T)
    (measurableSet_nonlinearDebtFailure init s F A W M b T) _
    (fun p _ => recorded_nonlinear_service_tail init s p F A W M b N hN hb hbM
      hcap hmono hservice T hT)

open Classical in
/-- The local estimate is summed over disjoint genuine stopping-time fibres,
without paying a factor for the number of possible start times. -/
theorem nonlinear_service_tail_at_pastTime (init : Cfg L K)
    (τ : Ω L K → WithTop ℕ) (hτ : PairLogPastTime τ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M b : ℕ) (N : ℝ) (hN : 0 < N) (hb : 0 < b)
    (hbM : b ≤ M) (hcap : 2 * (M : ℝ) ^ 2 ≤ N)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) → F (applyDraw c d) ≤ F c)
    (hservice : ∀ c, W c →
      nonlinearServiceRate N (Nat.ceil (F c - A)) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (T : ℕ) (hT : N / (b : ℝ) ≤ T) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
      ω ∈ nonlinearDebtFailure init s F A W M b T} ≤
      ENNReal.ofReal (Real.exp (-(b : ℝ) / 6)) :=
  law_at_past_time_bound init τ hτ
    (fun s => nonlinearDebtFailure init s F A W M b T)
    (fun s => measurableSet_nonlinearDebtFailure init s F A W M b T) _
    (fun s p => recorded_nonlinear_service_tail init s p F A W M b N hN hb hbM
      hcap hmono hservice T hT)

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end

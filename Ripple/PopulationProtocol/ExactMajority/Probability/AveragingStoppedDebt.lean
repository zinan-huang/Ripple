-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingStoppedDebt.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingRecordedExpectation
import Ripple.PopulationProtocol.ExactMajority.Probability.ScalarTails
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Killed integer excess of an actual rational debt

The process is the ceiling of a fixed debt excess on the physical scheduler.
It is killed at the first failed current-state gate. The initial-size gate is
also recorded, so all bounds hold on the entire continuation space.

The scalar tail is instantiated below: adaptation, boundedness, monotonicity,
and the conditional death estimate are conclusions. Protocol-specific service
rectangles enter only through the displayed one-step integral premise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingStoppedDebt

open TimeTheorem PairLog AveragingRecordedExpectation

variable {L K : ℕ}

def DebtLive (init : Cfg L K) (s : ℕ) (F : Cfg L K → ℚ)
    (A : ℚ) (W : Cfg L K → Prop) (M t : ℕ) (ω : Ω L K) : Prop :=
  Nat.ceil (F (trace init ω s) - A) ≤ M ∧
    ∀ u, u ≤ t → W (trace init ω (s + u))

open Classical in
def stoppedDebt (init : Cfg L K) (s : ℕ) (F : Cfg L K → ℚ)
    (A : ℚ) (W : Cfg L K → Prop) (M t : ℕ) (ω : Ω L K) : ℕ :=
  if DebtLive init s F A W M t ω
    then Nat.ceil (F (trace init ω (s + t)) - A) else 0

theorem debtLive_succ (init : Cfg L K) (s : ℕ) (F : Cfg L K → ℚ)
    (A : ℚ) (W : Cfg L K → Prop) (M t : ℕ) (ω : Ω L K) :
    DebtLive init s F A W M (t + 1) ω ↔
      DebtLive init s F A W M t ω ∧
        W (applyDraw (trace init ω (s + t)) (ω (s + t + 1))) := by
  constructor
  · rintro ⟨hM, hW⟩
    refine ⟨⟨hM, fun u hu => hW u (by omega)⟩, ?_⟩
    have hlast := hW (t + 1) le_rfl
    simpa only [Nat.add_assoc, TimeTheorem.trace_succ] using hlast
  · rintro ⟨⟨hM, hW⟩, hlast⟩
    refine ⟨hM, fun u hu => ?_⟩
    by_cases hut : u ≤ t
    · exact hW u hut
    · have heq : u = t + 1 := by omega
      subst u
      simpa only [Nat.add_assoc, TimeTheorem.trace_succ] using hlast

theorem measurableSet_debtLive (init : Cfg L K) (s : ℕ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop) (M t : ℕ) :
    MeasurableSet[pairLogFiltration L K (s + t)]
      {ω | DebtLive init s F A W M t ω} := by
  have hstart : MeasurableSet[pairLogFiltration L K (s + t)]
      {ω | Nat.ceil (F (trace init ω s) - A) ≤ M} :=
    (Set.to_countable {c : Cfg L K | Nat.ceil (F c - A) ≤ M}).measurableSet.preimage
      (measurable_trace_at_of_le init (by omega : s ≤ s + t))
  have hwindow : MeasurableSet[pairLogFiltration L K (s + t)]
      {ω | ∀ u, u ≤ t → W (trace init ω (s + u))} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu => ?_
    exact (Set.to_countable {c : Cfg L K | W c}).measurableSet.preimage
      (measurable_trace_at_of_le init (Nat.add_le_add_left hu s))
  exact hstart.inter hwindow

theorem stoppedDebt_stronglyMeasurable (init : Cfg L K) (s : ℕ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop) (M t : ℕ) :
    StronglyMeasurable[shiftedPairLog L K s t]
      (stoppedDebt init s F A W M t) := by
  classical
  have hval : Measurable[pairLogFiltration L K (s + t)]
      (fun ω => Nat.ceil (F (trace init ω (s + t)) - A)) :=
    (measurable_of_countable (fun c : Cfg L K => Nat.ceil (F c - A))).comp
      (measurable_trace_at init (s + t))
  exact (Measurable.ite (measurableSet_debtLive init s F A W M t)
    hval measurable_const).stronglyMeasurable

open Classical in
theorem stoppedDebt_succ (init : Cfg L K) (s : ℕ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M t : ℕ) (ω : Ω L K) :
    stoppedDebt init s F A W M (t + 1) ω =
      if DebtLive init s F A W M t ω ∧
          W (applyDraw (trace init ω (s + t)) (ω (s + t + 1)))
      then Nat.ceil
        (F (applyDraw (trace init ω (s + t)) (ω (s + t + 1))) - A)
      else 0 := by
  classical
  unfold stoppedDebt
  rw [if_congr (debtLive_succ init s F A W M t ω) rfl rfl]
  rfl

theorem stoppedDebt_mono (init : Cfg L K) (s : ℕ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop) (M : ℕ)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) →
      F (applyDraw c d) ≤ F c) (t : ℕ) (ω : Ω L K) :
    stoppedDebt init s F A W M (t + 1) ω ≤
      stoppedDebt init s F A W M t ω := by
  classical
  rw [stoppedDebt_succ]
  by_cases hlive : DebtLive init s F A W M t ω
  · by_cases hnext : W (applyDraw (trace init ω (s + t)) (ω (s + t + 1)))
    · rw [if_pos ⟨hlive, hnext⟩, stoppedDebt, if_pos hlive]
      apply Nat.ceil_mono
      exact sub_le_sub_right (hmono _ (hlive.2 t le_rfl) _ hnext) A
    · rw [if_neg (fun h => hnext h.2)]
      exact Nat.zero_le _
  · rw [if_neg (fun h => hlive h.1)]
    exact Nat.zero_le _

theorem stoppedDebt_le (init : Cfg L K) (s : ℕ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop) (M : ℕ)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) →
      F (applyDraw c d) ≤ F c) (t : ℕ) (ω : Ω L K) :
    stoppedDebt init s F A W M t ω ≤ M := by
  induction t with
  | zero =>
      classical
      by_cases h : DebtLive init s F A W M 0 ω
      · simpa only [stoppedDebt, if_pos h, Nat.add_zero] using h.1
      · simp only [stoppedDebt, if_neg h, Nat.zero_le]
  | succ t ih => exact (stoppedDebt_mono init s F A W M hmono t ω).trans ih

theorem stoppedDebt_integrable (init : Cfg L K) (s : ℕ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop) (M : ℕ)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) →
      F (applyDraw c d) ≤ F c)
    (p : (i : Finset.Iic s) → Draw L K) (t : ℕ) :
    Integrable (fun ω => (stoppedDebt init s F A W M t ω : ℝ))
      (recordedFuture init s p) := by
  have hsm := stoppedDebt_stronglyMeasurable init s F A W M t
  have hm : Measurable (stoppedDebt init s F A W M t) :=
    hsm.measurable.mono ((shiftedPairLog L K s).le t) le_rfl
  refine (integrable_const (M : ℝ)).mono'
    ((measurable_from_nat (f := ((↑) : ℕ → ℝ))).comp hm).aestronglyMeasurable ?_
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast stoppedDebt_le init s F A W M hmono t ω

theorem ceil_strict_drop {x y : ℚ} (hpos : 0 < Nat.ceil x)
    (hdrop : y + 1 ≤ x) : Nat.ceil y < Nat.ceil x := by
  have hceil : Nat.ceil y ≤ Nat.ceil x - 1 := by
    calc
      Nat.ceil y ≤ Nat.ceil (x - 1) := Nat.ceil_mono (by linarith)
      _ = Nat.ceil x - 1 := Nat.ceil_sub_one x
  omega

open Classical in
private theorem indicator_integrable {α : Type*} [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ] (P : α → Prop) :
    Integrable (fun x => if P x then (1 : ℝ) else 0) μ := by
  classical
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_of_countable _).aestronglyMeasurable ?_
  exact ae_of_all μ fun x => by split_ifs <;> norm_num

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
theorem stoppedDebt_conditional_death
    (init : Cfg L K) (s : ℕ) (p : (i : Finset.Iic s) → Draw L K)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop) (M : ℕ) (q : ℝ)
    (hservice : ∀ c, W c →
      q * (Nat.ceil (F c - A) : ℝ) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (t : ℕ) :
    (fun ω => q * (stoppedDebt init s F A W M t ω : ℝ))
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
  change q * (stoppedDebt init s F A W M t ω : ℝ) ≤ _
  refine le_of_le_of_eq ?_ hω.symm
  let c := trace init ω (s + t)
  let r := frestrictLe (π := fun _ : ℕ => Draw L K) (s + t) ω
  have hcfg : prefixCfg init (s + t) r = c := rfl
  change q * (stoppedDebt init s F A W M t ω : ℝ) ≤
    ∫ d, H r d ∂(drawLaw c).toMeasure
  by_cases hlive : DebtLive init s F A W M t ω
  · have hr : r ∈ B := (hmem ω).mpr hlive
    rw [stoppedDebt, if_pos hlive]
    change q * (Nat.ceil (F c - A) : ℝ) ≤ _
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
      rw [hz, Nat.cast_zero, mul_zero]
      exact integral_nonneg fun d => by dsimp [H]; split_ifs <;> norm_num
  · have hr : r ∉ B := fun hb => hlive ((hmem ω).mp hb)
    simp only [stoppedDebt, if_neg hlive, Nat.cast_zero, mul_zero]
    exact integral_nonneg fun d => by dsimp [H]; split_ifs <;> norm_num

open Classical in
/-- Local stopped death tail under the original recorded continuation. The
conclusion is a joint event with gate survival, never a conditional law. -/
theorem stoppedDebt_exponential_tail
    (init : Cfg L K) (s : ℕ) (p : (i : Finset.Iic s) → Draw L K)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M : ℕ) (q a : ℝ) (hq : 0 ≤ q) (hqM : q * M ≤ 1)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) →
      F (applyDraw c d) ≤ F c)
    (hservice : ∀ c, W c →
      q * (Nat.ceil (F c - A) : ℝ) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (T : ℕ) :
    (recordedFuture init s p).real
      {ω | DebtLive init s F A W M T ω ∧
        a * M ≤ (Nat.ceil (F (trace init ω (s + T)) - A) : ℝ)} ≤
      Real.exp ((7 * Real.exp (-q * T) - a * Real.log 8) * M) := by
  have htail := ScalarTails.adapted_death_exponential_tail
    (μ := recordedFuture init s p) (ℱ := shiftedPairLog L K s)
    (stoppedDebt init s F A W M) M q a hq hqM
    (stoppedDebt_stronglyMeasurable init s F A W M)
    (fun t => ae_of_all _ fun ω => stoppedDebt_le init s F A W M hmono t ω)
    (fun t => ae_of_all _ fun ω => stoppedDebt_mono init s F A W M hmono t ω)
    (stoppedDebt_conditional_death init s p F A W M q hservice) T
  refine (measureReal_mono ?_).trans htail
  rintro ω ⟨hlive, hlarge⟩
  show a * (M : ℝ) ≤ (stoppedDebt init s F A W M T ω : ℝ)
  unfold stoppedDebt
  rw [if_pos hlive]
  exact hlarge

end Ripple.PopulationProtocol.ExactMajority.AveragingStoppedDebt

end

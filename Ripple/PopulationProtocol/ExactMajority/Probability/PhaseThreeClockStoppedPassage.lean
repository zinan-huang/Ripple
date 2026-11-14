-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockStoppedPassage.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProbabilityFloors
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEmbeddingBridge
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPrefixTails

/-!
# A prefix-weighted killed passage bound for the virtual clock

The stop is the first failure of an explicit current-state window. Its
window requires the concrete phase/Clock initialization conditions needed
by the embedding, the Clock-density floor, and a positive sparse front
strictly below its target.

The probability bound is proved under the original pair-log law, with an
arbitrary event in the starting sigma-algebra retained as a factor.
No probability hypothesis about the target or eventual good event is used.

This is a coarse passage bound, not the calibrated coupon-collector bound
P3a: the latter still requires the state-dependent geometric comparison.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockStoppedPassage

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
open PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
open PhaseThreeClockProbabilityFloors PhaseThreeClockEmbeddingBridge
open PhaseThreeClockPrefixTails

section Scalar

variable {Ω : Type*} {m : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m}

private theorem passage_filled_adapted
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hτ : IsStoppingTime ℱ τ) :
    ∀ t, StronglyMeasurable[ℱ (t + 1)] (filledBernoulli I τ t) := by
  intro t
  have hleft : StronglyMeasurable[ℱ (t + 1)] (stoppedBernoulli I τ t) :=
    (hI t).indicator
      ((ℱ.mono (Nat.le_succ t)) _ (hτ.measurableSet_gt t))
  have hright : StronglyMeasurable[ℱ (t + 1)]
      (({ω | (t : WithTop ℕ) < τ ω}ᶜ).indicator (fun _ : Ω => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator
      ((ℱ.mono (Nat.le_succ t)) _ (hτ.measurableSet_gt t).compl)
  exact hleft.add hright

private theorem passage_filled_zero_one
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1) :
    ∀ t, ∀ᵐ ω ∂μ,
      filledBernoulli I τ t ω = 0 ∨ filledBernoulli I τ t ω = 1 := by
  intro t
  filter_upwards [hzeroOne t] with ω hω
  by_cases h : (t : WithTop ℕ) < τ ω
  · simpa [filledBernoulli, stoppedBernoulli, h] using hω
  · simp [filledBernoulli, stoppedBernoulli, h]

private theorem passage_filled_conditional
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hτ : IsStoppingTime ℱ τ) (t : ℕ) :
    μ[filledBernoulli I τ t | ℱ t] =ᵐ[μ]
      fun ω => if (t : WithTop ℕ) < τ ω then (μ[I t | ℱ t]) ω else 1 := by
  classical
  let A : Set Ω := {ω | (t : WithTop ℕ) < τ ω}
  have hA : MeasurableSet[ℱ t] A := hτ.measurableSet_gt t
  have hi := bernoulli_integrable hI hzeroOne t
  have hleft : Integrable (A.indicator (I t)) μ :=
    hi.indicator ((ℱ.le t) _ hA)
  have hright : Integrable (Aᶜ.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator ((ℱ.le t) _ hA.compl)
  change μ[A.indicator (I t) + Aᶜ.indicator (fun _ => (1 : ℝ)) | ℱ t]
    =ᵐ[μ] _
  filter_upwards
    [condExp_add hleft hright (ℱ t), condExp_indicator hi hA,
      condExp_indicator (integrable_const (1 : ℝ)) hA.compl] with ω ha hl hr
  simp only [Pi.add_apply] at ha
  rw [ha, hl, hr, condExp_const (ℱ.le t) (1 : ℝ)]
  by_cases h : (t : WithTop ℕ) < τ ω <;> simp [A, h]

/-- The success-hitting estimate with the mass of an observed prefix retained. -/
theorem prefix_success_hitting_tail
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ} {p : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hτ : IsStoppingTime ℱ τ) (hp : p ≤ 1)
    (hcond : ∀ t : ℕ, ∀ᵐ ω ∂μ, (t : WithTop ℕ) < τ ω →
      p ≤ (μ[I t | ℱ t]) ω)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (N : ℕ) (k : ℝ)
    (hfail : ∀ ω ∈ E, (N : WithTop ℕ) < τ ω →
      bernoulliCount I N ω < k) :
    μ.real (E ∩ {ω | (N : WithTop ℕ) < τ ω}) ≤
      Real.exp (k * Real.log 2 - p * (N : ℝ) / 2) * μ.real E := by
  have hfilled : ∀ t,
      (fun _ => p) ≤ᵐ[μ] μ[filledBernoulli I τ t | ℱ t] := by
    intro t
    filter_upwards [passage_filled_conditional hI hzeroOne hτ t, hcond t]
      with ω he hc
    rw [he]
    by_cases h : (t : WithTop ℕ) < τ ω
    · simpa [h] using hc h
    · simpa [h] using hp
  have hsub :
      E ∩ {ω | (N : WithTop ℕ) < τ ω} ⊆
        E ∩ {ω | bernoulliCount (filledBernoulli I τ) N ω < k} := by
    rintro ω ⟨hω, hN⟩
    refine ⟨hω, ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [filledBernoulli_count_eq_of_not_hit I τ N ω hN]
    exact hfail ω hω hN
  exact (measureReal_mono hsub).trans
    (prefix_adapted_bernoulli_lower_tail
      (passage_filled_adapted hI hτ) (passage_filled_zero_one hzeroOne)
      hfilled E hE N k)

end Scalar

variable {L m : ℕ}

/-- The stop is caused by a protocol-regime failure, loss of the Clock-density
or positive sparse-front conditions, or reaching the target b. -/
def PassageWindow (f : Fin m → AgentState L 256) (ℓ b : ℕ) : Prop :=
  (∀ k, 1 ≤ (f k).phase.val ∧ (f k).phase.val ≤ 3) ∧
  (∀ k, (f k).role = .clock → (f k).smallBias.val = 3) ∧
  6 * m ≤ 25 * clockCount f ∧
  1 ≤ frontCount f ℓ ∧ frontCount f ℓ < b ∧
  10 * frontCount f ℓ ≤ clockCount f

open Classical in
def passageStop (init : Cfg L 256) (ℓ b s : ℕ) (ω : Ω L 256) : WithTop ℕ :=
  if h : ∃ t, ¬ PassageWindow (virtualLabels init ω (s + t)) ℓ b
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

open Classical in
def gatedIndicator (init : Cfg L 256) (ℓ t : ℕ) (ω : Ω L 256) : ℝ :=
  if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
      GatedTick ℓ (auxLabels init virtualRule ω t) i j
  then 1 else 0

theorem passageStop_le_iff (init : Cfg L 256) (ℓ b s t : ℕ) (ω : Ω L 256) :
    passageStop init ℓ b s ω ≤ (t : WithTop ℕ) ↔
      ∃ u ≤ t, ¬ PassageWindow (virtualLabels init ω (s + u)) ℓ b := by
  classical
  unfold passageStop
  split_ifs with h
  · constructor
    · intro hle
      have h' : Nat.find h ≤ t := by exact_mod_cast hle
      exact ⟨Nat.find h, h', Nat.find_spec h⟩
    · rintro ⟨u, hu, hw⟩
      have h' : Nat.find h ≤ t := (Nat.find_min' h hw).trans hu
      exact_mod_cast h'
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨u, -, hu⟩
      exact absurd ⟨u, hu⟩ h

theorem passageWindow_of_lt_stop (init : Cfg L 256) (ℓ b s N : ℕ)
    (ω : Ω L 256) (hN : (N : WithTop ℕ) < passageStop init ℓ b s ω) :
    ∀ u ≤ N, PassageWindow (virtualLabels init ω (s + u)) ℓ b := by
  intro u hu
  by_contra hw
  have hle := (passageStop_le_iff init ℓ b s N ω).2 ⟨u, hu, hw⟩
  exact absurd hN (not_lt.mpr hle)

theorem passageWindow_measurable (init : Cfg L 256) (ℓ b s t : ℕ) :
    MeasurableSet[shiftedFiltration (pairLogFiltration L 256) s t]
      {ω | PassageWindow (virtualLabels init ω (s + t)) ℓ b} := by
  change MeasurableSet[pairLogFiltration L 256 (s + t)] _
  exact (measurable_virtualLabels init (s + t))
    (Set.to_countable {f : Fin init.card → AgentState L 256 |
      PassageWindow f ℓ b}).measurableSet

theorem passageStop_isStoppingTime (init : Cfg L 256) (ℓ b s : ℕ) :
    IsStoppingTime (shiftedFiltration (pairLogFiltration L 256) s)
      (passageStop init ℓ b s) := by
  intro t
  have hm : MeasurableSet[shiftedFiltration (pairLogFiltration L 256) s t]
      (⋃ u, {ω | u ≤ t ∧ ¬ PassageWindow (virtualLabels init ω (s + u)) ℓ b}) := by
    refine MeasurableSet.iUnion fun u => ?_
    by_cases hu : u ≤ t
    · have hw :
          MeasurableSet[shiftedFiltration (pairLogFiltration L 256) s t]
            {ω | ¬ PassageWindow (virtualLabels init ω (s + u)) ℓ b} :=
        ((shiftedFiltration (pairLogFiltration L 256) s).mono hu) _
          (passageWindow_measurable init ℓ b s u).compl
      simpa only [hu, true_and] using hw
    · simp only [hu, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact passageStop_le_iff init ℓ b s t ω

theorem gatedIndicator_zero_one (init : Cfg L 256) (ℓ t : ℕ) (ω : Ω L 256) :
    gatedIndicator init ℓ t ω = 0 ∨ gatedIndicator init ℓ t ω = 1 := by
  classical
  unfold gatedIndicator
  split_ifs <;> simp

/-- Both endpoint windows discharge the concrete phase, initialization,
role, and no-backup conditions of the virtual embedding. -/
theorem front_step_on_window (init : Cfg L 256) (ω : Ω L 256)
    (t ℓ b : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (hcur : PassageWindow (virtualLabels init ω t) ℓ b)
    (hnext : PassageWindow (virtualLabels init ω (t + 1)) ℓ b) :
    (frontCount (virtualLabels init ω (t + 1)) ℓ : ℝ) =
      (frontCount (virtualLabels init ω t) ℓ : ℝ) + gatedIndicator init ℓ t ω := by
  classical
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      have h := frontCount_virtualLabels_succ_of_none init ω t hd ℓ
      simp only [gatedIndicator, hd, reduceCtorEq, false_and, exists_false,
        if_false, add_zero]
      exact_mod_cast h
  | some ij =>
      rcases ij with ⟨i, j⟩
      have h := frontCount_virtualLabels_succ_of_phase_range init ω t i j hd
        hcur.1 hcur.2.1 (fun k => (hnext.1 k).2) ℓ hℓ hcap
      have hevent :
          (∃ u v, drawLabels init ω (t + 1) = some (u, v) ∧
            GatedTick ℓ (auxLabels init virtualRule ω t) u v) ↔
          GatedTick ℓ (virtualLabels init ω t) i j := by
        simp only [hd, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨u, v, ⟨rfl, rfl⟩, hg⟩
          exact hg
        · intro hg
          exact ⟨i, j, ⟨rfl, rfl⟩, hg⟩
      have hreal :
          (frontCount (virtualLabels init ω (t + 1)) ℓ : ℝ) =
            (frontCount (virtualLabels init ω t) ℓ : ℝ) +
              if GatedTick ℓ (virtualLabels init ω t) i j then (1 : ℝ) else 0 := by
        split_ifs with hg
        · rw [if_pos hg] at h
          exact_mod_cast h
        · rw [if_neg hg] at h
          exact_mod_cast h
      simpa only [gatedIndicator, hevent] using hreal

theorem gated_count_lt_target_of_survival (init : Cfg L 256) (ω : Ω L 256)
    (ℓ b s N : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (hN : (N : WithTop ℕ) < passageStop init ℓ b s ω) :
    bernoulliCount (fun t => gatedIndicator init ℓ (s + t)) N ω < (b : ℝ) := by
  have hw := passageWindow_of_lt_stop init ℓ b s N ω hN
  have htel : ∀ r, r ≤ N →
      (frontCount (virtualLabels init ω (s + r)) ℓ : ℝ) =
        (frontCount (virtualLabels init ω s) ℓ : ℝ) +
          bernoulliCount (fun t => gatedIndicator init ℓ (s + t)) r ω := by
    intro r
    induction r with
    | zero =>
        intro hr
        simp [bernoulliCount]
    | succ r ih =>
        intro hr
        have hp := ih (by omega)
        have hs := front_step_on_window init ω (s + r) ℓ b hℓ hcap
          (hw r (by omega)) (by simpa only [Nat.add_assoc] using hw (r + 1) hr)
        simpa only [Nat.add_assoc, bernoulliCount, Finset.sum_range_succ,
          add_assoc] using hs.trans (congrArg
            (fun z : ℝ => z + gatedIndicator init ℓ (s + r) ω) hp)
  have hbelow : (frontCount (virtualLabels init ω (s + N)) ℓ : ℝ) < (b : ℝ) := by
    exact_mod_cast (hw N le_rfl).2.2.2.2.1
  have hnonneg : 0 ≤ (frontCount (virtualLabels init ω s) ℓ : ℝ) := by positivity
  linarith [htel N le_rfl]

/-- A concrete killed passage tail under the original pair-log law,
uniform over any event observed at the deterministic start s. -/
theorem gated_passage_prefix_real_tail (init : Cfg L 256) (hc : 2 ≤ init.card)
    (ℓ b s N : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E) :
    (law init).real (E ∩ {ω | (N : WithTop ℕ) < passageStop init ℓ b s ω}) ≤
      Real.exp ((b : ℝ) * Real.log 2 - (N : ℝ) / (6 * (init.card : ℝ))) *
        (law init).real E := by
  classical
  let ℱ := shiftedFiltration (pairLogFiltration L 256) s
  let I : ℕ → Ω L 256 → ℝ := fun t => gatedIndicator init ℓ (s + t)
  let p : ℝ := 1 / (3 * (init.card : ℝ))
  have hn : (2 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hc
  have hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t) := by
    intro t
    simpa only [ℱ, I, shiftedFiltration_apply, Nat.add_assoc, gatedIndicator] using
      stronglyMeasurable_aux_pair_indicator init virtualRule (GatedTick ℓ) (s + t)
  have hzeroOne : ∀ t, ∀ᵐ ω ∂law init, I t ω = 0 ∨ I t ω = 1 := by
    intro t
    exact ae_of_all _ fun ω => gatedIndicator_zero_one init ℓ (s + t) ω
  have hτ : IsStoppingTime ℱ (passageStop init ℓ b s) :=
    passageStop_isStoppingTime init ℓ b s
  have hp : p ≤ 1 := by
    dsimp only [p]
    apply (div_le_iff₀ (by positivity : 0 < 3 * (init.card : ℝ))).2
    linarith
  have hcond : ∀ t : ℕ, ∀ᵐ ω ∂law init,
      (t : WithTop ℕ) < passageStop init ℓ b s ω →
        p ≤ ((law init)[I t | ℱ t]) ω := by
    intro t
    filter_upwards [gated_conditional_front_floor init hc ℓ (s + t) hℓ] with ω hf
    intro ht
    have hw := passageWindow_of_lt_stop init ℓ b s t ω ht t le_rfl
    have hpos : (1 : ℝ) ≤
        (frontCount (auxLabels init virtualRule ω (s + t)) ℓ : ℝ) := by
      exact_mod_cast hw.2.2.2.1
    have hlow :
        p ≤ (frontCount (auxLabels init virtualRule ω (s + t)) ℓ : ℝ) /
          (3 * (init.card : ℝ)) :=
      div_le_div_of_nonneg_right hpos (by positivity)
    exact hlow.trans (hf hw.2.2.1 hw.2.2.2.2.2)
  have hEs : MeasurableSet[ℱ 0] E := by
    simpa only [ℱ, shiftedFiltration_apply, Nat.add_zero] using hE
  have ht := prefix_success_hitting_tail hI hzeroOne hτ hp hcond E hEs N (b : ℝ)
    (fun ω _ hN => gated_count_lt_target_of_survival init ω ℓ b s N hℓ hcap hN)
  have hfrac : p * (N : ℝ) / 2 = (N : ℝ) / (6 * (init.card : ℝ)) := by
    dsimp only [p]
    field_simp [show (init.card : ℝ) ≠ 0 by linarith] <;> ring
  simpa only [hfrac] using ht

theorem gated_passage_prefix_tail (init : Cfg L 256) (hc : 2 ≤ init.card)
    (ℓ b s N : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E) :
    law init (E ∩ {ω | (N : WithTop ℕ) < passageStop init ℓ b s ω}) ≤
      ENNReal.ofReal
        (Real.exp ((b : ℝ) * Real.log 2 - (N : ℝ) / (6 * (init.card : ℝ)))) *
          law init E := by
  have h := gated_passage_prefix_real_tail init hc ℓ b s N hℓ hcap E hE
  calc
    law init (E ∩ {ω | (N : WithTop ℕ) < passageStop init ℓ b s ω}) =
        ENNReal.ofReal
          ((law init).real (E ∩ {ω | (N : WithTop ℕ) < passageStop init ℓ b s ω})) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal
        (Real.exp ((b : ℝ) * Real.log 2 - (N : ℝ) / (6 * (init.card : ℝ))) *
          (law init).real E) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      change ENNReal.ofReal
        (Real.exp ((b : ℝ) * Real.log 2 - (N : ℝ) / (6 * (init.card : ℝ))) *
          (law init E).toReal) = _
      rw [ENNReal.ofReal_mul (Real.exp_nonneg _),
        ENNReal.ofReal_toReal (measure_ne_top _ _)]


/-- The positive sparse protocol window is exited in finite time almost surely.
An exit can be the target crossing or a guard failure; this theorem does not
identify the exit as a crossing. -/
theorem passageStop_eq_top_null (init : Cfg L 256) (hc : 2 ≤ init.card)
    (ℓ b s : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1)) :
    law init {ω | passageStop init ℓ b s ω = ⊤} = 0 := by
  let A : Set (Ω L 256) := {ω | passageStop init ℓ b s ω = ⊤}
  let a : ℝ := (law init).real A
  have hn : (2 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hc
  have hd : 0 < 6 * (init.card : ℝ) := by positivity
  have hbound (N : ℕ) :
      a ≤ Real.exp ((b : ℝ) * Real.log 2 - (N : ℝ) / (6 * (init.card : ℝ))) := by
    have hsub : A ⊆ {ω | (N : WithTop ℕ) < passageStop init ℓ b s ω} := by
      intro ω hω
      change passageStop init ℓ b s ω = ⊤ at hω
      simp [hω]
    have ht := gated_passage_prefix_real_tail init hc ℓ b s N hℓ hcap
      Set.univ MeasurableSet.univ
    exact (measureReal_mono hsub).trans (by simpa using ht)
  have ha : a = 0 := by
    apply le_antisymm ?_ (by dsimp only [a]; positivity)
    by_contra hnot
    have hpos : 0 < a := lt_of_not_ge hnot
    obtain ⟨N, hN⟩ := exists_nat_gt
      ((6 * (init.card : ℝ)) * ((b : ℝ) * Real.log 2 - Real.log a))
    have hdiv :
        (b : ℝ) * Real.log 2 - Real.log a <
          (N : ℝ) / (6 * (init.card : ℝ)) := by
      apply (lt_div_iff₀ hd).2
      simpa only [mul_comm] using hN
    have harg :
        (b : ℝ) * Real.log 2 - (N : ℝ) / (6 * (init.card : ℝ)) < Real.log a := by
      linarith
    have hexp :
        Real.exp ((b : ℝ) * Real.log 2 -
          (N : ℝ) / (6 * (init.card : ℝ))) < a := by
      simpa only [Real.exp_log hpos] using Real.exp_lt_exp.mpr harg
    exact (not_lt_of_ge (hbound N)) hexp
  calc
    law init {ω | passageStop init ℓ b s ω = ⊤} = ENNReal.ofReal a :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = 0 := by rw [ha, ENNReal.ofReal_zero]

/-- Nullness remains valid with any prefix event, and indeed any event,
intersected before the infinite-window event. -/
theorem passageStop_eq_top_prefix_null (init : Cfg L 256) (hc : 2 ≤ init.card)
    (ℓ b s : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) :
    law init (E ∩ {ω | passageStop init ℓ b s ω = ⊤}) = 0 := by
  apply le_antisymm ?_ zero_le
  calc
    law init (E ∩ {ω | passageStop init ℓ b s ω = ⊤}) ≤
        law init {ω | passageStop init ℓ b s ω = ⊤} :=
      measure_mono Set.inter_subset_right
    _ = 0 := passageStop_eq_top_null init hc ℓ b s hℓ hcap

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockStoppedPassage

end

-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseNineContinuationCleanup.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase9OutputCleanup
import Ripple.PopulationProtocol.ExactMajority.Probability.ThresholdEpidemic
import Ripple.PopulationProtocol.ExactMajority.Probability.UniformRecovery
import Ripple.PopulationProtocol.ExactMajority.Probability.StrongContinuationComposition

/-!
The Phase-9 output stage, under the original occurrence-pair scheduler.
The stopped rank is zero after a stable endpoint or a Phase-10 seed,
one for a uniform conflicting opinion mask, and the wrong-output count
for a nonconflicting mask.  The empty mask is already pairwise fixed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseNineContinuationCleanup

open TimeTheorem StageEventSpec UniformRecovery Phase9OutputCleanup
  StrongContinuationComposition

variable {L K : ℕ}

/-- This extracts the actual Phase-9 endpoint, including both signed
orientations, from N19's qualitative correctness theorem. -/
theorem phase_nine_endpoint_of_fixed {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (c : InputCfg n)
    (hreach : ReachableFrom (PhaseThreeModel.Numeric.hourIndex n) 256 init c)
    (hpure : PurePhase 9 c) (hfixed : PairwiseFixed c) :
    phase9ConsensusEndpoint init c := by
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  have hcard : c.card = n :=
    (Protocol.reachable_card_eq hreach).trans hinput.2.2
  have hlow : 11 ≤ init.card := by rw [hinput.2.2]; omega
  have hsize : init.card ≤ 2 ^ PhaseThreeModel.Numeric.hourIndex n := by
    rw [hinput.2.2]
    exact Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) n
  have hdone := reachable_pairwiseFixed_mem_stableDone
    init c hinput.2.1 hlow hsize hreach hfixed
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp
    (show 0 < c.card by rw [hcard]; omega)
  have hphase := hpure a ha
  change majorityStableEndpoint init c at hdone
  rcases hdone with htwo | hfour | hnine | hten
  · rcases htwo with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    all_goals
      have hbad := h.1.1 a ha
      omega
  · have hbad := (hfour.2 a ha).1
    omega
  · rcases hnine with ⟨hm, h⟩ | ⟨hm, h⟩ | ⟨hm, h⟩
    · exact phase9ConsensusEndpoint_of_A init c hm h.1 h.2
    · exact phase9ConsensusEndpoint_of_B init c hm h.1 h.2
    · exact phase9ConsensusEndpoint_of_T init c hm h.1 h.2
  · rcases hten with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    all_goals
      have hbad := (h a ha).1
      omega

theorem phase_nine_fixed_stable_output {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (c : InputCfg n)
    (hreach : ReachableFrom (PhaseThreeModel.Numeric.hourIndex n) 256 init c)
    (hpure : PurePhase 9 c) (hfixed : PairwiseFixed c) :
    (doutPartition (PhaseThreeModel.Numeric.hourIndex n) 256).output
        (majorityVerdict init) c ∧
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).IsStable
        (doutPartition (PhaseThreeModel.Numeric.hourIndex n) 256) c :=
  stable_output_of_phase9ConsensusEndpoint init c
    (phase_nine_endpoint_of_fixed init hinput c hreach hpure hfixed)

def CleanupInv (init : Cfg L K) (u : Fin 8) (n : ℕ)
    (c : Cfg L K) : Prop :=
  ReachableFrom L K init c ∧ c.card = n ∧
    (c ∈ phaseWorkTarget 9 init ∨
      (PurePhase 9 c ∧ ∀ a ∈ c, a.opinions = u))

noncomputable def cleanupRank (init : Cfg L K) (u : Fin 8)
    (c : Cfg L K) : ℕ := by
  classical
  exact if c ∈ phaseWorkTarget 9 init then 0
    else if hasMinusOne u = true ∧ hasPlusOne u = true then 1
    else wrongOutputCount9 (opinionVerdict u) c

private theorem applicable_of_positive_count
    (c : Cfg L K) (s t : AgentState L K)
    (h : 0 < c.interactionCount s t) :
    Protocol.Applicable c s t := by
  classical
  change {s, t} ≤ c
  rw [Multiset.le_iff_count]
  intro a
  simp only [Config.interactionCount, Config.count] at h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons,
    Multiset.count_singleton]
  by_cases heq : s = t
  · subst heq
    simp only [ite_true] at h
    have htwo : 2 ≤ Multiset.count s c := by
      by_contra hlt
      have hle : Multiset.count s c ≤ 1 := by omega
      have hz : Multiset.count s c * (Multiset.count s c - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (Multiset.count s c) with hzero | hpos
        · simp [hzero]
        · have hone : Multiset.count s c = 1 := by omega
          simp [hone]
      omega
    by_cases ha : a = s <;> simp_all
  · simp only [if_neg heq] at h
    have hspos : 0 < Multiset.count s c :=
      pos_of_mul_pos_left h (Nat.zero_le _)
    have htpos : 0 < Multiset.count t c :=
      pos_of_mul_pos_right h (Nat.zero_le _)
    by_cases has : a = s <;> by_cases hat : a = t <;> simp_all <;> omega

private theorem support_applicable_pair
    (c d : Cfg L K) (hc : 2 ≤ c.card)
    (hd : d ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    ∃ s t, Protocol.Applicable c s t ∧
      Protocol.stepOrSelf (NonuniformMajority L K) c s t = d := by
  classical
  simp only [Protocol.stepDistOrSelf, dif_pos hc, Protocol.stepDist,
    PMF.support_map, Set.mem_image] at hd
  obtain ⟨⟨s, t⟩, hp, heq⟩ := hd
  have hprob : c.interactionProb s t ≠ 0 := hp
  have hcount : 0 < c.interactionCount s t := by
    by_contra h
    have hz : c.interactionCount s t = 0 := by omega
    exact hprob (by simp [Config.interactionProb, hz])
  exact ⟨s, t, applicable_of_positive_count c s t hcount, heq⟩

private theorem nonconflicting_guard (u : Fin 8)
    (h : ¬ (hasMinusOne u = true ∧ hasPlusOne u = true)) :
    (hasMinusOne u && hasPlusOne u) = false := by
  cases hm : hasMinusOne u <;> cases hp : hasPlusOne u <;> simp_all

theorem cleanupInv_support (init : Cfg L K) (u : Fin 8)
    (n : ℕ) (hn : 2 ≤ n) (c d : Cfg L K)
    (hc : CleanupInv init u n c)
    (hd : d ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    CleanupInv init u n d := by
  have hstep := Protocol.stepDistOrSelf_support_reachable
    (NonuniformMajority L K) c d hd
  refine ⟨hc.1.trans hstep,
    (Protocol.reachable_card_eq hstep).trans hc.2.1, ?_⟩
  rcases hc.2.2 with htarget | ⟨hpure, hu⟩
  · exact Or.inl (phaseWorkTarget_support 9 init c d htarget hd)
  · obtain ⟨s, t, happ, heq⟩ :=
      support_applicable_pair c d (by rw [hc.2.1]; exact hn) hd
    rw [← heq]
    by_cases hconf : hasMinusOne u = true ∧ hasPlusOne u = true
    · exact Or.inl (Or.inr (uniform_conflict_pair_advances
        9 (Or.inr rfl) u hconf.1 hconf.2 c hpure hu s t happ))
    · by_cases hz : u.val = 0
      · have hu0 : u = (0 : Fin 8) := Fin.ext hz
        have hfixed := opinion_zero_pairwiseFixed 9 (Or.inr rfl)
          c hpure (by simpa only [hu0] using hu)
        rw [hfixed s t]
        exact Or.inr ⟨hpure, hu⟩
      · exact Or.inr (opinion_cleanup_preserves 9 (Or.inr rfl) u hz
          (nonconflicting_guard u hconf) c hpure hu s t)

theorem cleanupInv_kernel_escape_zero (init : Cfg L K) (u : Fin 8)
    (n : ℕ) (hn : 2 ≤ n) (c : Cfg L K) (hc : CleanupInv init u n c) :
    (NonuniformMajority L K).transitionKernel c
      {d | ¬ CleanupInv init u n d} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
  intro d hd hbad
  exact hbad (cleanupInv_support init u n hn c d hc hd)

theorem cleanupRank_zero_target {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (u : Fin 8) (c : InputCfg n) (hc : CleanupInv init u n c)
    (hz : cleanupRank init u c = 0) :
    c ∈ phaseWorkTarget 9 init := by
  classical
  by_contra htarget
  have hpure : PurePhase 9 c := (hc.2.2.resolve_left htarget).1
  have hu : ∀ a ∈ c, a.opinions = u := (hc.2.2.resolve_left htarget).2
  have hfixed : PairwiseFixed c := by
    by_cases hu0 : u.val = 0
    · have hu0' : u = (0 : Fin 8) := Fin.ext hu0
      exact opinion_zero_pairwiseFixed 9 (Or.inr rfl)
        c hpure (by simpa only [hu0'] using hu)
    · have hconf : ¬ (hasMinusOne u = true ∧ hasPlusOne u = true) := by
        intro h
        simp [cleanupRank, htarget, h] at hz
      have hw : wrongOutputCount9 (opinionVerdict u) c = 0 := by
        simpa only [cleanupRank, if_neg htarget, if_neg hconf] using hz
      have hout : ∀ a ∈ c, a.output = opinionVerdict u := by
        simpa [wrongOutputCount9, Multiset.countP_eq_zero] using hw
      exact opinion_cleanup_pairwiseFixed 9 (Or.inr rfl) u hu0
        (nonconflicting_guard u hconf) c hpure hu hout
  have he := phase_nine_endpoint_of_fixed init hinput c hc.1 hpure hfixed
  exact htarget (Or.inl (Or.inr (Or.inr (Or.inl he))))

theorem cleanupRank_le_population (init : Cfg L K) (u : Fin 8)
    (n : ℕ) (hn : 1 ≤ n) (c : Cfg L K) (hc : c.card = n) :
    cleanupRank init u c ≤ n := by
  classical
  unfold cleanupRank
  split_ifs
  · omega
  · exact hn
  · exact (wrongOutputCount9_le_card _ c).trans_eq hc

private theorem uniform_signs (u : Fin 8) (hu : u.val ≠ 0)
    (hconf : ¬ (hasMinusOne u = true ∧ hasPlusOne u = true))
    (n : ℕ) (c : Cfg L K) (hcard : c.card = n)
    (hpure : PurePhase 9 c) (hop : ∀ a ∈ c, a.opinions = u) :
    Phase9SignsDone (opinionVerdict u) n c := by
  refine ⟨hcard, ?_⟩
  intro a ha
  have hp := hpure a ha
  have ho := hop a ha
  fin_cases u <;>
    simp_all [Phase9SignState, opinionVerdict, hasMinusOne, hasPlusOne,
      phase2OpinionT]

private theorem rank_integral_zero_of_target
    (init : Cfg L K) (u : Fin 8) (c : Cfg L K)
    (hzero : (NonuniformMajority L K).transitionKernel c
      (phaseWorkTarget 9 init)ᶜ = 0) :
    (∫⁻ d, (cleanupRank init u d : ℝ≥0∞)
      ∂(NonuniformMajority L K).transitionKernel c) = 0 := by
  classical
  have hae : ∀ᵐ d ∂(NonuniformMajority L K).transitionKernel c,
      d ∈ phaseWorkTarget 9 init := by
    rw [ae_iff]
    exact hzero
  calc
    _ = ∫⁻ _d, (0 : ℝ≥0∞)
        ∂(NonuniformMajority L K).transitionKernel c := by
      apply lintegral_congr_ae
      filter_upwards [hae] with d hd
      simp [cleanupRank, hd]
    _ = 0 := lintegral_zero

theorem cleanupRank_drift {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (u : Fin 8) (c : InputCfg n) (hc : CleanupInv init u n c) :
    (∫⁻ d, (cleanupRank init u d : ℝ≥0∞)
      ∂(NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c)
      ≤ phase9CleanupRate n * (cleanupRank init u c : ℝ≥0∞) := by
  classical
  have hn : 2 ≤ n := by
    have := (time_population_bounds hinput.1).2
    omega
  by_cases htarget : c ∈ phaseWorkTarget 9 init
  · rw [rank_integral_zero_of_target init u c
      (phaseWorkTarget_kernel_absorbing 9 init c htarget)]
    exact zero_le
  · have hpure := (hc.2.2.resolve_left htarget).1
    have hu := (hc.2.2.resolve_left htarget).2
    by_cases hconf : hasMinusOne u = true ∧ hasPlusOne u = true
    · have hzero :
          (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel
            c (phaseWorkTarget 9 init)ᶜ = 0 := by
        change ((NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).stepDistOrSelf c).toMeasure _ = 0
        rw [PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
        intro d hd hbad
        obtain ⟨s, t, happ, heq⟩ :=
          support_applicable_pair c d (by rw [hc.2.1]; exact hn) hd
        apply hbad
        rw [← heq]
        exact Or.inr (uniform_conflict_pair_advances
          9 (Or.inr rfl) u hconf.1 hconf.2 c hpure hu s t happ)
      rw [rank_integral_zero_of_target init u c hzero]
      exact zero_le
    · have hnonempty : u.val ≠ 0 := by
        intro hz
        have hu0 : u = (0 : Fin 8) := Fin.ext hz
        have hf := opinion_zero_pairwiseFixed 9 (Or.inr rfl)
          c hpure (by simpa only [hu0] using hu)
        have he := phase_nine_endpoint_of_fixed init hinput c hc.1 hpure hf
        exact htarget (Or.inl (Or.inr (Or.inr (Or.inl he))))
      have hsign := uniform_signs u hnonempty hconf n c hc.2.1 hpure hu
      calc
        _ ≤ ∫⁻ d, (wrongOutputCount9 (opinionVerdict u) d : ℝ≥0∞)
            ∂(NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel c := by
          apply lintegral_mono
          intro d
          by_cases hd : d ∈ phaseWorkTarget 9 init
          · simp [cleanupRank, hd]
          · simp only [cleanupRank, if_neg hd, if_neg hconf, le_refl]
        _ ≤ phase9CleanupRate n *
            (wrongOutputCount9 (opinionVerdict u) c : ℝ≥0∞) :=
          wrongOutputCount9_drift (opinionVerdict u) n hn c hsign
        _ = _ := by simp only [cleanupRank, if_neg htarget, if_neg hconf]

/-- Three logarithmic windows pay a fifth-power tail at rate two over n. -/
theorem cleanup_geometric_budget (n : ℕ) (hn : 2 ≤ n) :
    phase9CleanupRate n ^ logWindow n 3 * (n : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 5) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hfrac :
      phase9CleanupB n / ((n : ℝ) * ((n : ℝ) - 1)) = 2 / (n : ℝ) := by
    unfold phase9CleanupB
    have hsub : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hnpos.ne', hsub]
  have hrate : phase9CleanupRate n = ENNReal.ofReal (1 - 2 / (n : ℝ)) := by
    rw [phase9CleanupRate, hfrac, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (by positivity : 0 ≤ 2 / (n : ℝ))]
  have hr : 0 ≤ 1 - 2 / (n : ℝ) := by
    have : 2 / (n : ℝ) ≤ 1 := (div_le_one hnpos).2 hnR
    linarith
  have hx : 0 ≤ 2 / (n : ℝ) := by positivity
  have hceil : 3 * (n : ℝ) * Real.log n ≤ (logWindow n 3 : ℝ) := by
    exact Nat.le_ceil _
  have hscale : 6 * Real.log n ≤
      (2 / (n : ℝ)) * (logWindow n 3 : ℝ) := by
    calc
      6 * Real.log n = (2 / (n : ℝ)) * (3 * (n : ℝ) * Real.log n) := by
        field_simp [hnpos.ne']
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hceil hx
  have hexp : 1 - 2 / (n : ℝ) ≤ Real.exp (-(2 / (n : ℝ))) := by
    linarith [Real.add_one_le_exp (-(2 / (n : ℝ)))]
  have heval :
      Real.exp (-(6 * Real.log n)) * (n : ℝ) = 1 / (n : ℝ) ^ 5 := by
    have hlog : 6 * Real.log n = Real.log ((n : ℝ) ^ 6) := by
      rw [Real.log_pow]
      norm_num
    rw [hlog, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp [hnpos.ne']
    <;> ring
  have hreal :
      (1 - 2 / (n : ℝ)) ^ logWindow n 3 * (n : ℝ) ≤ 1 / (n : ℝ) ^ 5 := by
    calc
      _ ≤ Real.exp (-(2 / (n : ℝ))) ^ logWindow n 3 * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hexp _) hnpos.le
      _ = Real.exp (-((2 / (n : ℝ)) * (logWindow n 3 : ℝ))) * (n : ℝ) := by
        rw [← Real.exp_nat_mul]
        congr 2
        ring
      _ ≤ Real.exp (-(6 * Real.log n)) * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hnpos.le
        rw [Real.exp_le_exp]
        linarith
      _ = _ := heval
  rw [hrate, ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_mul (pow_nonneg hr _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem cleanup_kernel_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (c : InputCfg n)
    (hreach : ReachableFrom (PhaseThreeModel.Numeric.hourIndex n) 256 init c)
    (hcard : c.card = n) (hpure : PurePhase 9 c) (hu : UniformOpinions c) :
    ((NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel ^ logWindow n 3) c (phaseWorkTarget 9 init)ᶜ ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 5) := by
  classical
  obtain ⟨u, hu⟩ := hu
  have hn : 2 ≤ n := by
    have := (time_population_bounds hinput.1).2
    omega
  have hc : CleanupInv init u n c := ⟨hreach, hcard, Or.inr ⟨hpure, hu⟩⟩
  have htail := DriftSurvival.real_tail_le_drift_plus_escape
    (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel
    (CleanupInv init u n) (cleanupRank init u) (phase9CleanupRate n)
    (fun d hd => cleanupRank_drift init hinput u d hd)
    0 (fun d hd => le_of_eq (cleanupInv_kernel_escape_zero init u n hn d hd))
    (logWindow n 3) c hc
  have hsub : (phaseWorkTarget 9 init)ᶜ ⊆
      {d | ¬ (CleanupInv init u n d ∧ cleanupRank init u d = 0)} := by
    rintro d hd ⟨hi, hz⟩
    exact hd (cleanupRank_zero_target init hinput u d hi hz)
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ phase9CleanupRate n ^ logWindow n 3 *
        (cleanupRank init u c : ℝ≥0∞) := by simpa only [mul_zero, add_zero] using htail
    _ ≤ phase9CleanupRate n ^ logWindow n 3 * (n : ℝ≥0∞) := by
      gcongr
      exact_mod_cast cleanupRank_le_population init u n (by omega) c hcard
    _ ≤ _ := cleanup_geometric_budget n hn

/-- The cleanup estimate is relative to any observed prefix event; there
is no restriction of the scheduler to a future success event. -/
theorem cleanup_prefix_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (s : ℕ)
    (A : Set ((k : Finset.Iic s) →
      Draw (PhaseThreeModel.Numeric.hourIndex n) 256))
    (hA : ∀ a ∈ A, PurePhase 9 (prefixCfg init s a) ∧
      UniformOpinions (prefixCfg init s a)) :
    law init {ω | frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
      ¬ StableOrSeed init 10 (trace init ω (s + logWindow n 3))} ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 5) *
          law init {ω | frestrictLe (π := fun _ : ℕ =>
            Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} := by
  apply PhaseTwoThresholds.recorded_prefix_endpoint_bound
    init s (logWindow n 3) A {c | ¬ StableOrSeed init 10 c} _
  intro a ha
  apply (measure_mono ?_).trans
    (cleanup_kernel_tail init hinput (prefixCfg init s a)
      (prefix_reachable init s a) ((prefix_card init s a).trans hinput.2.2)
      (hA a ha).1 (hA a ha).2)
  intro c hc ht
  rcases ht with hs | ⟨b, hb, hp⟩
  · exact hc (Or.inl hs)
  · exact hc (Or.inr ⟨b, hb, by omega⟩)

end Ripple.PopulationProtocol.ExactMajority.PhaseNineContinuationCleanup

end

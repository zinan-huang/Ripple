-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockRawCapDeadline.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHalfChain
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockSpreadContraction
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFirstPositiveSplice

/-!
A direct raw-interaction all-cap estimate. No shape or hour-window event is a
premise. Half of the Clock population advances one level in each block of
25 n interactions, except with probability exp(-C/10). At the cap, the
remaining Clock population is an epidemic with contraction 1 - 1/(5 n).
The whole construction is performed under the original law, with the
probability of every observed prefix retained.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRawCapDeadline

open TimeTheorem PairLog PhaseThreeModel.Numeric
open PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockProbabilityFloors
open PhaseThreeClockFirstPositive PhaseThreeClockFirstPositiveSplice
open PhaseThreeClockNextFrontBirth PhaseThreeClockHalfPassage
open PhaseThreeClockHalfChain PhaseThreeClockSpreadContraction

variable {n : ℕ}

def rawCapHorizon (n : ℕ) : ℕ :=
  25 * n * clockCap n + logWindow n 60

theorem raw_cap_numerics (C : ℕ) (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * n ≤ C) (hCn : C ≤ n) :
    10 ≤ C ∧ 2 ≤ n ∧ rawCapHorizon n ≤ logWindow n 16000 ∧
      (clockCap n : ℝ) * Real.exp (-(C : ℝ) / 10) +
        1 / (n : ℝ) ^ 11 ≤ 2 / (n : ℝ) ^ 11 := by
  obtain ⟨hCp, hx, hxy, hyx, hdouble, -, -, -, hH, -, hxC, hQC, -, -⟩ :=
    numeric_calibration_core hn hlo hCn
  have hCten : (10 : ℝ) ≤ C := by linarith only [hx, hxC]
  have hC : 10 ≤ C := by exact_mod_cast hCten
  have hnNat : 2 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnp : (0 : ℝ) < n := by positivity
  have hlog : (1 : ℝ) ≤ Real.log (n : ℝ) := by linarith only [hx, hxy]
  have hprod : (1 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    simpa only [one_mul] using mul_le_mul hnR hlog (by norm_num : (0 : ℝ) ≤ 1) hnp.le
  have htime : rawCapHorizon n ≤ logWindow n 16000 := by
    have hceil : (logWindow n 60 : ℝ) ≤
        60 * (n : ℝ) * Real.log (n : ℝ) + 1 :=
      (Nat.ceil_lt_add_one (show 0 ≤ 60 * (n : ℝ) * Real.log (n : ℝ) by positivity)).le
    have hHm := mul_le_mul_of_nonneg_left hH
      (show 0 ≤ 6400 * (n : ℝ) by positivity)
    have hraw : (rawCapHorizon n : ℝ) ≤
        16000 * (n : ℝ) * Real.log (n : ℝ) := by
      simp only [rawCapHorizon, clockCap, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      nlinarith only [hHm, hceil, hprod]
    exact Nat.cast_le.mp (hraw.trans (Nat.le_ceil _))
  have hexp : Real.exp (-(C : ℝ) / 10) ≤ 1 / (n : ℝ) ^ 12 := by
    have hlogC : 0 ≤ Real.log (C : ℝ) := by linarith
    have hrate : 12 * Real.log (n : ℝ) ≤ (C : ℝ) / 10 := by
      linarith only [hyx, hdouble, hxC, hlogC]
    have he : Real.exp (12 * Real.log (n : ℝ)) = (n : ℝ) ^ 12 := by
      change Real.exp ((12 : ℕ) * Real.log (n : ℝ)) = _
      rw [Real.exp_nat_mul, Real.exp_log hnp]
    calc
      _ ≤ Real.exp (-(12 * Real.log (n : ℝ))) :=
        Real.exp_le_exp.mpr (by rw [neg_div]; linarith)
      _ = _ := by rw [Real.exp_neg, he, one_div]
  have hQn : clockCap n ≤ n := hQC.trans hCn
  have hterm : (clockCap n : ℝ) * Real.exp (-(C : ℝ) / 10) ≤
      1 / (n : ℝ) ^ 11 := by
    calc
      _ ≤ (n : ℝ) * Real.exp (-(C : ℝ) / 10) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hQn) (Real.exp_nonneg _)
      _ ≤ (n : ℝ) * (1 / (n : ℝ) ^ 12) :=
        mul_le_mul_of_nonneg_left hexp hnp.le
      _ = _ := by field_simp [ne_of_gt hnp] <;> ring
  have h2 : 2 / (n : ℝ) ^ 11 = 1 / (n : ℝ) ^ 11 + 1 / (n : ℝ) ^ 11 := by ring
  exact ⟨hC, hnNat, htime, by linarith [h2]⟩

theorem raw_cap_fixed_count_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (hcard : init.card = n)
    (C s : ℕ) (hCn : C ≤ n) (hdensity : 6 * n ≤ 25 * C)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω s ∧
      clockCount (virtualLabels init ω s) = C) :
    law init (E ∩ {ω | frontCount
      (virtualLabels init ω (s + rawCapHorizon n)) (clockCap n) < C}) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 11) * law init E := by
  have hlo : (6 / 25 : ℝ) * n ≤ C := by
    have hd : 6 * (n : ℝ) ≤ 25 * C := by exact_mod_cast hdensity
    linarith
  obtain ⟨hC, hnNat, -, hcoef⟩ := raw_cap_numerics C hn hlo hCn
  have hm : 2 ≤ init.card := by simpa only [hcard] using hnNat
  have hCm : C ≤ init.card := by simpa only [hcard] using hCn
  have hd : 6 * init.card ≤ 25 * C := by simpa only [hcard] using hdensity
  let Q := clockCap n
  let t := s + 25 * n * Q
  let N := logWindow n 60
  let A : Set (InputLog n) :=
    E ∩ {ω | halfCount C ≤ frontCount (virtualLabels init ω t) Q}
  have hst : s ≤ t := by dsimp only [t]; omega
  have hQ : Q ≤ 256 * (hourIndex n + 1) := le_rfl
  have hQpos : 1 ≤ Q := by dsimp only [Q, clockCap, clockHours]; omega
  have hA : MeasurableSet[pairLogFiltration _ _ t] A :=
    (((pairLogFiltration _ _).mono hst) _ hE).inter
      ((measurable_virtualLabels init t)
        (Set.to_countable {f : Fin init.card → AgentState (hourIndex n) 256 | halfCount C ≤ frontCount f Q}).measurableSet)
  have hstartA : A ⊆ spreadStart init C Q t := by
    rintro ω ⟨he, hp⟩
    have hu := (hstart ω he).1
    refine ⟨homogeneousStart_of_time init ω s hu t hst, ?_, hp⟩
    exact (congrArg Finset.card
      (clockSet_fixed_from_homogeneous init ω s hu t hst)).trans (hstart ω he).2
  have hhalf := half_chain_prefix_tail init hm C s Q hC hCm hd hQ E hE hstart
  have hspread := spread_prefix_tail init hm C Q t N (by omega) hCm hd hQpos hQ
    (by simpa only [hcard, N, logWindow] using
      (Nat.le_ceil (60 * (n : ℝ) * Real.log (n : ℝ)))) A hA hstartA
  have hcover :
      E ∩ {ω | frontCount (virtualLabels init ω (t + N)) Q < C} ⊆
      (E ∩ {ω | frontCount (virtualLabels init ω t) Q < halfCount C}) ∪
      (A ∩ {ω | frontCount (virtualLabels init ω (t + N)) Q < C}) := by
    rintro ω ⟨he, hb⟩
    by_cases hp : halfCount C ≤ frontCount (virtualLabels init ω t) Q
    · exact Or.inr ⟨⟨he, hp⟩, hb⟩
    · exact Or.inl ⟨he, Nat.lt_of_not_ge hp⟩
  have hcoefE :
      (Q : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(C : ℝ) / 10)) +
        ENNReal.ofReal (1 / (n : ℝ) ^ 11) ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 11) := by
    have h := ENNReal.ofReal_le_ofReal hcoef
    have hq0 : (0 : ℝ) ≤ ((clockCap n : ℕ) : ℝ) * Real.exp (-(C : ℝ) / 10) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
    have hn0 : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 11 := by positivity
    rw [ENNReal.ofReal_add hq0 hn0, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast] at h
    exact h
  have htime : t + N = s + rawCapHorizon n := by
    dsimp only [t, N, rawCapHorizon, Q]
    omega
  rw [← htime]
  calc
    _ ≤ law init ((E ∩ {ω | frontCount (virtualLabels init ω t) Q < halfCount C}) ∪
        (A ∩ {ω | frontCount (virtualLabels init ω (t + N)) Q < C})) := measure_mono hcover
    _ ≤ law init (E ∩ {ω | frontCount (virtualLabels init ω t) Q < halfCount C}) +
        law init (A ∩ {ω | frontCount (virtualLabels init ω (t + N)) Q < C}) :=
      measure_union_le _ _
    _ ≤ (Q : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(C : ℝ) / 10)) * law init E +
        ENNReal.ofReal (1 / (n : ℝ) ^ 11) * law init E := by
      apply add_le_add
      · simpa only [hcard, t] using hhalf
      · simpa only [hcard] using hspread.trans
          (mul_le_mul_left' (measure_mono (show A ⊆ E from Set.inter_subset_left)) _)
    _ = ((Q : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(C : ℝ) / 10)) +
        ENNReal.ofReal (1 / (n : ℝ) ^ 11)) * law init E := by ring
    _ ≤ _ := mul_le_mul_right' hcoefE _

/-- Concrete all-cap failure at a deterministic observed homogeneous start,
with the random number of Clocks summed out without losing the prefix factor. -/
theorem raw_cap_dense_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (hcard : init.card = n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hstart : ∀ ω ∈ E, DenseHomogeneousStart init ω s) :
    law init (E ∩ {ω | frontCount
      (virtualLabels init ω (s + rawCapHorizon n)) (clockCap n) <
        clockCount (virtualLabels init ω s)}) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 11) * law init E := by
  let A : ℕ → Set (InputLog n) :=
    fun C => E ∩ {ω | clockCount (virtualLabels init ω s) = C}
  let B : ℕ → Set (InputLog n) :=
    fun C => {ω | frontCount (virtualLabels init ω (s + rawCapHorizon n)) (clockCap n) < C}
  have hAm (C : ℕ) : MeasurableSet[pairLogFiltration _ _ s] (A C) :=
    hE.inter ((measurable_virtualLabels init s)
      (Set.to_countable {f : Fin init.card → AgentState (hourIndex n) 256 | clockCount f = C}).measurableSet)
  have hdisj : Pairwise (fun C D => Disjoint (A C) (A D)) := by
    intro C D hCD
    apply Set.disjoint_left.mpr
    rintro ω ⟨-, hc⟩ ⟨-, hd⟩
    exact hCD (hc.symm.trans hd)
  have hunion : (⋃ C, A C) = E := by
    ext ω
    constructor
    · intro h
      obtain ⟨C, he, -⟩ := Set.mem_iUnion.mp h
      exact he
    · intro he
      exact Set.mem_iUnion.mpr ⟨clockCount (virtualLabels init ω s), he, rfl⟩
  have hcover :
      E ∩ {ω | frontCount (virtualLabels init ω (s + rawCapHorizon n)) (clockCap n) <
        clockCount (virtualLabels init ω s)} ⊆ ⋃ C, A C ∩ B C := by
    rintro ω ⟨he, hb⟩
    exact Set.mem_iUnion.mpr ⟨clockCount (virtualLabels init ω s), ⟨he, rfl⟩, hb⟩
  have hlocal (C : ℕ) :
      law init (A C ∩ B C) ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 11) * law init (A C) := by
    by_cases hne : (A C).Nonempty
    · obtain ⟨ω, he, hc⟩ := hne
      have hc' : clockCount (virtualLabels init ω s) = C := hc
      have hCn : C ≤ n := by
        simpa only [hc', hcard] using clockCount_le_card (virtualLabels init ω s)
      have hd : 6 * n ≤ 25 * C := by
        simpa only [hc', hcard] using (hstart ω he).2.2
      exact raw_cap_fixed_count_prefix_tail init hn hcard C s hCn hd (A C) (hAm C)
        (fun ω hω => ⟨(hstart ω hω.1).1, hω.2⟩)
    · have hempty := Set.not_nonempty_iff_eq_empty.mp hne
      simp only [hempty, Set.empty_inter, measure_empty, mul_zero, le_refl]
  calc
    _ ≤ law init (⋃ C, A C ∩ B C) := measure_mono hcover
    _ ≤ ∑' C, law init (A C ∩ B C) := measure_iUnion_le _
    _ ≤ ∑' C, ENNReal.ofReal (2 / (n : ℝ) ^ 11) * law init (A C) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal (2 / (n : ℝ) ^ 11) * ∑' C, law init (A C) := by
      rw [ENNReal.tsum_mul_left]
    _ = _ := by
      rw [← measure_iUnion hdisj
        (fun C => (pairLogFiltration _ _).le s _ (hAm C)), hunion]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRawCapDeadline

end

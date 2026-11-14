-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockHalfPassage.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockStoppedPassage
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNextFrontBirth

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHalfPassage

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
open PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
open PhaseThreeClockEmbeddingBridge PhaseThreeClockProbabilityFloors
open PhaseThreeClockPrefixTails PhaseThreeClockStoppedPassage
open PhaseThreeClockFirstPositive PhaseThreeClockNextFrontBirth PhaseThreeClockThinning

variable {L m : ℕ}

def halfCount (C : ℕ) : ℕ := (C + 1) / 2

theorem halfCount_bounds (C : ℕ) :
    C ≤ 2 * halfCount C ∧ 2 * halfCount C ≤ C + 1 ∧ halfCount C ≤ C := by
  unfold halfCount
  omega

theorem half_pair_polynomial (C b x y : ℝ)
    (hC : 10 ≤ C) (hb : C ≤ 2 * b) (hb' : 2 * b ≤ C + 1)
    (hx : b ≤ x) (hy : 0 ≤ y) (hyb : y + 1 ≤ b) :
    C ^ 2 ≤ 5 * (2 * y * (C - y) + (x - y) * (x - y - 1)) := by
  have hbase := mul_nonneg (sub_nonneg.mpr hb)
    (show 0 ≤ 2 * b + C - 2 by linarith)
  have hlarge := mul_nonneg (show 0 ≤ C by linarith)
    (show 0 ≤ C - 10 by linarith)
  have hxterm := mul_nonneg (sub_nonneg.mpr hx)
    (show 0 ≤ x + b - 2 * y - 1 by linarith)
  have hyterm := mul_nonneg hy
    (show 0 ≤ 2 * C - 2 * b + 1 - y by linarith)
  nlinarith only [hbase, hlarge, hxterm, hyterm]

theorem gated_pairs_eq_raising_of_all_three
    (f : Fin m → AgentState L 256) (hphase : ∀ i, (f i).phase.val = 3)
    (ell : ℕ) :
    goodPairs (GatedTick ell) f = goodPairs (RaisingTick ell) f := by
  classical
  ext ⟨i, j⟩
  simp only [goodPairs, GatedTick, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hg, _⟩
    exact ⟨hne, hg⟩
  · rintro ⟨hne, hg⟩
    exact ⟨hne, hg, Or.inl (by rw [hphase i])⟩

theorem half_gated_pair_floor
    (f : Fin m → AgentState L 256) (hphase : ∀ i, (f i).phase.val = 3)
    (ell C : ℕ) (hell : 1 ≤ ell) (hC : 10 ≤ C)
    (hcount : clockCount f = C)
    (hprev : halfCount C ≤ frontCount f (ell - 1))
    (hbelow : frontCount f ell < halfCount C) :
    (C : ℝ) ^ 2 ≤ 5 * ((goodPairs (GatedTick ell) f).card : ℝ) := by
  have hsplit := frontCount_pred f ell hell
  have hepos : 1 ≤ exactCount f (ell - 1) := by omega
  have hyC : frontCount f ell ≤ C := by
    simpa only [hcount] using frontCount_le_clockCount f ell
  have hpair := goodPairs_raisingTick_card f ell
  rw [← gated_pairs_eq_raising_of_all_three f hphase ell, hcount] at hpair
  have hpairR :
      ((goodPairs (GatedTick ell) f).card : ℝ) =
        2 * (frontCount f ell : ℝ) * ((C : ℝ) - frontCount f ell) +
          (exactCount f (ell - 1) : ℝ) * ((exactCount f (ell - 1) : ℝ) - 1) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub hyC, Nat.cast_sub hepos, Nat.cast_one] using
        congrArg (fun k : ℕ => (k : ℝ)) hpair
  have hsplitR : (frontCount f (ell - 1) : ℝ) =
      (frontCount f ell : ℝ) + (exactCount f (ell - 1) : ℝ) := by
    exact_mod_cast hsplit
  have hb := halfCount_bounds C
  have hx := half_pair_polynomial (C : ℝ) (halfCount C : ℝ)
    (frontCount f (ell - 1) : ℝ) (frontCount f ell : ℝ)
    (by exact_mod_cast hC) (by exact_mod_cast hb.1)
    (by exact_mod_cast hb.2.1) (by exact_mod_cast hprev) (by positivity)
    (by exact_mod_cast (show frontCount f ell + 1 ≤ halfCount C by omega))
  rw [hpairR]
  nlinarith only [hx, hsplitR]

theorem half_raw_rate_floor
    (f : Fin m → AgentState L 256) (hm : 2 ≤ m)
    (hphase : ∀ i, (f i).phase.val = 3)
    (ell C : ℕ) (hell : 1 ≤ ell) (hC : 10 ≤ C)
    (hdensity : 6 * m ≤ 25 * C) (hcount : clockCount f = C)
    (hprev : halfCount C ≤ frontCount f (ell - 1))
    (hbelow : frontCount f ell < halfCount C) :
    (C : ℝ) / (25 * (m : ℝ)) ≤
      ((goodPairs (GatedTick ell) f).card : ℝ) /
        ((m : ℝ) * ((m : ℝ) - 1)) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hCR : (0 : ℝ) ≤ C := by positivity
  have hdR : 6 * (m : ℝ) ≤ 25 * (C : ℝ) := by exact_mod_cast hdensity
  have hp := half_gated_pair_floor f hphase ell C hell hC hcount hprev hbelow
  have hroom := mul_nonneg hCR (show 0 ≤ 5 * (C : ℝ) - ((m : ℝ) - 1) by linarith)
  have hinner :
      (C : ℝ) / 25 ≤
        ((goodPairs (GatedTick ell) f).card : ℝ) / ((m : ℝ) - 1) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 25)
      (by linarith : 0 < (m : ℝ) - 1)).2
    nlinarith only [hp, hroom]
  simpa only [div_div, mul_comm] using
    div_le_div_of_nonneg_right hinner (show (0 : ℝ) ≤ m by positivity)

structure HalfWindow (f : Fin m → AgentState L 256) (ell C : ℕ) : Prop where
  all_three : ∀ i, (f i).phase.val = 3
  carrier : ∀ i, nonMainCarrierSmallBiasZeroAgent (f i)
  count : clockCount f = C
  previous : halfCount C ≤ frontCount f (ell - 1)
  below : frontCount f ell < halfCount C

open Classical in
def halfStop (init : Cfg L 256) (ell C s : ℕ) (ω : Ω L 256) : WithTop ℕ :=
  if h : ∃ t, ¬ HalfWindow (virtualLabels init ω (s + t)) ell C
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem halfStop_le_iff (init : Cfg L 256) (ell C s t : ℕ) (ω : Ω L 256) :
    halfStop init ell C s ω ≤ (t : WithTop ℕ) ↔
      ∃ u ≤ t, ¬ HalfWindow (virtualLabels init ω (s + u)) ell C := by
  classical
  unfold halfStop
  split_ifs with h
  · constructor
    · intro ht
      exact ⟨Nat.find h, by exact_mod_cast ht, Nat.find_spec h⟩
    · rintro ⟨u, hut, hu⟩
      exact_mod_cast (Nat.find_min' h hu).trans hut
  · constructor
    · intro ht
      exact absurd ht (by simp)
    · rintro ⟨u, _, hu⟩
      exact (h ⟨u, hu⟩).elim

theorem halfWindow_of_lt_stop (init : Cfg L 256) (ell C s N : ℕ)
    (ω : Ω L 256) (hN : (N : WithTop ℕ) < halfStop init ell C s ω) :
    ∀ u ≤ N, HalfWindow (virtualLabels init ω (s + u)) ell C := by
  intro u hu
  by_contra hbad
  exact (not_lt_of_ge ((halfStop_le_iff init ell C s N ω).2 ⟨u, hu, hbad⟩)) hN

theorem halfWindow_measurable (init : Cfg L 256) (ell C s t : ℕ) :
    MeasurableSet[shiftedFiltration (pairLogFiltration L 256) s t]
      {ω | HalfWindow (virtualLabels init ω (s + t)) ell C} := by
  change MeasurableSet[pairLogFiltration L 256 (s + t)] _
  exact (measurable_virtualLabels init (s + t))
    (Set.to_countable {f : Fin init.card → AgentState L 256 |
      HalfWindow f ell C}).measurableSet

theorem halfStop_isStoppingTime (init : Cfg L 256) (ell C s : ℕ) :
    IsStoppingTime (shiftedFiltration (pairLogFiltration L 256) s)
      (halfStop init ell C s) := by
  intro t
  have hm : MeasurableSet[shiftedFiltration (pairLogFiltration L 256) s t]
      (⋃ u : ℕ, {ω | u ≤ t ∧ ¬ HalfWindow (virtualLabels init ω (s + u)) ell C}) := by
    refine MeasurableSet.iUnion fun u => ?_
    by_cases hu : u ≤ t
    · have hw := ((shiftedFiltration (pairLogFiltration L 256) s).mono hu) _
        (halfWindow_measurable init ell C s u).compl
      simpa only [hu, true_and] using hw
    · simp only [hu, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact halfStop_le_iff init ell C s t ω

theorem front_step_of_homogeneous (init : Cfg L 256) (ω : Ω L 256)
    (t ell : ℕ) (hell : 1 ≤ ell) (hcap : ell ≤ 256 * (L + 1))
    (hcur : HomogeneousStart init ω t) :
    (frontCount (virtualLabels init ω (t + 1)) ell : ℝ) =
      (frontCount (virtualLabels init ω t) ell : ℝ) + gatedIndicator init ell t ω := by
  classical
  have hnext := homogeneousStart_of_time init ω t hcur (t + 1) (by omega)
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      have h := frontCount_virtualLabels_succ_of_none init ω t hd ell
      simp only [gatedIndicator, hd, reduceCtorEq, false_and, exists_false,
        if_false, add_zero]
      exact_mod_cast h
  | some ij =>
      rcases ij with ⟨i, j⟩
      have h := frontCount_virtualLabels_succ_of_phase_range init ω t i j hd
        (fun k => by have := hcur.1 k; constructor <;> omega)
        (fun k hk => hcur.2 k (Or.inr (Or.inr hk)))
        (fun k => (hnext.1 k).le) ell hell hcap
      have hevent :
          (∃ a b, drawLabels init ω (t + 1) = some (a, b) ∧
            GatedTick ell (auxLabels init virtualRule ω t) a b) ↔
          GatedTick ell (virtualLabels init ω t) i j := by
        simp only [hd, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨a, b, ⟨rfl, rfl⟩, hg⟩
          exact hg
        · intro hg
          exact ⟨i, j, ⟨rfl, rfl⟩, hg⟩
      have hr :
          (frontCount (virtualLabels init ω (t + 1)) ell : ℝ) =
            (frontCount (virtualLabels init ω t) ell : ℝ) +
              if GatedTick ell (virtualLabels init ω t) i j then (1 : ℝ) else 0 := by
        by_cases hg : GatedTick ell (virtualLabels init ω t) i j
        · rw [if_pos hg] at h ⊢
          exact_mod_cast h
        · rw [if_neg hg] at h ⊢
          exact_mod_cast h
      simpa only [gatedIndicator, hevent] using hr

theorem half_survival_count (init : Cfg L 256) (ω : Ω L 256)
    (ell C s N : ℕ) (hell : 1 ≤ ell) (hcap : ell ≤ 256 * (L + 1))
    (hN : (N : WithTop ℕ) < halfStop init ell C s ω) :
    bernoulliCount (fun t => gatedIndicator init ell (s + t)) N ω < (halfCount C : ℝ) := by
  have hw := halfWindow_of_lt_stop init ell C s N ω hN
  have htel : ∀ r, r ≤ N →
      (frontCount (virtualLabels init ω (s + r)) ell : ℝ) =
        (frontCount (virtualLabels init ω s) ell : ℝ) +
          bernoulliCount (fun t => gatedIndicator init ell (s + t)) r ω := by
    intro r
    induction r with
    | zero =>
        intro hr
        simp [bernoulliCount]
    | succ r ih =>
        intro hr
        have hp := ih (by omega)
        have hs := front_step_of_homogeneous init ω (s + r) ell hell hcap
          ⟨(hw r (by omega)).all_three, (hw r (by omega)).carrier⟩
        simpa only [Nat.add_assoc, bernoulliCount, Finset.sum_range_succ,
          add_assoc] using hs.trans
            (congrArg (fun z : ℝ => z + gatedIndicator init ell (s + r) ω) hp)
  have hbelow : (frontCount (virtualLabels init ω (s + N)) ell : ℝ) <
      (halfCount C : ℝ) := by exact_mod_cast (hw N le_rfl).below
  have hz : 0 ≤ (frontCount (virtualLabels init ω s) ell : ℝ) := by positivity
  linarith [htel N le_rfl]

theorem half_stop_prefix_tail (init : Cfg L 256) (hm : 2 ≤ init.card)
    (C ell s : ℕ) (hC : 10 ≤ C) (hCm : C ≤ init.card)
    (hdensity : 6 * init.card ≤ 25 * C)
    (hell : 1 ≤ ell) (hcap : ell ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E) :
    law init (E ∩ {ω | ((25 * init.card : ℕ) : WithTop ℕ) < halfStop init ell C s ω}) ≤
      ENNReal.ofReal (Real.exp (-(C : ℝ) / 10)) * law init E := by
  classical
  let ℱ := shiftedFiltration (pairLogFiltration L 256) s
  let I : ℕ → Ω L 256 → ℝ := fun t => gatedIndicator init ell (s + t)
  let p : ℝ := (C : ℝ) / (25 * (init.card : ℝ))
  have hmR : (2 : ℝ) ≤ init.card := by exact_mod_cast hm
  have hCR : (10 : ℝ) ≤ C := by exact_mod_cast hC
  have hCmR : (C : ℝ) ≤ init.card := by exact_mod_cast hCm
  have hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t) := by
    intro t
    simpa only [ℱ, I, shiftedFiltration_apply, Nat.add_assoc, gatedIndicator] using
      stronglyMeasurable_aux_pair_indicator init virtualRule (GatedTick ell) (s + t)
  have hzero : ∀ t, ∀ᵐ ω ∂law init, I t ω = 0 ∨ I t ω = 1 :=
    fun t => ae_of_all _ (gatedIndicator_zero_one init ell (s + t))
  have hcond : ∀ t : ℕ, ∀ᵐ ω ∂law init,
      (t : WithTop ℕ) < halfStop init ell C s ω →
        p ≤ ((law init)[I t | ℱ t]) ω := by
    intro t
    have he := gatedTick_conditional_law init hm ell (s + t)
    have he' : (law init)[I t | ℱ t] =ᵐ[law init]
        fun ω => ((goodPairs (GatedTick ell) (virtualLabels init ω (s + t))).card : ℝ) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
      change (law init)[fun ω => gatedIndicator init ell (s + t) ω |
        pairLogFiltration L 256 (s + t)] =ᵐ[law init] _
      simpa only [gatedIndicator] using he
    filter_upwards [he'] with ω heω
    intro ht
    rw [heω]
    have hw := halfWindow_of_lt_stop init ell C s t ω ht t le_rfl
    exact half_raw_rate_floor _ hm hw.all_three ell C hell hC hdensity
      hw.count hw.previous hw.below
  have hp : p ≤ 1 := by
    dsimp only [p]
    apply (div_le_iff₀ (by positivity : 0 < 25 * (init.card : ℝ))).2
    linarith
  have ht := prefix_success_hitting_tail hI hzero
    (halfStop_isStoppingTime init ell C s) hp hcond E
    (by simpa only [ℱ, shiftedFiltration_apply, Nat.add_zero] using hE)
    (25 * init.card) (halfCount C : ℝ)
    (fun ω _ hsur => half_survival_count init ω ell C s _ hell hcap hsur)
  have hexp : (halfCount C : ℝ) * Real.log 2 - p * (25 * init.card : ℕ) / 2 ≤
      -(C : ℝ) / 10 := by
    have hb : 2 * (halfCount C : ℝ) ≤ (C : ℝ) + 1 := by
      exact_mod_cast (halfCount_bounds C).2.1
    have hl := mul_le_mul_of_nonneg_left PhaseThreeModel.Numeric.log_two_bounds.2
      (show (0 : ℝ) ≤ halfCount C by positivity)
    have hpN : p * (25 * init.card : ℕ) = (C : ℝ) := by
      dsimp only [p]
      push_cast
      field_simp [show (init.card : ℝ) ≠ 0 by linarith]
    rw [hpN]
    linarith
  have hr := ht.trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity : 0 ≤ (law init).real E))
  exact measure_le_of_real_weighted_bound (law init) _ E _
    (Real.exp_nonneg _) hr

theorem half_below_implies_survival (init : Cfg L 256) (ω : Ω L 256)
    (C ell s N : ℕ) (hstart : HomogeneousStart init ω s)
    (hcount : clockCount (virtualLabels init ω s) = C)
    (hprev : halfCount C ≤ frontCount (virtualLabels init ω s) (ell - 1))
    (hbelow : frontCount (virtualLabels init ω (s + N)) ell < halfCount C) :
    (N : WithTop ℕ) < halfStop init ell C s ω := by
  apply lt_of_not_ge
  intro hs
  obtain ⟨u, hu, hbad⟩ := (halfStop_le_iff init ell C s N ω).mp hs
  apply hbad
  have hhom := homogeneousStart_of_time init ω s hstart (s + u) (by omega)
  refine ⟨hhom.1, hhom.2, ?_, ?_, ?_⟩
  · have hc := congrArg Finset.card
      (clockSet_fixed_from_homogeneous init ω s hstart (s + u) (by omega))
    exact hc.trans hcount
  · exact hprev.trans (Finset.card_le_card
      (aboveSet_mono_from_homogeneous init ω s hstart s (s + u) le_rfl (by omega) _))
  · exact (Finset.card_le_card
      (aboveSet_mono_from_homogeneous init ω s hstart (s + u) (s + N)
        (by omega) (by omega) ell)).trans_lt hbelow

theorem half_passage_prefix_tail (init : Cfg L 256) (hm : 2 ≤ init.card)
    (C ell s : ℕ) (hC : 10 ≤ C) (hCm : C ≤ init.card)
    (hdensity : 6 * init.card ≤ 25 * C)
    (hell : 1 ≤ ell) (hcap : ell ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E)
    (hstart : ∀ ω ∈ E, HomogeneousStart init ω s ∧
      clockCount (virtualLabels init ω s) = C ∧
      halfCount C ≤ frontCount (virtualLabels init ω s) (ell - 1)) :
    law init (E ∩ {ω |
      frontCount (virtualLabels init ω (s + 25 * init.card)) ell < halfCount C}) ≤
      ENNReal.ofReal (Real.exp (-(C : ℝ) / 10)) * law init E := by
  apply (measure_mono ?_).trans
    (half_stop_prefix_tail init hm C ell s hC hCm hdensity hell hcap E hE)
  rintro ω ⟨he, hb⟩
  exact ⟨he, half_below_implies_survival init ω C ell s _ (hstart ω he).1
    (hstart ω he).2.1 (hstart ω he).2.2 hb⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHalfPassage

end

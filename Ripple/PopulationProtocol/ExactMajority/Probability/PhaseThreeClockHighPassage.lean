-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockHighPassage.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFirstBulkBase

/-!
P8 on the actual asynchronous gated process.  The positive-level epidemic
term survives the level-one gate, so no all-active hypothesis is used.
A raw auxiliary horizon converts two prefix estimates into an 8C-contact
passage estimate.  The future safe environment occurs only in the failure
event, never in the observed conditioning prefix.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHighPassage

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockProbabilityFloors PhaseThreeClockPrefixTails
  PhaseThreeClockStoppedPassage PhaseThreeClockShapeFreeze
  PhaseThreeClockShapeBarrier PhaseThreeClockBulkClockPassage
  PhaseThreeClockThinning PhaseThreeClockFirstBulkBase
  PhaseThreeClockRareDripCharging PhaseThreeClockMarkCoverage
open PhaseThreeModel.Numeric

variable {n : ℕ}

theorem bulkThreshold_le_highThreshold (C : ℕ) :
    StageEventSpec.bulkThreshold C ≤ StageEventSpec.highThreshold C := by
  apply Nat.ceil_mono
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  linarith

theorem highThreshold_sub_bulkThreshold_bound (C : ℕ) :
    (StageEventSpec.highThreshold C : ℝ) -
        (StageEventSpec.bulkThreshold C : ℝ) ≤ (4 / 5 : ℝ) * C + 1 := by
  have hb := Nat.le_ceil ((C : ℝ) / 10)
  have hh := Nat.ceil_lt_add_one
    (show 0 ≤ 9 * (C : ℝ) / 10 by positivity)
  change (C : ℝ) / 10 ≤ StageEventSpec.bulkThreshold C at hb
  change (StageEventSpec.highThreshold C : ℝ) <
    9 * (C : ℝ) / 10 + 1 at hh
  linarith

/-- The 1/6 embedded floor uses only unequal-minute copying. -/
theorem high_passage_raw_floor (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 2 ≤ C.card) (ell : ℕ) (hell : 1 ≤ ell)
    (f : Fin init.card → AgentState (hourIndex n) 256)
    (hcount : clockCount f = C.card)
    (hlow : StageEventSpec.bulkThreshold C.card ≤ frontCount f ell)
    (hhigh : frontCount f ell < StageEventSpec.highThreshold C.card) :
    clockMaskRate init.card C.card / 6 ≤
      ((goodPairs (GatedTick ell) f).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  have hXlow : (C.card : ℝ) / 10 ≤ (frontCount f ell : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hlow)
  have hXhigh : (frontCount f ell : ℝ) < 9 * (C.card : ℝ) / 10 :=
    Nat.lt_ceil.mp hhigh
  have hnonneg := mul_nonneg
    (sub_nonneg.mpr hXlow) (sub_nonneg.mpr hXhigh.le)
  have hCR : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  have hpoly :
      (C.card : ℝ) * ((C.card : ℝ) - 1) / 6 ≤
        2 * (frontCount f ell : ℝ) * ((C.card : ℝ) - (frontCount f ell : ℝ)) := by
    nlinarith [sq_nonneg (C.card : ℝ)]
  have hXC := frontCount_le_clockCount f ell
  have hcounting := epidemic_le_gated_pairs f ell hell
  have hcast :
      2 * (frontCount f ell : ℝ) *
          ((clockCount f : ℝ) - (frontCount f ell : ℝ)) ≤
        ((goodPairs (GatedTick ell) f).card : ℝ) := by
    have hh :
        ((2 * frontCount f ell * (clockCount f - frontCount f ell) : ℕ) : ℝ) ≤
          ((goodPairs (GatedTick ell) f).card : ℝ) := by
      exact_mod_cast hcounting
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hXC] using hh
  rw [hcount] at hcast
  have hcR : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
  have hden : 0 ≤ (init.card : ℝ) * ((init.card : ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hdiv := div_le_div_of_nonneg_right (hpoly.trans hcast) hden
  rw [clockMaskRate_eq_real _ _ (by omega)]
  convert hdiv using 1 <;> ring

def highWindow (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u t : ℕ) (ω : InputLog n) : Prop :=
  shapeSafeAt init C s (u + t) ω ∧
    StageEventSpec.bulkThreshold C.card ≤
      frontCount (virtualLabels init ω (u + t)) ell ∧
    frontCount (virtualLabels init ω (u + t)) ell < StageEventSpec.highThreshold C.card

open Classical in
def highStop (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (ω : InputLog n) : WithTop ℕ :=
  if h : ∃ t, ¬ highWindow init C ell s u t ω
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem highStop_le_iff (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u N : ℕ) (ω : InputLog n) :
    highStop init C ell s u ω ≤ (N : WithTop ℕ) ↔
      ∃ t ≤ N, ¬ highWindow init C ell s u t ω := by
  classical
  unfold highStop
  split_ifs with h
  · constructor
    · intro hle
      exact ⟨Nat.find h, by exact_mod_cast hle, Nat.find_spec h⟩
    · rintro ⟨t, ht, hbad⟩
      exact_mod_cast (Nat.find_min' h hbad).trans ht
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨t, _, hbad⟩
      exact absurd ⟨t, hbad⟩ h

theorem highWindow_of_lt_stop (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u N : ℕ) (ω : InputLog n)
    (hN : (N : WithTop ℕ) < highStop init C ell s u ω) :
    ∀ t ≤ N, highWindow init C ell s u t ω := by
  intro t ht
  by_contra hbad
  exact (not_lt_of_ge
    ((highStop_le_iff init C ell s u N ω).2 ⟨t, ht, hbad⟩)) hN

theorem highWindow_measurable (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u : ℕ) (hsu : s ≤ u) (t : ℕ) :
    MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u t]
      {ω | highWindow init C ell s u t ω} := by
  have hstate : MeasurableSet[pairLogFiltration _ _ (u + t)]
      {ω | StageEventSpec.bulkThreshold C.card ≤
        frontCount (virtualLabels init ω (u + t)) ell ∧
        frontCount (virtualLabels init ω (u + t)) ell <
          StageEventSpec.highThreshold C.card} :=
    (show MeasurableSet {f : Fin init.card → AgentState (hourIndex n) 256 |
      StageEventSpec.bulkThreshold C.card ≤ frontCount f ell ∧
        frontCount f ell < StageEventSpec.highThreshold C.card} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init (u + t))
  exact (shapeSafeAt_measurable init C s (u + t) (by omega)).inter hstate

theorem highStop_isStoppingTime (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u : ℕ) (hsu : s ≤ u) :
    IsStoppingTime (shiftedFiltration (pairLogFiltration _ _) u)
      (highStop init C ell s u) := by
  intro N
  have hm : MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u N]
      (⋃ t : ℕ, {ω | t ≤ N ∧ ¬ highWindow init C ell s u t ω}) := by
    refine MeasurableSet.iUnion fun t => ?_
    by_cases ht : t ≤ N
    · have hbad := ((shiftedFiltration (pairLogFiltration _ _) u).mono ht) _
        (highWindow_measurable init C ell s u hsu t).compl
      simpa only [ht, true_and] using hbad
    · simp only [ht, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact highStop_le_iff init C ell s u N ω

theorem high_survival_count (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u N : ℕ)
    (hell : 1 ≤ ell) (htop : ell ≤ clockCap n) (hsu : s ≤ u)
    (ω : InputLog n) (hN : (N : WithTop ℕ) < highStop init C ell s u ω) :
    bernoulliCount (fun t => gatedIndicator init ell (u + t)) N ω <
      (StageEventSpec.highThreshold C.card : ℝ) -
        (StageEventSpec.bulkThreshold C.card : ℝ) := by
  have hw := highWindow_of_lt_stop init C ell s u N ω hN
  have htel : ∀ r, r ≤ N →
      (frontCount (virtualLabels init ω (u + r)) ell : ℝ) =
        (frontCount (virtualLabels init ω u) ell : ℝ) +
          bernoulliCount (fun t => gatedIndicator init ell (u + t)) r ω := by
    intro r
    induction r with
    | zero =>
        intro hr
        simp [bernoulliCount]
    | succ r ih =>
        intro hr
        have hp := ih (by omega)
        have hs := front_step_safe init C ell 0 s (u + r) (by omega) hell
          htop ω (by simpa only [Nat.add_assoc] using (hw (r + 1) hr).1)
        simpa only [Nat.add_assoc, bernoulliCount, Finset.sum_range_succ, add_assoc] using
          hs.trans (congrArg (fun z : ℝ => z + gatedIndicator init ell (u + r) ω) hp)
  have hbelow : (frontCount (virtualLabels init ω (u + N)) ell : ℝ) <
      (StageEventSpec.highThreshold C.card : ℝ) := by exact_mod_cast (hw N le_rfl).2.2
  have hstart : (StageEventSpec.bulkThreshold C.card : ℝ) ≤
      (frontCount (virtualLabels init ω u) ell : ℝ) := by
    have hh := (hw 0 (Nat.zero_le _)).2.1
    simpa only [Nat.add_zero] using
      (show (StageEventSpec.bulkThreshold C.card : ℝ) ≤
        (frontCount (virtualLabels init ω (u + 0)) ell : ℝ) by exact_mod_cast hh)
  linarith [htel N le_rfl]

def highRawHorizon (init : InputCfg n) (C : Finset (Fin init.card)) : ℕ :=
  Nat.ceil (7 * (C.card : ℝ) / clockMaskRate init.card C.card)

theorem highRawHorizon_bounds (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 2 ≤ C.card) :
    7 * (C.card : ℝ) ≤ clockMaskRate init.card C.card * (highRawHorizon init C : ℝ) ∧
    clockMaskRate init.card C.card * (highRawHorizon init C : ℝ) ≤
      7 * (C.card : ℝ) + 1 := by
  have hq := mask_rate_bounds init hc C hC
  have hl := Nat.le_ceil (7 * (C.card : ℝ) / clockMaskRate init.card C.card)
  have hu := Nat.ceil_lt_add_one
    (show 0 ≤ 7 * (C.card : ℝ) / clockMaskRate init.card C.card from
      div_nonneg (by positivity) hq.1.le)
  have he : clockMaskRate init.card C.card *
      (7 * (C.card : ℝ) / clockMaskRate init.card C.card) = 7 * (C.card : ℝ) := by
    field_simp [hq.1.ne']
  have hlow := mul_le_mul_of_nonneg_left hl hq.1.le
  have hupper := mul_le_mul_of_nonneg_left hu.le hq.1.le
  dsimp only [highRawHorizon]
  rw [he] at hlow
  rw [mul_add, he, mul_one] at hupper
  exact ⟨hlow, by linarith⟩

theorem high_raw_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 100 ≤ C.card)
    (ell s u : ℕ) (hell : 1 ≤ ell) (htop : ell ≤ clockCap n) (hsu : s ≤ u)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ u] E) :
    law init (E ∩ {ω | (highRawHorizon init C : WithTop ℕ) <
      highStop init C ell s u ω}) ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 50)) * law init E := by
  let ℱ := shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) u
  let I : ℕ → InputLog n → ℝ := fun t => gatedIndicator init ell (u + t)
  let p : ℝ := clockMaskRate init.card C.card / 6
  let k : ℝ := (StageEventSpec.highThreshold C.card : ℝ) -
    (StageEventSpec.bulkThreshold C.card : ℝ)
  have hq := mask_rate_bounds init hc C (by omega)
  have hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t) := by
    intro t
    simpa only [ℱ, I, shiftedFiltration_apply, Nat.add_assoc] using
      gatedIndicator_adapted init ell (u + t)
  have hz : ∀ t, ∀ᵐ ω ∂law init, I t ω = 0 ∨ I t ω = 1 :=
    fun t => ae_of_all _ (gatedIndicator_zero_one init ell (u + t))
  have hp : p ≤ 1 := by dsimp only [p]; linarith [hq.2]
  have hcond : ∀ t : ℕ, ∀ᵐ ω ∂law init,
      (t : WithTop ℕ) < highStop init C ell s u ω →
        p ≤ (law init)[I t | ℱ t] ω := by
    intro t
    filter_upwards [gatedIndicator_law init hc ell (u + t)] with ω hlaw
    intro ht
    have hw := highWindow_of_lt_stop init C ell s u t ω ht t le_rfl
    have hg := shapeSafeAt_guard init C ell 0 s (u + t) (by omega) hell ω hw.1
    have hcount : clockCount (virtualLabels init ω (u + t)) = C.card := by
      change (clockSet (virtualLabels init ω (u + t))).card = C.card
      rw [← hg.2.1]
    change p ≤ (law init)[gatedIndicator init ell (u + t) |
      pairLogFiltration _ _ (u + t)] ω
    rw [hlaw]
    exact high_passage_raw_floor init hc C (by omega) ell hell _ hcount hw.2.1 hw.2.2
  have ht := prefix_success_hitting_tail hI hz
    (highStop_isStoppingTime init C ell s u hsu) hp hcond E
    (by simpa only [ℱ, shiftedFiltration_apply, Nat.add_zero] using hE)
    (highRawHorizon init C) k
    (fun ω _ hsur => high_survival_count init C ell s u _ hell htop hsu ω hsur)
  have hk : 0 ≤ k := by
    dsimp only [k]
    exact sub_nonneg.mpr (by exact_mod_cast bulkThreshold_le_highThreshold C.card)
  have hprod := mul_le_mul_of_nonneg_right log_two_bounds.2 hk
  have hgap := highThreshold_sub_bulkThreshold_bound C.card
  have hN := (highRawHorizon_bounds init hc C (by omega)).1
  have hCR : (100 : ℝ) ≤ C.card := by exact_mod_cast hC
  have hexp : k * Real.log 2 - p * (highRawHorizon init C : ℝ) / 2 ≤
      -(C.card : ℝ) / 50 := by
    dsimp only [p, k] at *
    nlinarith only [hprod, hgap, hN, hCR]
  exact measure_le_of_real_weighted_bound (law init) _ E _ (Real.exp_nonneg _)
    (ht.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp)
      ENNReal.toReal_nonneg))

theorem log_eight_sevenths_lower : (13 / 98 : ℝ) ≤ Real.log (8 / 7 : ℝ) := by
  have h := Real.le_log_one_add_of_nonneg
    (x := (1 / 7 : ℝ)) (by norm_num)
  norm_num at h
  linarith

theorem high_horizon_contact_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 100 ≤ C.card) (u : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ u] E) :
    law init (E ∩ {ω | 8 * (C.card : ℝ) ≤
      maskTickCount init C u (highRawHorizon init C) ω}) ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 20)) * law init E := by
  have hθ : 0 ≤ Real.log (8 / 7 : ℝ) := by
    linarith [log_eight_sevenths_lower]
  have hsub :
      E ∩ {ω | 8 * (C.card : ℝ) ≤ maskTickCount init C u (highRawHorizon init C) ω} ⊆
      E ∩ {ω | Real.log (8 / 7 : ℝ) * (8 * (C.card : ℝ)) ≤
        Real.log (8 / 7 : ℝ) * maskTickCount init C u (highRawHorizon init C) ω} := by
    rintro ω ⟨hω, hrω⟩
    exact ⟨hω, mul_le_mul_of_nonneg_left hrω hθ⟩
  have ht := prefix_maskTick_exponential_tail init hc C u
    (highRawHorizon init C) E hE (Real.log (8 / 7 : ℝ)) (8 * (C.card : ℝ))
  have hlog := mul_le_mul_of_nonneg_right log_eight_sevenths_lower
    (show (0 : ℝ) ≤ 8 * (C.card : ℝ) by positivity)
  have hmean := (highRawHorizon_bounds init hc C (by omega)).2
  have hCR : (100 : ℝ) ≤ C.card := by exact_mod_cast hC
  have hexp :
      (Real.exp (Real.log (8 / 7 : ℝ)) - 1) *
        clockMaskRate init.card C.card * (highRawHorizon init C : ℝ) -
        Real.log (8 / 7 : ℝ) * (8 * (C.card : ℝ)) ≤ -(C.card : ℝ) / 20 := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 8 / 7)]
    nlinarith only [hlog, hmean, hCR]
  exact measure_le_of_real_weighted_bound (law init) _ E _ (Real.exp_nonneg _)
    ((measureReal_mono hsub).trans (ht.trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) ENNReal.toReal_nonneg)))

theorem high_endpoint_survival (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u N : ℕ)
    (hell : 1 ≤ ell) (htop : ell ≤ clockCap n) (hsu : s ≤ u)
    (ω : InputLog n) (hsafe : shapeSafeAt init C s (u + N) ω)
    (hstart : StageEventSpec.bulkThreshold C.card ≤
      frontCount (virtualLabels init ω u) ell)
    (hbelow : frontCount (virtualLabels init ω (u + N)) ell <
      StageEventSpec.highThreshold C.card) :
    (N : WithTop ℕ) < highStop init C ell s u ω := by
  apply lt_of_not_ge
  intro hs
  obtain ⟨t, ht, hbad⟩ := (highStop_le_iff init C ell s u N ω).mp hs
  have hsafet := shapeSafeAt_anti init C s (u + t) (u + N) (by omega) ω hsafe
  apply hbad
  refine ⟨hsafet, ?_, ?_⟩
  · exact hstart.trans
      (frontCount_mono_safe init C s u (u + t) ell
        hsu (by omega) hell htop ω hsafet)
  · exact (frontCount_mono_safe init C s (u + t) (u + N) ell
      (by omega) (by omega) hell htop ω hsafe).trans_lt hbelow

def highClockFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) : Set (InputLog n) :=
  ⋃ N : ℕ, {ω | shapeSafeAt init C s (u + N) ω ∧
    frontCount (virtualLabels init ω (u + N)) ell < StageEventSpec.highThreshold C.card ∧
    8 * (C.card : ℝ) ≤ maskTickCount init C u N ω}

theorem high_clock_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 100 ≤ C.card)
    (ell s u : ℕ) (hell : 1 ≤ ell) (htop : ell ≤ clockCap n) (hsu : s ≤ u)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hstart : ∀ ω ∈ E, StageEventSpec.bulkThreshold C.card ≤
      frontCount (virtualLabels init ω u) ell) :
    law init (E ∩ highClockFailure init C ell s u) ≤
      (2 * ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 100))) * law init E := by
  let H := highRawHorizon init C
  let A : Set (InputLog n) :=
    E ∩ {ω | (H : WithTop ℕ) < highStop init C ell s u ω}
  let B : Set (InputLog n) :=
    E ∩ {ω | 8 * (C.card : ℝ) ≤ maskTickCount init C u H ω}
  have hcover : E ∩ highClockFailure init C ell s u ⊆ A ∪ B := by
    rintro ω ⟨he, hb⟩
    obtain ⟨N, hsafe, hbelow, htick⟩ := Set.mem_iUnion.mp hb
    by_cases hHN : H ≤ N
    · left
      exact ⟨he, (show (H : WithTop ℕ) ≤ (N : WithTop ℕ) by exact_mod_cast hHN).trans_lt
        (high_endpoint_survival init C ell s u N hell htop hsu ω hsafe
          (hstart ω he) hbelow)⟩
    · exact Or.inr ⟨he, htick.trans (maskTickCount_mono init C u N H (by omega) ω)⟩
  have ha := high_raw_prefix_tail init hc C hC ell s u hell htop hsu E hE
  have hb := high_horizon_contact_tail init hc C hC u E hE
  have ha' : law init A ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 100)) * law init E :=
    ha.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (by
        have : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
        linarith))) _)
  have hb' : law init B ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 100)) * law init E :=
    hb.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (by
        have : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
        linarith))) _)
  calc
    law init (E ∩ highClockFailure init C ell s u) ≤ law init (A ∪ B) :=
      measure_mono hcover
    _ ≤ law init A + law init B := measure_union_le _ _
    _ ≤ _ := add_le_add ha' hb'
    _ = _ := by ring

theorem high_first_hit_contacts_le (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u tau : ℕ) (ω : InputLog n)
    (hsafe : shapeSafeAt init C s tau ω)
    (hfirst : StageEventSpec.firstAfter
      (fun v => StageEventSpec.highThreshold C.card ≤
        frontCount (virtualLabels init ω v) ell) s tau)
    (hsu : s ≤ u) (hgood : ω ∉ highClockFailure init C ell s u) :
    maskContacts init C u tau ω ≤ 8 * C.card := by
  by_cases hut : u ≤ tau
  · apply contacts_le_budget_of_predecessors init C u tau (8 * C.card) hut ω
    intro N hN
    apply lt_of_not_ge
    intro htick
    apply hgood
    exact Set.mem_iUnion.mpr ⟨N,
      shapeSafeAt_anti init C s (u + N) tau hN.le ω hsafe,
      lt_of_not_ge (hfirst.2.2 (u + N) (by omega) hN),
      by simpa only [Nat.cast_mul, Nat.cast_ofNat] using htick⟩
  · classical
    have hz : maskContacts init C u tau ω = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have htu := Finset.mem_Ioc.mp (Finset.mem_filter.mp ht).1
      omega
    rw [hz]
    exact Nat.zero_le _

/-- At the full budget an observed safe endpoint has already reached high.
This strict pre-hit exclusion is needed when twenty P7 gaps sum to exactly 8C. -/
theorem high_front_of_contact_budget (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u v : ℕ) (ω : InputLog n)
    (huv : u ≤ v) (hsafe : shapeSafeAt init C s v ω)
    (hbudget : 8 * (C.card : ℝ) ≤ (maskContacts init C u v ω : ℝ))
    (hgood : ω ∉ highClockFailure init C ell s u) :
    StageEventSpec.highThreshold C.card ≤ frontCount (virtualLabels init ω v) ell := by
  by_contra hnot
  apply hgood
  refine Set.mem_iUnion.mpr ⟨v - u, ?_, ?_, ?_⟩
  · simpa only [Nat.add_sub_of_le huv] using hsafe
  · simpa only [Nat.add_sub_of_le huv] using (show
      frontCount (virtualLabels init ω v) ell < StageEventSpec.highThreshold C.card by omega)
  · rw [maskTickCount_eq_contacts, Nat.add_sub_of_le huv]
    exact hbudget

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHighPassage

end

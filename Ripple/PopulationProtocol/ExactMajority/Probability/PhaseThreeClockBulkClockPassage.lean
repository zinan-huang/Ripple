-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockBulkClockPassage.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockShapeBarrier
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinning

/-!
# Positive-level bulk passages in physical Clock contacts

The full raising-pair polynomial has a uniform 1/125 Clock-contact floor
throughout a previous-bulk/current-below-bulk window. A deterministic raw
horizon and the exact fixed-mask contact law give P3's 100C-contact tail.
The comparison uses observed prefixes and retains their probability.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBulkClockPassage

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeScalar
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockProbabilityFloors PhaseThreeClockPrefixTails
  PhaseThreeClockStoppedPassage PhaseThreeClockObservedPassage
  PhaseThreeClockShapeFreeze PhaseThreeClockShapeBarrier PhaseThreeClockThinning

variable {n : ℕ}

theorem bulk_pair_polynomial (C b x y : ℝ)
    (hC : 100 ≤ C) (hb : C ≤ 10 * b) (hb' : 10 * b ≤ C + 10)
    (hx : b ≤ x) (hy : 0 ≤ y) (hyb : y + 1 ≤ b) :
    C * (C - 1) ≤
      125 * (2 * y * (C - y) + (x - y) * (x - y - 1)) := by
  have hbase := mul_nonneg (sub_nonneg.mpr hb)
    (show 0 ≤ 10 * b + C - 10 by linarith)
  have hlarge := mul_nonneg (show 0 ≤ C by linarith)
    (show 0 ≤ C - 46 by linarith)
  have hmove := mul_nonneg (sub_nonneg.mpr hx)
    (show 0 ≤ x + b - 2 * y - 1 by linarith)
  have hyterm := mul_nonneg hy
    (show 0 ≤ 2 * C - 2 * b + 1 - y by linarith)
  nlinarith only [hbase, hlarge, hmove, hyterm]

theorem bulk_gated_pair_floor {L m : ℕ}
    (f : Fin m → AgentState L 256) (ell C : ℕ)
    (hell : 2 ≤ ell) (hC : 100 ≤ C) (hcount : clockCount f = C)
    (hprev : StageEventSpec.bulkThreshold C ≤ frontCount f (ell - 1))
    (hbelow : frontCount f ell < StageEventSpec.bulkThreshold C) :
    (C : ℝ) * ((C : ℝ) - 1) ≤
      125 * ((goodPairs (GatedTick ell) f).card : ℝ) := by
  have hsplit := frontCount_pred f ell (by omega)
  have hepos : 1 ≤ exactCount f (ell - 1) := by omega
  have hyC : frontCount f ell ≤ C := by
    simpa only [hcount] using frontCount_le_clockCount f ell
  have hpair := goodPairs_raisingTick_card f ell
  rw [← goodPairs_gatedTick_eq_of_two_le f ell hell, hcount] at hpair
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
  have hb : (C : ℝ) ≤ 10 * (StageEventSpec.bulkThreshold C : ℝ) := by
    have h := Nat.le_ceil ((C : ℝ) / 10)
    change (C : ℝ) ≤ 10 * (Nat.ceil ((C : ℝ) / 10) : ℝ)
    linarith
  have hb' : 10 * (StageEventSpec.bulkThreshold C : ℝ) ≤ (C : ℝ) + 10 := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ (C : ℝ) / 10)
    change 10 * (Nat.ceil ((C : ℝ) / 10) : ℝ) ≤ (C : ℝ) + 10
    linarith
  have hp := bulk_pair_polynomial (C : ℝ) (StageEventSpec.bulkThreshold C : ℝ)
    (frontCount f (ell - 1) : ℝ) (frontCount f ell : ℝ)
    (by exact_mod_cast hC) hb hb' (by exact_mod_cast hprev) (by positivity)
    (by exact_mod_cast (show frontCount f ell + 1 ≤ StageEventSpec.bulkThreshold C by omega))
  rw [hpairR]
  nlinarith only [hp, hsplitR]

theorem mask_rate_bounds (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 2 ≤ C.card) :
    0 < clockMaskRate init.card C.card ∧ clockMaskRate init.card C.card ≤ 1 := by
  have hcR : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
  have hCR : (2 : ℝ) ≤ C.card := by exact_mod_cast hC
  have hCm : C.card ≤ init.card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ C)
  have hCmR : (C.card : ℝ) ≤ init.card := by exact_mod_cast hCm
  have hden : 0 < (init.card : ℝ) * ((init.card : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  rw [clockMaskRate_eq_real _ _ (by omega)]
  refine ⟨div_pos (mul_pos (by linarith) (by linarith)) hden, ?_⟩
  apply (div_le_one hden).2
  exact mul_le_mul hCmR (sub_le_sub_right hCmR 1) (by linarith) (by linarith)

theorem bulk_raw_rate_floor (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 100 ≤ C.card)
    (f : Fin init.card → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256)
    (ell : ℕ) (hell : 2 ≤ ell) (hcount : clockCount f = C.card)
    (hprev : StageEventSpec.bulkThreshold C.card ≤ frontCount f (ell - 1))
    (hbelow : frontCount f ell < StageEventSpec.bulkThreshold C.card) :
    clockMaskRate init.card C.card / 125 ≤
      ((goodPairs (GatedTick ell) f).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
  have hpair := bulk_gated_pair_floor f ell C.card hell hC hcount hprev hbelow
  have hcR : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
  have hden : 0 ≤ (init.card : ℝ) * ((init.card : ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hp : (C.card : ℝ) * ((C.card : ℝ) - 1) / 125 ≤
      ((goodPairs (GatedTick ell) f).card : ℝ) := by linarith
  have h := div_le_div_of_nonneg_right hp hden
  rw [clockMaskRate_eq_real _ _ (by omega)]
  convert h using 1 <;> ring

def bulkWindow (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u t : ℕ) (ω : InputLog n) : Prop :=
  shapeSafeAt init C s (u + t) ω ∧
    StageEventSpec.bulkThreshold C.card ≤
      frontCount (virtualLabels init ω (u + t)) (ell - 1) ∧
    frontCount (virtualLabels init ω (u + t)) ell < StageEventSpec.bulkThreshold C.card

open Classical in
def bulkStop (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (ω : InputLog n) : WithTop ℕ :=
  if h : ∃ t, ¬ bulkWindow init C ell s u t ω
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem bulkStop_le_iff (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u N : ℕ) (ω : InputLog n) :
    bulkStop init C ell s u ω ≤ (N : WithTop ℕ) ↔
      ∃ t ≤ N, ¬ bulkWindow init C ell s u t ω := by
  classical
  unfold bulkStop
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

theorem bulkWindow_of_lt_stop (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u N : ℕ) (ω : InputLog n)
    (hN : (N : WithTop ℕ) < bulkStop init C ell s u ω) :
    ∀ t ≤ N, bulkWindow init C ell s u t ω := by
  intro t ht
  by_contra hbad
  exact (not_lt_of_ge ((bulkStop_le_iff init C ell s u N ω).2 ⟨t, ht, hbad⟩)) hN

theorem bulkWindow_measurable (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (hsu : s ≤ u) (t : ℕ) :
    MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u t]
      {ω | bulkWindow init C ell s u t ω} := by
  have hp : MeasurableSet[pairLogFiltration _ _ (u + t)]
      {ω | StageEventSpec.bulkThreshold C.card ≤
          frontCount (virtualLabels init ω (u + t)) (ell - 1) ∧
        frontCount (virtualLabels init ω (u + t)) ell < StageEventSpec.bulkThreshold C.card} :=
    (show MeasurableSet {f : Fin init.card →
      AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 |
        StageEventSpec.bulkThreshold C.card ≤ frontCount f (ell - 1) ∧
          frontCount f ell < StageEventSpec.bulkThreshold C.card} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init (u + t))
  exact (shapeSafeAt_measurable init C s (u + t) (by omega)).inter hp

theorem bulkStop_isStoppingTime (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) (hsu : s ≤ u) :
    IsStoppingTime (shiftedFiltration (pairLogFiltration _ _) u)
      (bulkStop init C ell s u) := by
  intro N
  have hm : MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u N]
      (⋃ t : ℕ, {ω | t ≤ N ∧ ¬ bulkWindow init C ell s u t ω}) := by
    refine MeasurableSet.iUnion fun t => ?_
    by_cases ht : t ≤ N
    · have hbad := ((shiftedFiltration (pairLogFiltration _ _) u).mono ht) _
        (bulkWindow_measurable init C ell s u hsu t).compl
      simpa only [ht, true_and] using hbad
    · simp only [ht, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact bulkStop_le_iff init C ell s u N ω

theorem bulk_survival_count (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u N : ℕ) (hsu : s ≤ u) (hell : 2 ≤ ell)
    (hcap : ell ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (ω : InputLog n) (hN : (N : WithTop ℕ) < bulkStop init C ell s u ω) :
    bernoulliCount (fun t => gatedIndicator init ell (u + t)) N ω <
      (StageEventSpec.bulkThreshold C.card : ℝ) := by
  have hw := bulkWindow_of_lt_stop init C ell s u N ω hN
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
        have hs := front_step_safe init C ell 0 s (u + r) (by omega) (by omega) hcap ω
          (by simpa only [Nat.add_assoc] using (hw (r + 1) hr).1)
        simpa only [Nat.add_assoc, bernoulliCount, Finset.sum_range_succ, add_assoc] using
          hs.trans (congrArg (fun z : ℝ => z + gatedIndicator init ell (u + r) ω) hp)
  have hbelow : (frontCount (virtualLabels init ω (u + N)) ell : ℝ) <
      (StageEventSpec.bulkThreshold C.card : ℝ) := by exact_mod_cast (hw N le_rfl).2.2
  have hz : 0 ≤ (frontCount (virtualLabels init ω u) ell : ℝ) := by positivity
  linarith [htel N le_rfl]

def bulkRawHorizon (init : InputCfg n) (C : Finset (Fin init.card)) : ℕ :=
  Nat.ceil (50 * (C.card : ℝ) / clockMaskRate init.card C.card)

theorem bulkRawHorizon_bounds (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 100 ≤ C.card) :
    50 * (C.card : ℝ) ≤ clockMaskRate init.card C.card * (bulkRawHorizon init C : ℝ) ∧
    clockMaskRate init.card C.card * (bulkRawHorizon init C : ℝ) ≤ 75 * (C.card : ℝ) := by
  have hq := mask_rate_bounds init hc C (by omega)
  have hCR : (100 : ℝ) ≤ C.card := by exact_mod_cast hC
  have hlow := Nat.le_ceil (50 * (C.card : ℝ) / clockMaskRate init.card C.card)
  have hupp := Nat.ceil_lt_add_one
    (show 0 ≤ 50 * (C.card : ℝ) / clockMaskRate init.card C.card from
      div_nonneg (by positivity) hq.1.le)
  have he : clockMaskRate init.card C.card *
      (50 * (C.card : ℝ) / clockMaskRate init.card C.card) = 50 * (C.card : ℝ) := by
    field_simp [ne_of_gt hq.1] <;> ring
  have hl := mul_le_mul_of_nonneg_left hlow hq.1.le
  have hu := mul_le_mul_of_nonneg_left hupp.le hq.1.le
  dsimp only [bulkRawHorizon]
  rw [he] at hl
  rw [mul_add, he, mul_one] at hu
  exact ⟨hl, by linarith⟩

theorem bulk_raw_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 100 ≤ C.card)
    (ell s u : ℕ) (hsu : s ≤ u) (hell : 2 ≤ ell)
    (hcap : ell ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ u] E) :
    law init (E ∩ {ω |
      (bulkRawHorizon init C : WithTop ℕ) < bulkStop init C ell s u ω}) ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 10)) * law init E := by
  let ℱ := shiftedFiltration (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256) u
  let I : ℕ → InputLog n → ℝ := fun t => gatedIndicator init ell (u + t)
  let p : ℝ := clockMaskRate init.card C.card / 125
  have hq := mask_rate_bounds init hc C (by omega)
  have hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t) := by
    intro t
    simpa only [ℱ, I, shiftedFiltration_apply, Nat.add_assoc] using
      gatedIndicator_adapted init ell (u + t)
  have hz : ∀ t, ∀ᵐ ω ∂law init, I t ω = 0 ∨ I t ω = 1 :=
    fun t => ae_of_all _ (gatedIndicator_zero_one init ell (u + t))
  have hp : p ≤ 1 := by dsimp only [p]; linarith [hq.2]
  have hcond : ∀ t : ℕ, ∀ᵐ ω ∂law init,
      (t : WithTop ℕ) < bulkStop init C ell s u ω →
        p ≤ (law init)[I t | ℱ t] ω := by
    intro t
    filter_upwards [gatedIndicator_law init hc ell (u + t)] with ω hlaw
    intro ht
    have hw := bulkWindow_of_lt_stop init C ell s u t ω ht t le_rfl
    have hg := shapeSafeAt_guard init C ell 0 s (u + t) (by omega) (by omega) ω hw.1
    have hcount : clockCount (virtualLabels init ω (u + t)) = C.card := by
      change (clockSet (virtualLabels init ω (u + t))).card = C.card
      rw [← hg.2.1]
    change p ≤ (law init)[gatedIndicator init ell (u + t) | pairLogFiltration _ _ (u + t)] ω
    rw [hlaw]
    exact bulk_raw_rate_floor init hc C hC _ ell hell hcount hw.2.1 hw.2.2
  have ht := prefix_success_hitting_tail hI hz (bulkStop_isStoppingTime init C ell s u hsu)
    hp hcond E (by simpa only [ℱ, shiftedFiltration_apply, Nat.add_zero] using hE)
    (bulkRawHorizon init C) (StageEventSpec.bulkThreshold C.card : ℝ)
    (fun ω _ hsur => bulk_survival_count init C ell s u _ hsu hell hcap ω hsur)
  have hCR : (100 : ℝ) ≤ C.card := by exact_mod_cast hC
  have hb : (StageEventSpec.bulkThreshold C.card : ℝ) ≤ (C.card : ℝ) / 10 + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (C.card : ℝ) / 10)).le
  have hl : Real.log 2 ≤ (3 / 4 : ℝ) :=
    PhaseThreeModel.Numeric.log_two_bounds.2.trans (by norm_num)
  have hprod := mul_le_mul_of_nonneg_left hl
    (show (0 : ℝ) ≤ StageEventSpec.bulkThreshold C.card by positivity)
  have hN := (bulkRawHorizon_bounds init hc C hC).1
  have hexp : (StageEventSpec.bulkThreshold C.card : ℝ) * Real.log 2 -
      p * (bulkRawHorizon init C : ℝ) / 2 ≤ -(C.card : ℝ) / 10 := by
    dsimp only [p]
    nlinarith only [hprod, hb, hN, hCR]
  exact measure_le_of_real_weighted_bound (law init) _ E _
    (Real.exp_nonneg _) (ht.trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)))

theorem bulk_endpoint_implies_survival (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u N : ℕ)
    (hsu : s ≤ u) (hell : 2 ≤ ell)
    (hcap : ell ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (ω : InputLog n) (hsafe : shapeSafeAt init C s (u + N) ω)
    (hprev : StageEventSpec.bulkThreshold C.card ≤
      frontCount (virtualLabels init ω u) (ell - 1))
    (hbelow : frontCount (virtualLabels init ω (u + N)) ell <
      StageEventSpec.bulkThreshold C.card) :
    (N : WithTop ℕ) < bulkStop init C ell s u ω := by
  have hspan : EnvironmentSpan init u N ω := by
    intro t ht
    exact (shapeSafeAt_guard init C ell 0 s (u + t) (by omega) (by omega) ω
      (shapeSafeAt_anti init C s (u + t) (u + N) (by omega) ω hsafe)).1
  apply lt_of_not_ge
  intro hs
  obtain ⟨t, ht, hbad⟩ := (bulkStop_le_iff init C ell s u N ω).mp hs
  apply hbad
  refine ⟨shapeSafeAt_anti init C s (u + t) (u + N) (by omega) ω hsafe, ?_, ?_⟩
  · apply hprev.trans
    simpa only [Nat.add_zero] using frontCount_mono_of_environmentSpan init ω u N
      (ell - 1) (by omega) (by omega) hspan 0 t (Nat.zero_le t) ht
  · exact (frontCount_mono_of_environmentSpan init ω u N ell (by omega) hcap
      hspan t N ht le_rfl).trans_lt hbelow

theorem maskTickCount_mono (init : InputCfg n) (C : Finset (Fin init.card))
    (u N M : ℕ) (hNM : N ≤ M) (ω : InputLog n) :
    maskTickCount init C u N ω ≤ maskTickCount init C u M ω := by
  rw [maskTickCount_eq_contacts, maskTickCount_eq_contacts]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro k hk
  simp only [maskContacts, Finset.mem_filter, Finset.mem_Ioc] at hk ⊢
  exact ⟨⟨hk.1.1, by omega⟩, hk.2⟩

theorem contacts_le_budget_of_predecessors (init : InputCfg n)
    (C : Finset (Fin init.card)) (u T budget : ℕ) (huT : u ≤ T) (ω : InputLog n)
    (hbefore : ∀ N, u + N < T → maskTickCount init C u N ω < (budget : ℝ)) :
    maskContacts init C u T ω ≤ budget := by
  by_cases he : u = T
  · subst T
    simp [maskContacts]
  · let N := T - u - 1
    have hT : T = u + (N + 1) := by dsimp only [N]; omega
    have hpre := hbefore N (by omega)
    have hstep := maskTickCount_succ init C u N ω
    have hJ : maskTickIndicator init C (u + N) ω ≤ 1 := by
      rcases maskTickIndicator_zero_one init C (u + N) ω with h | h <;> simp only [h] <;> norm_num
    have hbound : maskTickCount init C u (N + 1) ω < (budget : ℝ) + 1 := by linarith
    rw [maskTickCount_eq_contacts, ← hT] at hbound
    have hcast : (maskContacts init C u T ω : ℝ) < ((budget + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hbound
    have hnat : maskContacts init C u T ω < budget + 1 := by exact_mod_cast hcast
    omega

theorem prefix_clock_contact_passage_comparison
    (init : InputCfg n) (C : Finset (Fin init.card)) (u H : ℕ)
    (E : Set (InputLog n)) (D : ℕ → Set (InputLog n))
    (tau : InputLog n → WithTop ℕ) (r : ℝ)
    (hsurvive : ∀ N ω, ω ∈ E → ω ∈ D N → (N : WithTop ℕ) < tau ω) :
    law init (E ∩ ⋃ N : ℕ, D N ∩ {ω | r ≤ maskTickCount init C u N ω}) ≤
      law init (E ∩ {ω | (H : WithTop ℕ) < tau ω}) +
        law init (E ∩ {ω | r ≤ maskTickCount init C u H ω}) := by
  have hsub : (E ∩ ⋃ N : ℕ, D N ∩ {ω | r ≤ maskTickCount init C u N ω}) ⊆
      (E ∩ {ω | (H : WithTop ℕ) < tau ω}) ∪
        (E ∩ {ω | r ≤ maskTickCount init C u H ω}) := by
    rintro ω ⟨he, hbad⟩
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hbad
    by_cases hHN : H ≤ N
    · left
      exact ⟨he, (show (H : WithTop ℕ) ≤ (N : WithTop ℕ) by exact_mod_cast hHN).trans_lt
        (hsurvive N ω he hN.1)⟩
    · right
      exact ⟨he, hN.2.trans (maskTickCount_mono init C u N H (by omega) ω)⟩
  exact (measure_mono hsub).trans (measure_union_le _ _)

def bulkClockFailureAt (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u N : ℕ) : Set (InputLog n) :=
  {ω | shapeSafeAt init C s (u + N) ω ∧
    frontCount (virtualLabels init ω (u + N)) ell < StageEventSpec.bulkThreshold C.card ∧
    100 * (C.card : ℝ) ≤ maskTickCount init C u N ω}

def bulkClockFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ell s u : ℕ) : Set (InputLog n) :=
  ⋃ N : ℕ, bulkClockFailureAt init C ell s u N

theorem bulkClockFailureAt_measurable (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u N : ℕ) (hsu : s ≤ u) :
    MeasurableSet[pairLogFiltration _ _ (u + N)] (bulkClockFailureAt init C ell s u N) := by
  have hf : MeasurableSet[pairLogFiltration _ _ (u + N)]
      {ω | frontCount (virtualLabels init ω (u + N)) ell <
        StageEventSpec.bulkThreshold C.card} :=
    (show MeasurableSet {f : Fin init.card →
      AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 |
        frontCount f ell < StageEventSpec.bulkThreshold C.card} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init (u + N))
  have hJ : ∀ t, StronglyMeasurable[shiftedFiltration (pairLogFiltration _ _) u (t + 1)]
      (maskTickIndicator init C (u + t)) := by
    intro t
    simpa only [shiftedFiltration_apply, Nat.add_assoc] using
      maskTickIndicator_stronglyMeasurable init C (u + t)
  have hc := (bernoulliCount_stronglyMeasurable hJ N).measurable
  exact (shapeSafeAt_measurable init C s (u + N) (by omega)).inter
    (hf.inter (measurableSet_le measurable_const hc))

theorem bulkClockFailure_measurable (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u : ℕ) (hsu : s ≤ u) :
    MeasurableSet (bulkClockFailure init C ell s u) :=
  MeasurableSet.iUnion (fun N => ((pairLogFiltration _ _).le (u + N)) _
    (bulkClockFailureAt_measurable init C ell s u N hsu))

theorem bulkClockFailureAt_iff_stageContacts (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u N : ℕ) (ω : InputLog n) :
    ω ∈ bulkClockFailureAt init C ell s u N ↔
      shapeSafeAt init C s (u + N) ω ∧
        frontCount (virtualLabels init ω (u + N)) ell < StageEventSpec.bulkThreshold C.card ∧
        100 * C.card ≤ StageEventSpec.clockContacts init ω s u (u + N) := by
  have hcontacts (hsafe : shapeSafeAt init C s (u + N) ω) :
      maskContacts init C u (u + N) ω = StageEventSpec.clockContacts init ω s u (u + N) := by
    rw [← hsafe.1.2]
    exact maskContacts_seed_eq_stageEvent init ω s u (u + N)
  constructor
  · rintro ⟨hsafe, hbelow, htick⟩
    refine ⟨hsafe, hbelow, ?_⟩
    rw [maskTickCount_eq_contacts, hcontacts hsafe] at htick
    exact_mod_cast htick
  · rintro ⟨hsafe, hbelow, htick⟩
    refine ⟨hsafe, hbelow, ?_⟩
    change 100 * (C.card : ℝ) ≤ maskTickCount init C u N ω
    rw [maskTickCount_eq_contacts, hcontacts hsafe]
    exact_mod_cast htick

theorem bulk_next_bulk_clock_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 100 ≤ C.card)
    (ell s u : ℕ) (hsu : s ≤ u) (hell : 2 ≤ ell)
    (hcap : ell ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hprev : ∀ ω ∈ E, StageEventSpec.bulkThreshold C.card ≤
      frontCount (virtualLabels init ω u) (ell - 1)) :
    law init (E ∩ bulkClockFailure init C ell s u) ≤
      (2 * ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 1000))) * law init E := by
  let H := bulkRawHorizon init C
  let A : Set (InputLog n) := E ∩ {ω | (H : WithTop ℕ) < bulkStop init C ell s u ω}
  let B : Set (InputLog n) := E ∩ {ω | 100 * (C.card : ℝ) ≤ maskTickCount init C u H ω}
  have hsub : E ∩ bulkClockFailure init C ell s u ⊆ A ∪ B := by
    rintro ω ⟨he, hbad⟩
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hbad
    by_cases hHN : H ≤ N
    · left
      refine ⟨he, ?_⟩
      exact (show (H : WithTop ℕ) ≤ (N : WithTop ℕ) by exact_mod_cast hHN).trans_lt
        (bulk_endpoint_implies_survival init C ell s u N hsu hell hcap ω
          hN.1 (hprev ω he) hN.2.1)
    · right
      exact ⟨he, hN.2.2.trans
        (maskTickCount_mono init C u N H (by omega) ω)⟩
  have ha := bulk_raw_prefix_tail init hc C hC ell s u hsu hell hcap E hE
  have hb := prefix_maskTick_upper_tail init hc C u H E hE
    (100 * (C.card : ℝ)) (by positivity)
    (by have hm := (bulkRawHorizon_bounds init hc C hC).2
        dsimp only [H]
        linarith)
  have hB : law init B ≤
      ENNReal.ofReal (Real.exp (-(100 * (C.card : ℝ)) / 36)) * law init E :=
    measure_le_of_real_weighted_bound (law init) B E _
      (Real.exp_nonneg _) hb
  have ha' : law init A ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 1000)) * law init E :=
    ha.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (by
        have hzero : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
        linarith))) _)
  have hb' : law init B ≤
      ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 1000)) * law init E :=
    hB.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (by
        have hzero : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
        linarith))) _)
  calc
    law init (E ∩ bulkClockFailure init C ell s u) ≤ law init (A ∪ B) := measure_mono hsub
    _ ≤ law init A + law init B := measure_union_le A B
    _ ≤ _ := add_le_add ha' hb'
    _ = (2 * ENNReal.ofReal (Real.exp (-(C.card : ℝ) / 1000))) * law init E := by ring

theorem bulk_first_hit_contacts_le (init : InputCfg n)
    (C : Finset (Fin init.card)) (ell s u T : ℕ) (huT : u ≤ T) (ω : InputLog n)
    (hsafe : shapeSafeAt init C s T ω)
    (hfirst : ∀ v, u ≤ v → v < T →
      frontCount (virtualLabels init ω v) ell < StageEventSpec.bulkThreshold C.card)
    (hgood : ω ∉ bulkClockFailure init C ell s u) :
    StageEventSpec.clockContacts init ω s u T ≤ 100 * C.card := by
  have hmask := maskContacts_seed_eq_stageEvent init ω s u T
  rw [hsafe.1.2] at hmask
  rw [← hmask]
  apply contacts_le_budget_of_predecessors init C u T (100 * C.card) huT ω
  intro N hN
  apply lt_of_not_ge
  intro htick
  apply hgood
  apply Set.mem_iUnion.mpr
  refine ⟨N, shapeSafeAt_anti init C s (u + N) T hN.le ω hsafe,
    hfirst (u + N) (Nat.le_add_right _ _) hN, ?_⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using htick

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBulkClockPassage

end
